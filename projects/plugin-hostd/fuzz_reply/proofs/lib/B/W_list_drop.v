(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: the ASan+UBSan walk (image B, fuzz_reply.asan-ubsan) of fuzz_reply's list_drop,
   a NEW walk over lib/B/W_listing.v (B's body is not A's up to relocation: VERDICT.md (sha256 810ca1df9ca9; internal record),
   MEASURE-W1.md (sha256 bc8377b9603f; internal record)), after lib/A/W_list_drop.v and lib/A/W_list_drop_top.v (commit f83b4c2732c), in the
   form of the cgif walks of proofs/cgif/cgif_file_fuzzer/lib/A/AC8h.v (free sites) and lib/A/ACbk.v (entry and
   return). *)
(* list_drop(l, i) at 0x85b50 (image B; 0x85814 in A; frame 64, ra and s0..s5 at 56..8) frees the text of record i
   (the allocator's free, through the GUIDE's allocator parameter: the Section hypothesis AFREE, W_journal_x.v
   afree_cf_rule_c_x at the caller-context table CTX), moves the records after it down by one with the __asan_memmove
   intrinsic (AMOVE, W_sites_x.v amemmove_realizes_x), and stores n - 1.  The walk is ARx-generic (route (b), step 3;
   the template is lib/A/W_list_drop.v + lib/A/W_list_drop_top.v at commit be8158006bd): any
   allocator relation ARx with its laws LAWS and HP0, the placement parameter PST, the journal
   W_journal_x.ajournal_gx_x; Sections dARc / eARc / dAR / eAR below re-derive from it the caller-context AR forms
   pb_list_drop_c / pb_list_drop_at_c / pb_list_drop_ro_c (a Theorem Labs lane's statements) and the AR walks pb_list_drop,
   pb_list_drop_at and pb_list_drop_ro.  The representation step, from the list before to the list after, is the
   stand-alone lemma alist_at_drop (image-independent; lib/A's text).
   B's UBSan checks (trap mode: every check branches to `unimp` at 0x85cd4; 14 of them, TRAPS-CENSUS.md (sha256 b33c2b52103e; internal record)
   rows 14-27) are refuted from the contract's premises.  With the atom facts below (LA, v, &l->v[i] 8-aligned,
   i, n, cap < 2^30 (alist_at's hl_cap < 2^30), n >= 1 in the body) the runner decides nine of them itself; the five
   it stops at (MEASURED, vm_compute) are refuted by lib/B/W_traps.v's shape lemmas:
     0x85bc4  trap_ptr_sovf    &l->v[i] = v + 16 i does not overflow     (pb_list_drop_x)
     0x85c14  trap_ptr_sovf    the same check after the free             (ld_bodyX_x)
     0x85c40  trap_ptr_sovf    &l->v[i+1] = v + 16 (i+1)                 (ld_bodyX_x)
     0x85c70  trap_decw_sext   (n - i) - 1 fits int32                     (ld_bodyX_x)
     0x85c84  trap_align8_pair the memmove's operands are 8-aligned       (ld_bodyX_x)
   The ASan shadow checks (and their report blocks 0x85cd8..0x85d24) are decided by the runner from zero shadow. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YI08 YO0c.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YP0d YP0c YC80 YC81 YO0a YN1e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YM05 YI00 YC5d.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require HarnessRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib Require Mem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YN2e.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_syms W_listing W_pl W_kit W_journal W_rep W_contract W_sites W_frame W_traps.
(* The sink-instance guard (MERGE.md (sha256 0694aca87ccd; internal record) step 3): no sink instance is inferred; the walk's sink_head is the Section's SK *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YCbqG.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_kit_x W_journal_x W_contract_x W_sites_x.
(* route R: SRrG (Reusable YA0nH) and list_drop's R contract (W_contract_xR_g3.v), for the Section wR twins *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YA0nH.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_contract_xR_g3.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require YLX0.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.

Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section b.
Context {PI : PAImg fr_prog_listing}.
#[local] Notation SEGS := (@pa_segs _ fr_prog_listing PI).
#[local] Notation VAL := (@pa_val _ fr_prog_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ fr_prog_listing PI).
#[local] Notation BASE := (@pa_val _ fr_prog_listing PI A_TEXT).

(* ------------------------------------------------------------------ the list's cells as val_mem.
   WalkListFind's three bridge lemmas of lib/A/W_list_find.v, copied here under LDB because
   W_list_find.v was not compiling when this file needed them (W1Small, 2026-10-28 23:4xZ).  Same
   statements, same proofs; at integration one copy goes. *)
Lemma garr8_val_mem8 : forall (m : word -> option byte) a (w : word),
garr8 SEGS m a (HarnessRep.bzs (word_to_le_bytes 8 w)) -> val_mem SEGS m a 8 (bv_unsigned w).
Proof.
intros m a w H k Hk.
assert (Hl : length (HarnessRep.bzs (word_to_le_bytes 8 w)) = 8%nat)
by (unfold HarnessRep.bzs; rewrite length_map; apply length_N_to_le_bytes).
rewrite (garr8_mbyte SEGS m a _ k H ltac:(lia)). f_equal.
pose proof (YN2e.word_to_le_bytes_nth 8 (bv_unsigned w) k Hk (bv_unsigned_in_range 64 w)) as Hn.
rewrite Z_to_bv_bv_unsigned in Hn.
unfold HarnessRep.bzs.
replace (nth k (map HarnessRep.bz (word_to_le_bytes 8 w)) 0)
with (HarnessRep.bz (nth k (word_to_le_bytes 8 w) (Z_to_bv 8 0))).
2: { rewrite <- (map_nth HarnessRep.bz). apply nth_indep. rewrite length_map, length_N_to_le_bytes. exact Hk. }
rewrite (nth_error_nth _ _ _ Hn). unfold HarnessRep.bz. apply Z_to_bv_bv_unsigned.
Qed.
Lemma text_recs_length : forall rs, length (concat (map HarnessRep.text_rec rs)) = (16 * length rs)%nat.
Proof.
induction rs as [|r rs IH]; [reflexivity|]. cbn [map concat]. rewrite length_app, IH.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8.
rewrite length_app, !length_N_to_le_bytes. cbn [length]. lia.
Qed.
(* `writable_at` (YP09.v:136) is "the byte is present, or the address falls in a writable segment", so it
   survives a step that keeps presence and hides no more (W_frame.v:76 writable_kept, across two worlds). *)
Lemma writable_kept_w : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) -> wle W W' ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m' ) a.
Proof.
intros W W' m m' a Hp Hh Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- rewrite (Hh _ EH') in Hw. exact Hw.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma awr_kept_w : forall (W W' : world SEGS) m m' a nn,
(forall x, a <= x < a + nn -> apresent (w_H W) m x -> apresent (w_H W') m' x) -> wle W W' ->
awr W m a nn -> awr W' m' a nn.
Proof.
intros W W' m m' a nn Hp Hwle H j Hj.
apply (writable_kept_w W W' m m' (a + j)); [intros Hx; exact (Hp (a + j) ltac:(lia) Hx) | exact Hwle | exact (H j Hj)].
Qed.


(* a four-byte cell of a region, read back off the symbolic state after the program stored it *)
Lemma val_mem_of_chunk4 : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 4%N e)) -> U E e = v -> 0 <= v < 2 ^ 32 ->
val_mem SEGS m (base + off) 4 v.
Proof.
intros E m base off e v Hc Hv Hr k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb. injection Hb as <-. cbn [YP09.c_off] in Hm.
rewrite Hm. f_equal. unfold byte_of_word, YO0f.le_byte.
change (bv_unsigned (sv_denot E e)) with (U E e). rewrite Hv.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 4))) by (cbn; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
Lemma val_mem_of_chunk8 : forall E (m : word -> option byte) base off e v,
YP09.chunk_ok SEGS E m base (YP09.mkChunk off (CVal 8%N e)) -> U E e = v -> 0 <= v < 2 ^ 64 ->
val_mem SEGS m (base + off) 8 v.
Proof.
intros E m base off e v Hc Hv Hr k Hk.
destruct (Hc (Z.of_nat k) ltac:(cbn; lia)) as (b & Hb & Hm).
cbn [YP09.c_off YP09.c_val YP09.cbyte] in Hb. injection Hb as <-. cbn [YP09.c_off] in Hm.
rewrite Hm. f_equal. unfold byte_of_word, YO0f.le_byte.
change (bv_unsigned (sv_denot E e)) with (U E e). rewrite Hv.
rewrite (Z.mod_small v (2 ^ (8 * Z.of_nat 8))) by (cbn; lia).
apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 8) with 256.
rewrite Z.mod_mod by lia. reflexivity.
Qed.
(* two memories that hold the same n-byte value at a show the same bytes there *)
Lemma aview_of_val_mem2 : forall H H' (m m' : word -> option byte) a n v k,
val_mem SEGS (mrestrict H m) a n v -> val_mem SEGS (mrestrict H' m') a n v -> 0 <= k < Z.of_nat n ->
aview SEGS H' m' (a + k) = aview SEGS H m (a + k).
Proof.
intros H H' m m' a n v k H1 H2 Hk. unfold aview.
rewrite (val_mem_agree SEGS _ _ a n v H1 H2 k Hk). reflexivity.
Qed.

(* ---- the three register values at the __asan_memmove call, 0x858b0 ---- *)
Lemma ld_sll4 : forall z, 0 <= z < 2 ^ 59 ->
alu64 ALU_SLL (Z_to_bv 64 z) (Z_to_bv 64 4) = Z_to_bv 64 (16 * z).
Proof.
intros z Hz. apply bv_eq. rewrite YO0c.alu64_sll.
rewrite (unsigned_lit_small 4) by lia. rewrite (unsigned_lit_small z) by lia.
replace (4 mod 64) with 4 by reflexivity.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. lia.
Qed.
Lemma ld_addr_eq : forall vv ii, 0 <= ii < 2 ^ 30 -> 0 <= vv -> vv + 16 * ii < 2 ^ 64 ->
alu64 ALU_ADD (alu64 ALU_SLL (Z_to_bv 64 ii) (Z_to_bv 64 4)) (Z_to_bv 64 vv) = Z_to_bv 64 (vv + 16 * ii).
Proof.
intros vv ii Hi Hv Hs. rewrite ld_sll4 by lia. rewrite YI08.alu64_add_lit. f_equal. lia.
Qed.
Lemma ld_count_eq : forall nn ii, 0 <= ii -> ii + 1 <= nn -> nn < 2 ^ 30 ->
alu64 ALU_SLL (sext 64 (alu32 ALU_ADD (low32 (Z_to_bv 64 nn))
  (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1)))))) (Z_to_bv 64 4)
= Z_to_bv 64 (16 * (nn - ii - 1)).
Proof.
intros nn ii H0 H1 H2.
assert (RX : bv_unsigned (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1))) = 2 ^ 64 - 1 - ii).
{ rewrite YO0c.alu64_xori_m1. rewrite unsigned_lit_small by lia. apply not64_eq. lia. }
assert (RL : bv_unsigned (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1)))) = 2 ^ 32 - 1 - ii).
{ rewrite YO0c.low32_unsigned, RX. unfold lo32.
  replace (2 ^ 64 - 1 - ii) with ((2 ^ 32 - 1 - ii) + (2 ^ 32 - 1) * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
assert (RN : bv_unsigned (low32 (Z_to_bv 64 nn)) = nn).
{ rewrite YO0c.low32_unsigned, unsigned_lit_small by lia. unfold lo32. apply Z.mod_small. lia. }
assert (RA : bv_unsigned (alu32 ALU_ADD (low32 (Z_to_bv 64 nn))
  (low32 (alu64 ALU_XOR (Z_to_bv 64 ii) (Z_to_bv 64 (-1))))) = nn - ii - 1).
{ rewrite YO0c.alu32_add_unsigned, RN, RL.
  replace (nn + (2 ^ 32 - 1 - ii)) with ((nn - ii - 1) + 1 * 2 ^ 32) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
apply bv_eq. rewrite YO0c.alu64_sll, YO0c.sext64_alu32, RA.
rewrite sx32_small by lia. rewrite (unsigned_lit_small 4) by lia.
replace (4 mod 64) with 4 by reflexivity.
unfold sll64. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16.
rewrite Z.mod_small by lia. rewrite unsigned_lit_small by lia. lia.
Qed.

(* ------------------------------------------------------------------ the representation step *)
Lemma drop_split : forall {X : Type} (A Bs : list X) x,
firstn (length A) (A ++ x :: Bs) ++ skipn (S (length A)) (A ++ x :: Bs) = A ++ Bs.
Proof. intros X A. induction A as [|a A IH]; intros Bs x; cbn; [reflexivity | f_equal; apply IH]. Qed.
Lemma text_rec_length : forall r, length (HarnessRep.text_rec r) = 16%nat.
Proof. intros r. pose proof (text_recs_length [r]) as H. cbn [map concat] in H. rewrite app_nil_r in H. exact H. Qed.
Lemma mbyte_of_aview2 : forall H H' (m m' : word -> option byte) x y,
aview SEGS H' m' x = aview SEGS H m y -> mbyte SEGS (mrestrict H' m') x = mbyte SEGS (mrestrict H m) y.
Proof.
intros H H' m m' x y E. unfold aview in E.
destruct (mbyte SEGS (mrestrict H' m') x) as [b'|], (mbyte SEGS (mrestrict H m) y) as [b|];
cbn in E; try discriminate; [|reflexivity].
injection E as E. f_equal. apply bv_eq. exact E.
Qed.
(* a byte string read at a, found again at b in a later memory *)
Lemma garr8_shift : forall (W W' : world SEGS) mem mem' a b l,
garr8 SEGS (mrestrict (w_H W) mem) a l ->
(forall k, 0 <= k < Z.of_nat (length l) -> aview SEGS (w_H W') mem' (b + k) = aview SEGS (w_H W) mem (a + k)) ->
garr8 SEGS (mrestrict (w_H W') mem') b l.
Proof.
intros W W' mem mem' a b l H Hs j Hj. destruct (H j Hj) as [Hv Hr]. split; [|exact Hr].
intros k Hk. assert (Ek : k = 0%nat) by lia. subst k. specialize (Hv 0%nat Hk).
cbn [Z.of_nat] in Hv |- *. rewrite Z.add_0_r in Hv |- *.
rewrite (mbyte_of_aview2 (w_H W) (w_H W') mem mem' (b + Z.of_nat j) (a + Z.of_nat j) (Hs (Z.of_nat j) ltac:(lia))).
exact Hv.
Qed.
Lemma garr8_kept_at : forall (W W' : world SEGS) mem mem' a b l,
garr8 SEGS (mrestrict (w_H W) mem) a l -> a = b ->
(forall x, b <= x < b + Z.of_nat (length l) -> aview SEGS (w_H W') mem' x = aview SEGS (w_H W) mem x) ->
garr8 SEGS (mrestrict (w_H W') mem') b l.
Proof.
intros W W' mem mem' a b l H <- Hk. apply (garr8_shift W W' mem mem' a a l H). intros k Hk'. apply Hk. lia.
Qed.
Ltac lnorm_in H := repeat (first [rewrite length_map in H | rewrite text_recs_length in H | rewrite text_rec_length in H]).
Ltac lnorm := repeat (first [rewrite length_map | rewrite text_recs_length | rewrite text_rec_length]).

Section c.
Variable B : asyms.
(* list_drop's effect on the representation.  From the list l at LA with i < n records: the text of record i
   has left the allocator's blocks (b1 ++ its block :: b2 became b1 ++ b2); the bytes of records i+1..n-1 now
   sit one record lower in the vector; every other byte the list's predicate reads is as it was (the list head
   but its count, the vector before record i and from record n-1 on, the texts of the other records); the head
   is still writable; the count is n - 1.  Then the list at LA is ldrop_list l i (W_contract.v). *)
Lemma alist_at_drop : forall ly S W mem ly' S' W' mem' LA l lines i,
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
(exists b1 b2, ablocks B ly S = b1 ++ (fst (nth i (HarnessRep.hl_recs l) (0, [])),
   Z.of_nat (length (snd (nth i (HarnessRep.hl_recs l) (0, [])))) + 1) :: b2 /\ ablocks B ly' S' = b1 ++ b2) ->
(forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
awr W' mem' LA 16 ->
val_mem SEGS (arm W' mem') (LA + 8) 4 (HarnessRep.hl_n l - 1) ->
(forall k, 0 <= k < AREC * (HarnessRep.hl_n l - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (HarnessRep.hl_v l + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) mem (HarnessRep.hl_v l + AREC * Z.of_nat i + AREC + k)) ->
(forall a, HarnessRep.hl_v l <= a < HarnessRep.hl_v l + AREC * Z.of_nat i \/
 HarnessRep.hl_v l + AREC * (HarnessRep.hl_n l - 1) <= a < HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
(forall r, In r (HarnessRep.hl_recs (ldrop_list l i)) -> forall a, fst r <= a < fst r + Z.of_nat (length (snd r)) + 1 ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) mem a) ->
alist_at B ly' S' W' mem' LA (ldrop_list l i) lines.
Proof.
intros ly S W mem ly' S' W' mem' LA l lines i HA Hi (b1 & b2 & Eb & Eb') HLA Hawr Hn Hmv Hvec Hrec.
destruct l as [v cap recs junk].
destruct HA as (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9).
unfold ldrop_list in Hrec |- *. unfold HarnessRep.hl_n in *.
cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk] in *.
destruct (nth_split recs (0, []) Hi) as (A & Bs & Hsp & HlA).
set (ri := nth i recs (0, [])) in *. clearbody ri. subst recs. subst i.
rewrite drop_split in Hrec |- *.
unfold arm in *.
rewrite !length_app in H5, Hn, Hmv, Hvec. cbn [length] in H5, Hn, Hmv, Hvec.
assert (Hcap : 0 < cap) by lia.
destruct H6 as [(Hc0 & _) | (_ & Hvin & Hjl & Hg)]; [lia|].
rewrite length_app in Hjl. cbn [length] in Hjl.
assert (ND : List.NoDup (map fst A ++ fst ri :: map fst Bs)) by (apply NoDup_ListNoDup; rewrite map_app in H7; exact H7).
assert (Hni : ~ In (fst ri) (map fst A ++ map fst Bs)) by exact (NoDup_remove_2 _ _ _ ND).
assert (Hvi : v <> fst ri) by (intros E; apply H8; rewrite E, map_app; apply in_or_app; right; left; reflexivity).
unfold alist_at.
cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]. unfold HarnessRep.hl_n.
cbn [HarnessRep.hl_recs]. unfold arm.
split; [apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [intros k Hk; apply HLA; cbn in Hk; lia | exact H1]|].
split.
{ replace (Z.of_nat (length (A ++ Bs))) with (Z.of_nat (length A + Datatypes.S (length Bs)) - 1) by (rewrite length_app; lia).
  exact Hn. }
split; [apply (val_mem_kept SEGS (w_H W) (w_H W') mem mem'); [intros k Hk; apply HLA; cbn in Hk; lia | exact H3]|].
split; [exact Hawr|].
split; [rewrite length_app; lia|].
split.
{ right. split; [exact Hcap|]. split.
  { rewrite Eb'. rewrite Eb in Hvin. apply in_app_or in Hvin as [Hx | [Hx | Hx]]; apply in_or_app;
    [left; exact Hx | | right; exact Hx].
    exfalso. injection Hx as Ex _. exact (Hvi (eq_sym Ex)). }
  split.
  { rewrite !length_app, text_rec_length. unfold AREC in *. lia. }
  (* the vector: records 0..i-1 kept, records i+1..n-1 moved down, then the last record's old slot and the junk *)
  assert (NE : A ++ ri :: Bs <> []) by (intros E; apply app_eq_nil in E as [_ E]; discriminate).
  pose proof (@app_removelast_last _ (A ++ ri :: Bs) (0, []) NE) as ERL.
  set (Rl := List.removelast (A ++ ri :: Bs)) in *. set (rl := List.last (A ++ ri :: Bs) (0, [])) in *.
  assert (HRl : length Rl = (length A + length Bs)%nat).
  { assert (L := f_equal (@length _) ERL). rewrite !length_app in L. cbn [length] in L. lia. }
  pose proof Hg as Hg2. rewrite ERL in Hg2 at 1.
  unfold HarnessRep.bzs in Hg, Hg2 |- *.
  rewrite (map_app HarnessRep.text_rec), concat_app in Hg2. cbn [map concat] in Hg2. rewrite app_nil_r in Hg2.
  rewrite !map_app, <- !app_assoc in Hg2.
  apply garr8_app in Hg2 as [_ Hg2]. apply garr8_app in Hg2 as [HTl _].
  rewrite length_map, text_recs_length, HRl in HTl.
  rewrite (map_app HarnessRep.text_rec), concat_app in Hg. cbn [map concat] in Hg. rewrite !map_app, <- !app_assoc in Hg.
  apply garr8_app in Hg as [HA' Hg]. apply garr8_app in Hg as [HTi Hg]. apply garr8_app in Hg as [HB' HJ'].
  lnorm_in HB'. lnorm_in HJ'.
  rewrite (map_app HarnessRep.text_rec), concat_app, !map_app, <- !app_assoc.
  apply garr8_app. split.
  { apply (garr8_kept_at W W' mem mem' v v _ HA' eq_refl). intros x Hx. lnorm_in Hx. apply Hvec. left. unfold AREC. lia. }
  lnorm. apply garr8_app. split.
  { apply (garr8_shift W W' mem mem' _ _ _ HB'). intros k Hk. lnorm_in Hk.
    match goal with |- aview _ _ _ ?x = aview _ _ _ ?y =>
      replace x with (v + AREC * Z.of_nat (length A) + k) by (unfold AREC; lia);
      replace y with (v + AREC * Z.of_nat (length A) + AREC + k) by (unfold AREC; lia) end.
    apply Hmv. unfold AREC. lia. }
  lnorm. apply garr8_app. split.
  { apply (garr8_kept_at W W' mem mem' _ _ _ HTl); [lia|]. intros x Hx. lnorm_in Hx. apply Hvec. right. unfold AREC. lia. }
  lnorm. apply (garr8_kept_at W W' mem mem' _ _ _ HJ'); [lia|]. intros x Hx. lnorm_in Hx.
  apply Hvec. right. unfold AREC in *. lia. }
split.
{ apply NoDup_ListNoDup. rewrite map_app. apply (NoDup_remove_1 _ _ (fst ri)). exact ND. }
split.
{ intros Hin. apply H8. rewrite map_app in Hin |- *. apply in_app_or in Hin as [Hx|Hx]; apply in_or_app;
  [left; exact Hx | right; right; exact Hx]. }
rewrite Forall_forall in H9 |- *. intros r Hr.
assert (Hr0 : In r (A ++ ri :: Bs))
by (apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx]).
destruct (H9 r Hr0) as (R1 & R2 & R3 & R4).
assert (Hfr : fst r <> fst ri) by (intros E; apply Hni; rewrite <- E, <- map_app; apply in_map; exact Hr).
split.
{ rewrite Eb'. rewrite Eb in R1. apply in_app_or in R1 as [Hx | [Hx | Hx]]; apply in_or_app;
  [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. exact (Hfr (eq_sym Ex)). }
split; [|split; [exact R3 | exact R4]].
apply (garr8_shift W W' mem mem' _ _ _ R2). intros k Hk. apply (Hrec r Hr).
unfold HarnessRep.bzs in Hk. rewrite length_map, length_app in Hk. cbn [length] in Hk. lia.
Qed.
End c.

(* ------------------------------------------------------------------ the list's records and cells
   (lib/A/W_list_drop_top.v's four image-independent helpers, commit f83b4c2732c) *)
(* record i's text pointer, an 8-byte cell of the vector (lib/A/W_list_find.v alist_rec_fields, its first half) *)
Lemma ld_rec_ptr : forall B ly S W mem LA l lines j,
alist_at B ly S W mem LA l lines -> (j < length (HarnessRep.hl_recs l))%nat ->
val_mem SEGS (arm W mem) (HarnessRep.hl_v l + 16 * Z.of_nat j) 8
  (fst (nth j (HarnessRep.hl_recs l) (0, [])) mod 2 ^ 64).
Proof.
intros B ly S W mem LA l lines j HA Hj.
destruct HA as (_ & _ & _ & _ & Hcap & Hv & _).
destruct Hv as [(Hc0 & _) | (_ & _ & _ & Hg)].
{ unfold HarnessRep.hl_n in Hcap. lia. }
destruct (nth_split (HarnessRep.hl_recs l) (0, []) Hj) as (l1 & l2 & Hsp & Hl1).
set (r := nth j (HarnessRep.hl_recs l) (0, [])) in *.
rewrite Hsp in Hg. rewrite map_app, concat_app in Hg. cbn [map concat] in Hg.
unfold HarnessRep.bzs in Hg. rewrite !map_app in Hg. rewrite <- !app_assoc in Hg.
apply garr8_app in Hg as [_ Hg]. rewrite length_map, text_recs_length, Hl1 in Hg.
unfold HarnessRep.text_rec, OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Lib.Mem.le8 in Hg.
rewrite !map_app, <- !app_assoc in Hg.
apply garr8_app in Hg as [H1 _].
apply garr8_val_mem8 in H1.
rewrite Z_to_bv_unsigned in H1. unfold bv_wrap in H1. change (bv_modulus 64) with (2 ^ 64) in H1.
replace (HarnessRep.hl_v l + Z.of_nat (16 * j)) with (HarnessRep.hl_v l + 16 * Z.of_nat j) in H1 by lia.
exact H1.
Qed.
(* the shadow address of an 8-aligned object, as the machine computes it (W_list_find.v lf_srl3) *)
Lemma ld_srl3 : forall X, 0 <= X < 2 ^ 63 ->
alu64 ALU_SRL (Z_to_bv 64 X) (Z_to_bv 64 3) = Z_to_bv 64 (X / 8).
Proof.
intros X HX.
assert (HD : 0 <= X / 8 < 2 ^ 63) by (split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
apply bv_eq. rewrite alu64_unsigned. cbn [zalu_raw].
rewrite (unsigned_lit_small X) by lia. rewrite (unsigned_lit_small 3) by lia.
rewrite (unsigned_lit_small (X / 8)) by lia.
change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
first [ unfold bv_wrap; change (bv_modulus 64) with (2 ^ 64) | unfold zcanon, M64 ].
apply Z.mod_small. lia.
Qed.
(* the records list_drop leaves: each one of the list before, none of them record i *)
Lemma ld_recs_drop : forall (recs : list (Z * list byte)) i r, (i < length recs)%nat -> List.NoDup (map fst recs) ->
In r (firstn i recs ++ skipn (S i) recs) -> In r recs /\ fst r <> fst (nth i recs (0, [])).
Proof.
intros recs i r Hi ND Hr.
destruct (nth_split recs (0, []) Hi) as (A & Bs & Hsp & HlA).
set (ri := nth i recs (0, [])) in *. clearbody ri. subst recs i.
rewrite drop_split in Hr. rewrite map_app in ND. cbn [map] in ND.
split.
- apply in_app_or in Hr as [Hx|Hx]; apply in_or_app; [left; exact Hx | right; right; exact Hx].
- intros E. apply (NoDup_remove_2 _ _ _ ND). rewrite <- E, <- map_app. apply in_map. exact Hr.
Qed.
(* two values that agree byte for byte at a read the same through the ASan view *)
Lemma ld_aview_agree : forall (W W' : world SEGS) m m' a (n : nat) x k,
val_mem SEGS (arm W m) a n x -> val_mem SEGS (arm W' m') a n x -> 0 <= k < Z.of_nat n ->
aview SEGS (w_H W') m' (a + k) = aview SEGS (w_H W) m (a + k).
Proof.
intros W W' m m' a n x k H1 H2 Hk. unfold aview. cbv beta. f_equal.
exact (val_mem_agree SEGS _ _ a n x H1 H2 k Hk).
Qed.

(* ------------------------------------------------------------------ image B's values, in the engine's
   vocabulary (YP0e.U / YP0e.Sg, as lib/B/W_traps.v states its trap lemmas).  The forms are the ones the runner
   builds at list_drop's checks (MEASURED, vm_compute on the symbolic states): &l->v[i] is
   SAlu ADD (SAlu SLL i 4) v, &l->v[i+1] is SAlu ADD (SAlu ADD (SAlu SLL i 4) 16) v, n - i is
   SAlu ADD (SMd MUL i (-1)) n, and the memmove's count is SAlu SLL (SAluw ADD (n - i) (-1)) 4. *)
Lemma ldU_sll4 : forall E a x, U E a = x -> 0 <= x < 2 ^ 59 -> U E (SAlu ALU_SLL a (SLit 4)) = 16 * x.
Proof.
intros E a x Ha Hx. rewrite U_SAlu, Ha, U_SLit. cbn [zalu_raw].
rewrite (zcanon_id 4) by (unfold M64; lia). change (Z.land 4 63) with 4.
rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 4) with 16. rewrite zcanon_id by (unfold M64; lia). lia.
Qed.
Lemma ldU_o : forall E k x, ew E k = Z_to_bv 64 x -> 0 <= x < 2 ^ 59 ->
U E (SAlu ALU_SLL (SOff k 0) (SLit 4)) = 16 * x.
Proof. intros E k x Hk Hx. apply ldU_sll4; [apply U_atom; [exact Hk | lia] | exact Hx]. Qed.
Lemma ldU_p : forall E k x vv, ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 vv -> 0 <= x < 2 ^ 59 -> 0 <= vv ->
16 * x + vv < 2 ^ 64 -> U E (SAlu ALU_ADD (SAlu ALU_SLL (SOff k 0) (SLit 4)) (SOff 32 0)) = 16 * x + vv.
Proof.
intros E k x vv Hk Hv Hx Hv0 Hs.
apply trap_U_add; [apply ldU_o; [exact Hk | exact Hx] | apply U_atom; [exact Hv | lia] | lia].
Qed.
Lemma ldU_p1 : forall E k x vv, ew E k = Z_to_bv 64 x -> ew E 32 = Z_to_bv 64 vv -> 0 <= x < 2 ^ 59 -> 0 <= vv ->
16 * x + 16 + vv < 2 ^ 64 ->
U E (SAlu ALU_ADD (SAlu ALU_ADD (SAlu ALU_SLL (SOff k 0) (SLit 4)) (SLit 16)) (SOff 32 0)) = 16 * x + 16 + vv.
Proof.
intros E k x vv Hk Hv Hx Hv0 Hs.
apply trap_U_add; [| apply U_atom; [exact Hv | lia] | lia].
apply trap_U_add; [apply ldU_o; [exact Hk | exact Hx] | apply U_lit; lia | lia].
Qed.
Lemma ldU_x : forall E k x nn, ew E k = Z_to_bv 64 x -> ew E 33 = Z_to_bv 64 nn -> 0 <= x <= nn -> nn < 2 ^ 64 ->
U E (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit (-1))) (SOff 33 0)) = nn - x.
Proof.
intros E k x nn Hk Hn Hx Hn64.
rewrite U_SAlu, U_SMd, (U_atom E k x Hk) by lia. rewrite (U_atom E 33 nn Hn) by lia. rewrite U_SLit.
cbn [zalu_raw zmd_raw]. unfold zcanon, M64.
assert (Hm : (-1) mod 2 ^ 64 = 2 ^ 64 - 1) by reflexivity. rewrite Hm.
rewrite Z.add_mod_idemp_l by lia.
replace (x * (2 ^ 64 - 1) + nn) with ((nn - x) + x * 2 ^ 64) by ring.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.
Lemma ldS_of_U : forall E a x, U E a = x -> 0 <= x < 2 ^ 63 -> Sg E a = x.
Proof. intros E a x Ha Hx. rewrite S_of_U, Ha. apply swrap64_id. unfold half64. lia. Qed.
Lemma ldU_decw : forall E x j, U E x = j -> 1 <= j < 2 ^ 31 -> U E (SAluw ALU_ADD x (SLit (-1))) = j - 1.
Proof.
intros E x j Hx Hj.
assert (HS : Sg E (SAluw ALU_ADD x (SLit (-1))) = j - 1).
{ rewrite S_SAluw, U_SLit, Hx. cbn [zalu_raw].
  rewrite (trap_swrap32 _ (j - 1)); [apply swrap32_id; lia|].
  change (zcanon (-1) mod 2 ^ 32) with (2 ^ 32 - 1). rewrite (Z.mod_small j (2 ^ 32)) by lia.
  replace (j + (2 ^ 32 - 1)) with (j - 1 + 1 * 2 ^ 32) by lia. apply Z_mod_plus_full. }
rewrite U_of_S, HS. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64). apply Z.mod_small. lia.
Qed.
Lemma ldU_count : forall E k x nn, ew E k = Z_to_bv 64 x -> ew E 33 = Z_to_bv 64 nn -> 0 <= x -> x + 1 <= nn < 2 ^ 31 ->
U E (SAlu ALU_SLL (SAluw ALU_ADD (SAlu ALU_ADD (SMd M_MUL (SOff k 0) (SLit (-1))) (SOff 33 0)) (SLit (-1))) (SLit 4))
= 16 * (nn - x - 1).
Proof.
intros E k x nn Hk Hn Hx Hxn.
apply ldU_sll4; [| lia].
apply ldU_decw; [| lia].
apply ldU_x; [exact Hk | exact Hn | lia | lia].
Qed.
(* &l->v[i] and &l->v[i+1] are 8-aligned when the vector is 16-aligned *)
Lemma ld_mod8 : forall v k, v mod 16 = 0 -> (16 * k + v) mod 8 = 0.
Proof.
intros v k H. rewrite (Z.div_mod v 16) by lia. rewrite H, Z.add_0_r.
replace (16 * k + 16 * (v / 16)) with ((2 * k + 2 * (v / 16)) * 8) by ring. apply Z_mod_mult.
Qed.
Lemma ld_mod8b : forall v k, v mod 16 = 0 -> (16 * k + 16 + v) mod 8 = 0.
Proof. intros v k H. replace (16 * k + 16 + v) with (16 * (k + 1) + v) by ring. exact (ld_mod8 v (k + 1) H). Qed.

(* ------------------------------------------------------------------ the walk *)
Definition A_list_drop : Z := AF_fr_list_drop.
Definition A_list_dropP : Z := BASE + A_list_drop.
Definition A_ld_body : Z := AF_fr_list_drop + 0x7c.   (* 0x85bcc, a0 = &l->v[i], its UBSan checks passed *)
Definition A_ld_epi : Z := AF_fr_list_drop + 0x160.   (* 0x85cb0, the epilogue *)
Definition LD_CEIL : Z := 140737486618624.            (* 0x7fffff800000, the ceiling's upper bound *)
Definition ld_Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the registers the body (0x85bcc .. 0x85cb0) may leave changed: at 0x85cb0 s0 = 16 i, s1 = l + 8, s2 = SB + (l+8)/8
   (MEASURED), and s3..s5 hold computed forms of their entry values; the epilogue reloads s0..s5 from the frame *)
Definition LDB_CLOB : list (bv 5) := 8%bv :: 9%bv :: 18%bv :: 19%bv :: 20%bv :: 21%bv :: CLOB.
Definition LDB_KEPT : list (bv 5) := [2; 3; 4; 22; 23; 24; 25; 26; 27]%bv.
Lemma ldb_clob_kept : forall r : bv 5, reg_in r LDB_CLOB = false -> r = 0%bv \/ In r LDB_KEPT.
Proof.
intros r Hr. pose proof (all_regs_in r) as Hin. cbv [all_regs In] in Hin.
repeat (destruct Hin as [<-|Hin]; [first [left; reflexivity | vm_compute in Hr; discriminate | right; cbv; tauto] |]).
destruct Hin.
Qed.

(* ---- the frame bookkeeping of a walk that runs in several pieces (one per UBSan trap branch) ----
   After each run the runner leaves  frame_of Ev rs (mrestrict H mp) (mrestrict H mn)  and
   mem_grows (mrestrict H mp) (mrestrict H mn).  These tactics fold them into the running facts
   KQ (body: every byte off the list head kept) / KT (prologue: every byte off the frame and the head kept) and
   PQ / PT (presence kept), so that every later step reads one fact per memory. *)
Ltac ld_nowr9 U9 Hout :=
let r := fresh "r" in let Hinr := fresh "Hinr" in let Hr := fresh "Hr" in
intros (r & Hinr & Hr); vm_compute in Hinr;
repeat match type of Hinr with
| _ \/ _ => destruct Hinr as [<- | Hinr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; cbn [ew ewset Nat.eqb] in Hr;
    rewrite ?U9 in Hr; first [clear - Hr; lia | apply Hout; clear - Hr; lia] | ]
| False => destruct Hinr
end.
Ltac ld_fold9 LA U9 KQ PQ :=
lazymatch type of KQ with forall a, _ -> _ -> aview ?sg ?H ?mp a = aview _ _ ?m0 a =>
lazymatch goal with
| HFx : frame_of ?Ev ?rs (mrestrict H mp) (mrestrict H ?mn) |- _ =>
lazymatch goal with
| HGx : mem_grows (mrestrict H mp) (mrestrict H mn) |- _ =>
  assert (KQn : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview sg H mn a = aview sg H m0 a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hout := fresh "Hout" in intros a Ha Hout;
      rewrite (aview_kept_out Ev rs H mp mn HFx a Ha); [exact (KQ a Ha Hout) | ld_nowr9 U9 Hout]);
  assert (PQn : forall x, apresent H m0 x -> apresent H mn x)
  by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exact (apresent_grows H mp mn x HGx (PQ x Hx)));
  clear KQ PQ HFx HGx; rename KQn into KQ; rename PQn into PQ
end end end.
Ltac ld_nowrT Usp E10 Hs Hl :=
let r := fresh "r" in let Hinr := fresh "Hinr" in let Hr := fresh "Hr" in
intros (r & Hinr & Hr); vm_compute in Hinr;
repeat match type of Hinr with
| _ \/ _ => destruct Hinr as [<- | Hinr];
  [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; cbn [ew ewset Nat.eqb] in Hr;
    rewrite ?Usp in Hr; rewrite ?E10 in Hr; rewrite ?unsigned_lit_small in Hr by lia;
    first [clear - Hr; lia | apply Hs; unfold LDROP_FRAME; clear - Hr; lia | apply Hl; clear - Hr; lia] | ]
| False => destruct Hinr
end.
Ltac ld_foldT SP LA Usp E10 KT PT :=
lazymatch type of KT with forall a, _ -> _ -> _ -> aview ?sg ?H ?mp a = aview _ _ ?m0 a =>
lazymatch goal with
| HFx : frame_of ?Ev ?rs (mrestrict H mp) (mrestrict H ?mn) |- _ =>
lazymatch goal with
| HGx : mem_grows (mrestrict H mp) (mrestrict H mn) |- _ =>
  assert (KTn : forall a, 0 <= a < 2 ^ 64 -> ~ (SP - LDROP_FRAME <= a < SP) -> ~ (LA <= a < LA + 16) ->
    aview sg H mn a = aview sg H m0 a)
  by (let a := fresh "a" in let Ha := fresh "Ha" in let Hs := fresh "Hs" in let Hl := fresh "Hl" in intros a Ha Hs Hl;
      rewrite (aview_kept_out Ev rs H mp mn HFx a Ha); [exact (KT a Ha Hs Hl) | ld_nowrT Usp E10 Hs Hl]);
  assert (PTn : forall x, apresent H m0 x -> apresent H mn x)
  by (let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; exact (apresent_grows H mp mn x HGx (PT x Hx)));
  clear KT PT HFx HGx; rename KTn into KT; rename PTn into PT
end end end.
(* name the machine state, the frame and the growth a run just left *)
(* a run that stops at a call leaves an st_ok state (the callee's pc), any other an st_ok_pi one *)
Ltac ld_name_ms msn :=
lazymatch goal with
| HSx : st_ok_pi _ _ _ _ (restrict _ ?msx) |- _ => rename msx into msn
| HSx : st_ok _ _ _ (restrict _ ?msx) |- _ => rename msx into msn
end.
Ltac ld_names msn Frn Grn :=
ld_name_ms msn;
lazymatch goal with HFx : frame_of _ _ _ (mrestrict _ (ms_mem msn)) |- _ => rename HFx into Frn end;
lazymatch goal with HGx : mem_grows _ (mrestrict _ (ms_mem msn)) |- _ => rename HGx into Grn end.
(* a register's value as the runner holds it, read as U (no cbn of its form) *)
Ltac prreg_u HS r Hr :=
lazymatch type of HS with
| st_ok_pi ?segs ?val ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_pi_restrict_reg H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr; rewrite (denot_lit_U E e) in Hr
| st_ok ?segs ?E ?ss (restrict ?H ?ms) =>
pose proof (st_ok_restrict_reg segs H E ss ms r HS) as Hr;
let e := eval vm_compute in (sr_get (ss_regs ss) r) in change (sr_get (ss_regs ss) r) with e in Hr;
cbn [ms_regs restrict mkst] in Hr; rewrite (denot_lit_U E e) in Hr
end.
(* the awr side goal of a run whose one writable region is the list head at atom 9 (a G range) *)
Ltac ld_awr9 BV HLG :=
lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end;
apply awr_ok_x_cons_g; [cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV;
  let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HLG; clear - Ha; lia | apply awr_ok_x_nil].

(* ---- THE GENERIC WALK (route (b), step 3): the Section hypotheses are the AR walk's, over any allocator relation
   ARx with its laws (PST / ARx / hl / LAWS), HP0 (the hidden-head set is empty in every ARx state: a Theorem Labs lane's
   ruling; W_journal_x Section hp0), and the callee contracts' generic twins at the same PST / ARx (AFREE:
   W_journal_x.afree_cf_rule_c_x at the caller-context table CTX, AMOVE: W_sites_x.amemmove_realizes_x).  The free
   call hands the rule the chain [] (s0 holds 16 i, not a frame pointer), so its trace is the singleton [its return
   address], the closed fact HCTX_ld_free (a Theorem Labs lane's ruling (c): the _c rule, as lib/A/W_list_free.v takes it).
   The journal is W_journal_x.ajournal_gx_x at the walk's own G, XO = 0, OUT = []. ---- *)
Section d.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
(* the room round (ROOM-TEXTS.md v3 sha256 767baa12f13c; internal record): the room invariant and the live counts, the free rule's two new premises *)
Variable RP : roomp.
Variable G : list (Z * Z).
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* fuzz_reply.asan-ubsan objdump: 0x85be8 jal __interceptor_trampoline_free; returns to 0x85bec = list_drop 0x85b50 + 0x9c *)
Hypothesis HCTX_ld_free : In [BASE + AF_fr_list_drop + 0x9c] CTX.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).
(* rom_view has to cross the free call: acall_kept keeps an image byte outside the allocator's statics and errno,
   and an owned read-only byte is one of the relation's pinned const cells (W_journal.v rom_pinned, read through
   W_journal_x.rom_pinned_view_x).  ROM bytes are off G.
   Facts about the instance and G, not about list_drop (rom_out's shape, W_journal.v); lib/A/W_list_drop.v's text. *)
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL. Let HBfree := pal_free B TL.
Let RUN := paj_run_x_x B PST ARx LAWS G HG 0 [].
Let RUNTO := paj_run_to_x_x B PST ARx LAWS G HG 0 [].
Local Notation AJG := (ajournal_gx_x SEGS B PST ARx G 0 []).
Let BR := paj_branch (PI := PI).
Let RET := paj_ret_at (PL := PL_fr) (PI := PI).

(* ---- the entry 0x85b50 ---- *)
Definition ld_Bx : sv := SOff 35 0.
Definition ld_lreg (m : nat) : YP09.region :=
YP09.mkRegion (Some m) 0 16 0 16
[YP09.mkChunk 0 (CVal 8 (SOff 32 0)); YP09.mkChunk 8 (CVal 4 (SOff 33 0)); YP09.mkChunk 12 (CVal 4 (SOff 34 0))].
Definition ld_regions : smem := [ stack_region LDROP_FRAME; got_regionP; bcell_regionP 35; ld_lreg 10 ].
(* i, n, cap < 2^30 (alist_at's hl_cap < 2^30), the vector 16-aligned: with these the runner decides every UBSan check
   of the prologue but the pointer-overflow check of &l->v[i] (0x85bc4) *)
Definition ld_facts : facts :=
mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (10%nat, mkAF 0x10000 (0x5fc000 - 16) 3); (11%nat, mkAF 0 (2 ^ 30 - 1) 0);
(32%nat, mkAF 4096 LD_CEIL 4); (33%nat, mkAF 0 (2 ^ 30 - 1) 0); (34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF SB SB 0) ] [] [].
Definition ss_ld : sstate := mkSS A_list_drop sr_atoms ld_regions None ld_facts.
Definition ld_SH : list shent := [ mkSHE 10 0 16 ].
Definition ld_extra (l : HarnessRep.hlist) : list word :=
map (Z_to_bv 64) [HarnessRep.hl_v l; HarnessRep.hl_n l; HarnessRep.hl_cap l; SB].

Lemma ld_LA_range : forall LA, (forall a, LA <= a < LA + 16 -> inG G a) -> 0x10000 <= LA /\ LA + 16 <= 0x5fc000.
Proof.
intros LA HLG.
pose proof (pa_img_range LA (proj1 (HG LA (HLG LA ltac:(lia))))) as H1.
pose proof (pa_img_range (LA + 15) (proj1 (HG (LA + 15) (HLG (LA + 15) ltac:(lia))))) as H2.
lia.
Qed.

Lemma ld_entry_x : forall W ly S Hp regs mem md ch LA l lines i,
afn_pre_x SEGS B ARx LDROP_STK ly S Hp W regs mem md ch ->
getr regs 10 = w64 LA -> getr regs 11 = w64 (Z.of_nat i) ->
alist_at B ly S W mem LA l lines ->
(i < length (HarnessRep.hl_recs l))%nat ->
LA mod 8 = 0 -> azs B LA 16 ->
(forall a, LA <= a < LA + 16 -> inG G a) ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ld_extra l))) ss_ld
(restrict (w_H W) (mkst regs (Z_to_bv 64 A_list_dropP) mem (seg_rom SEGS)))
/\ sh_ok SEGS ld_Bx ld_SH (Eimg (Ereg regs (ld_extra l))) (mrestrict (w_H W) mem).
Proof.
intros W ly S Hp regs mem md ch LA l lines i HPRE H10 H11 HL Hi HLA8 HZS HLG.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (ld_LA_range LA HLG) as HLAR.
pose proof HL as (M1 & M2 & M3 & Mawr & (Hn0 & Hcap) & Hvb & _).
assert (HnZ : 0 < HarnessRep.hl_n l) by (unfold HarnessRep.hl_n; lia).
assert (Hcap0 : 0 < HarnessRep.hl_cap l) by lia.
destruct Hvb as [(Hc0 & _) | (_ & Hvin & _ & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & _ & _ & _).
assert (Hreq0 : req_size (AREC * HarnessRep.hl_cap l) = AREC * HarnessRep.hl_cap l)
by (unfold req_size; destruct (Z.eqb_spec (AREC * HarnessRep.hl_cap l) 0); unfold AREC in *; lia).
rewrite Hreq0 in Hvceil.
assert (HvR : 0 <= HarnessRep.hl_v l < 2 ^ 64) by (unfold AREC in *; lia).
assert (HvC : HarnessRep.hl_v l + AREC * HarnessRep.hl_cap l <= LD_CEIL)
by (unfold req_size in Hvceil; destruct (Z.eqb_spec (AREC * HarnessRep.hl_cap l) 0); unfold LD_CEIL, AREC in *; lia).
assert (WS : LDROP_STK = 16448) by reflexivity.
destruct (alx_const _ _ _ LAWS ly S Hp W mem md HAR) as (Kcell & _ & Kgot & _).
rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell.
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ld_extra l))). pose proof pa_B_ok as HBASE.
assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 10 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat i)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 11 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 (HarnessRep.hl_v l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (HarnessRep.hl_n l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 (HarnessRep.hl_cap l)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pal_got_cell B TL) as HgcD. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR.
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (DGOT : VAL (A_OBJ 0) + 8 <= LA \/ LA + 16 <= VAL (A_OBJ 0)).
{ destruct (Z_le_gt_dec (VAL (A_OBJ 0) + 8) LA) as [Hd|Hd]; [left; lia|].
  destruct (Z_le_gt_dec (LA + 16) (VAL (A_OBJ 0))) as [Hd2|Hd2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec LA (VAL (A_OBJ 0))) as [Hd3|Hd3].
  - apply (proj1 (proj2 (GRT (VAL (A_OBJ 0)) (HLG (VAL (A_OBJ 0)) ltac:(lia))))). lia.
  - apply (proj1 (proj2 (GRT LA (HLG LA ltac:(lia))))). lia. }
assert (DCELL : VAL (A_OBJ 30) + 8 <= LA \/ LA + 16 <= VAL (A_OBJ 30)).
{ destruct (Z_le_gt_dec (VAL (A_OBJ 30) + 8) LA) as [Hd|Hd]; [left; lia|].
  destruct (Z_le_gt_dec (LA + 16) (VAL (A_OBJ 30))) as [Hd2|Hd2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec LA (VAL (A_OBJ 30))) as [Hd3|Hd3].
  - apply (proj2 (proj2 (GRT (VAL (A_OBJ 30)) (HLG (VAL (A_OBJ 30)) ltac:(lia))))). lia.
  - apply (proj2 (proj2 (GRT LA (HLG LA ltac:(lia))))). lia. }
assert (HiZ : 0 <= Z.of_nat i < HarnessRep.hl_n l) by (unfold HarnessRep.hl_n; lia).
split.
- unfold ss_ld, A_list_dropP. apply pa_entry_st_ok_full.
+ apply regs_ok_Eimg_Ereg.
+ vm_compute. reflexivity.
+ unfold ld_regions, stack_region, got_regionP, bcell_regionP, ld_lreg, LDROP_FRAME.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
intros o Ho. apply (apresent_writable SEGS). apply Hpres. rewrite WS. lia.
* rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
[cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kgot).
* rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (VAL (A_OBJ 30)) 0 8 ld_Bx SB);
[cbn [sv_denot ld_Bx]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
rewrite Z.add_0_r. exact (val_mem_of_rdword SEGS (w_H W) mem _ _ Kcell).
* rewrite (VB 10%nat LA E10) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (Mawr o ltac:(lia))|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ LA 0 8 (SOff 32 0) (HarnessRep.hl_v l));
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact M1.
-- apply (chunk_ok_val SEGS E _ LA 8 4 (SOff 33 0) (HarnessRep.hl_n l));
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact M2.
-- apply (chunk_ok_val SEGS E _ LA 12 4 (SOff 34 0) (HarnessRep.hl_cap l));
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
exact M3.
+ apply pairwise_disjoint_of_extents.
unfold ld_regions, stack_region, got_regionP, bcell_regionP, ld_lreg, extent_of_region, LDROP_FRAME.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
rewrite (VB 10%nat LA E10) by lia. cbn [base_val]. rewrite Usp.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgcD HgotR HLAR DGOT DCELL. clear.
unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ld_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
rewrite Usp, E10, E11, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, LD_CEIL; lia).
change (2 ^ 4) with 16. change (2 ^ 3) with 8. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear DGOT DCELL.
revert Hslo Hshi H47 Hceil Hal16 C1 C3 WS Hstk0 HLAR HLA8 Hn0 Hcap HnZ HiZ Hv4096 Hvceil Hcap0 Hv16 HvC.
unfold HarnessRep.hl_n. clear. unfold SB, LD_CEIL, AREC, zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL.
intros. repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ld_SH. constructor; [|constructor].
apply (shent_ok_of_range SEGS (w_H W) mem _ ld_Bx 10 LA 16 LA 0 16).
+ exact (azs_range_addressable_x B ARx LAWS ly S Hp W mem md LA 16 HAR HZS).
+ unfold U, ld_Bx. cbn [sv_denot]. rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned.
rewrite unsigned_lit_small by (unfold SB; lia). reflexivity.
+ unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
+ lia.
+ lia.
+ intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
Qed.

(* ---- the body 0x85bcc: a0 = &l->v[i], s0 = i, s1 = l, s2 = SB, s3 = 16 i, s4 = SB + l/8, s5 = (i < 0) = 0 ---- *)
Definition ldb_Bx : sv := SOff 18 0.
Definition ldb_rreg : YP09.region :=
YP09.mkRegion (Some 10%nat) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SOff 35 0))].
Definition ldb_regions : smem := [ ld_lreg 9; ldb_rreg ].
Definition ldb_sr : list sv :=
sr_set (sr_set (sr_set sr_atoms 19 (SAlu ALU_SLL (SOff 8 0) (SLit 4)))
  20 (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 18 0))) 21 (SLit 0).
(* n >= 1 (i < n): with it the runner decides the int32 check of n - 1 at 0x85ca0 *)
Definition ldb_facts : facts :=
mkFacts [ (8%nat, mkAF 0 (2 ^ 30 - 1) 0); (9%nat, mkAF 0x10000 (0x5fc000 - 16) 3); (10%nat, mkAF 4096 LD_CEIL 3);
(18%nat, mkAF SB SB 0); (32%nat, mkAF 4096 LD_CEIL 4); (33%nat, mkAF 1 (2 ^ 30 - 1) 0);
(34%nat, mkAF 0 (2 ^ 30 - 1) 0); (35%nat, mkAF 4096 LD_CEIL 0) ] [] [].
Definition ss_ldb : sstate := mkSS A_ld_body ldb_sr ldb_regions None ldb_facts.
Definition ldb_SH : list shent := [ mkSHE 9 0 16; mkSHE 10 0 8 ].
(* after the free the record's block is gone (its shadow is poisoned) and the code never checks it again *)
Definition ldb_SH2 : list shent := [ mkSHE 9 0 16 ].
Definition ldb_extra (v n cap s_i : Z) : list word := map (Z_to_bv 64) [v; n; cap; s_i].

Lemma ldb_entry_x : forall W (regs : bvmap 5 word) memc lyc Sc Hpc mdc LA v n cap (i : nat) s_i len_i,
ARx lyc Sc Hpc W memc mdc ->
getr regs 8 = w64 (Z.of_nat i) -> getr regs 9 = w64 LA -> getr regs 10 = w64 (v + AREC * Z.of_nat i) ->
getr regs 18 = w64 SB -> getr regs 19 = w64 (AREC * Z.of_nat i) -> getr regs 20 = w64 (SB + LA / 8) ->
getr regs 21 = w64 0 ->
0 <= Z.of_nat i < n -> n <= cap < 2 ^ 30 ->
LA mod 8 = 0 -> (forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
val_mem SEGS (arm W memc) LA 8 v -> val_mem SEGS (arm W memc) (LA + 8) 4 n ->
val_mem SEGS (arm W memc) (LA + 12) 4 cap -> awr W memc LA 16 ->
val_mem SEGS (arm W memc) (v + AREC * Z.of_nat i) 8 s_i -> 0 <= s_i < 2 ^ 64 ->
In (v, AREC * cap) (ablocks B lyc Sc) -> In (s_i, len_i + 1) (ablocks B lyc Sc) -> 0 <= len_i ->
st_ok_pi SEGS VAL (Eimg (Ereg regs (ldb_extra v n cap s_i))) ss_ldb
(restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_ld_body)) memc (seg_rom SEGS)))
/\ sh_ok SEGS ldb_Bx ldb_SH (Eimg (Ereg regs (ldb_extra v n cap s_i))) (mrestrict (w_H W) memc).
Proof.
intros W regs memc lyc Sc Hpc mdc LA v n cap i s_i len_i HAR H8 H9 H10 H18 H19 H20 H21 Hi Hn HLA8 HLG HZS
Mv Mn Mc Mawr Ms HsR Hvin Hsin Hlen.
pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
pose proof (ld_LA_range LA HLG) as HLAR.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & Hvapp & _ & _).
assert (Hreq0 : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Hreq0 in Hvceil.
assert (HvC : v + AREC * cap <= LD_CEIL) by (unfold LD_CEIL, AREC in *; lia).
assert (HPr : 4096 <= v + AREC * Z.of_nat i /\ v + AREC * Z.of_nat i + 8 <= LD_CEIL)
by (unfold AREC in *; lia).
assert (Hv8 : v mod 8 = 0).
{ pose proof (Z.div_mod v 16 ltac:(lia)) as D. rewrite Hv16, Z.add_0_r in D.
  rewrite D. replace (16 * (v / 16)) with ((2 * (v / 16)) * 8) by ring. apply Z_mod_mult. }
assert (HP8 : (v + AREC * Z.of_nat i) mod 8 = 0).
{ unfold AREC. rewrite Zplus_mod, Hv8.
  replace (16 * Z.of_nat i) with ((2 * Z.of_nat i) * 8) by ring. rewrite Z_mod_mult. reflexivity. }
(* the record's eight bytes are block bytes, so they are not image bytes; the head is *)
assert (DREC : v + AREC * Z.of_nat i + 8 <= LA \/ LA + 16 <= v + AREC * Z.of_nat i).
{ assert (NB : forall a, v + AREC * Z.of_nat i <= a < v + AREC * Z.of_nat i + 8 -> ~ in_img SEGS a).
  { intros a Ha. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) a HAR Hvin).
    rewrite Hreq0. unfold AREC in *. lia. }
  assert (IB : forall a, LA <= a < LA + 16 -> in_img SEGS a) by (intros a Ha; exact (proj1 (HG a (HLG a Ha)))).
  destruct (Z_le_gt_dec (v + AREC * Z.of_nat i + 8) LA) as [Hd|Hd]; [left; lia|].
  destruct (Z_le_gt_dec (LA + 16) (v + AREC * Z.of_nat i)) as [Hd2|Hd2]; [right; lia|].
  exfalso. destruct (Z_le_gt_dec LA (v + AREC * Z.of_nat i)) as [Hd3|Hd3].
  - exact (NB (v + AREC * Z.of_nat i) ltac:(lia) (IB (v + AREC * Z.of_nat i) ltac:(lia))).
  - exact (NB LA ltac:(lia) (IB LA ltac:(lia))). }
rewrite restrict_mkst_fx.
set (E := Eimg (Ereg regs (ldb_extra v n cap s_i))). pose proof pa_B_ok as HBASE.
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E8 : ew E 8 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 LA) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 (v + AREC * Z.of_nat i)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s_i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
{ intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
assert (HBx : U E ldb_Bx = SHADOW_OFF)
by (unfold ldb_Bx; rewrite (U_atom E 18 SB E18) by (unfold SB; lia); reflexivity).
split.
- unfold ss_ldb. apply pa_entry_st_ok_full.
+ assert (HLAd : 0 <= LA / 8 /\ LA / 8 <= 0x5fc000)
  by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (HSBd : 0 <= SB + LA / 8 < 2 ^ 64) by (unfold SB; lia).
  assert (HLAd2 : 0 <= LA / 8 < 2 ^ 64) by (unfold SB in HSBd; lia).
  unfold ldb_sr.
  apply regs_ok_pin; [| intros X; discriminate X | rewrite H21; reflexivity].
  apply regs_ok_pin; [| intros X; discriminate X |].
  2: { rewrite H20. apply bv_eq. fold (U E (SAlu ALU_ADD (SAlu ALU_SRL (SOff 9 0) (SLit 3)) (SOff 18 0))).
       rewrite !U_SAlu, (U_atom E 18 SB E18), (U_atom E 9 LA E9), U_lit by (unfold SB; lia). cbn [zalu_raw].
       change (Z.land 3 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. unfold zcanon, M64.
       rewrite (Z.mod_small (LA / 8)) by exact HLAd2.
       rewrite Z.mod_small by lia.
       rewrite unsigned_lit_small by exact HSBd. lia. }
  apply regs_ok_pin; [subst E; apply regs_ok_Eimg_Ereg | intros X; discriminate X |].
  rewrite H19. apply bv_eq. fold (U E (SAlu ALU_SLL (SOff 8 0) (SLit 4))).
  rewrite (ldU_o E 8 (Z.of_nat i) E8) by (unfold AREC in *; lia).
  rewrite unsigned_lit_small by (unfold AREC in *; lia). unfold AREC. lia.
+ vm_compute. reflexivity.
+ unfold ldb_regions, ld_lreg, ldb_rreg.
repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
* rewrite (VB 9%nat LA E9) by lia. split; [lia|]. split; [lia|].
split; [intros o Ho; apply (Mawr o ltac:(lia))|].
constructor; [|constructor; [|constructor; [|constructor]]].
-- apply (chunk_ok_val SEGS E _ LA 0 8 (SOff 32 0) v);
[cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold AREC in *; zside | zside |].
rewrite Z.add_0_r. exact Mv.
-- apply (chunk_ok_val SEGS E _ LA 8 4 (SOff 33 0) n);
[cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold AREC in *; zside | zside |]. exact Mn.
-- apply (chunk_ok_val SEGS E _ LA 12 4 (SOff 34 0) cap);
[cbn [sv_denot]; rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold AREC in *; zside | zside |]. exact Mc.
* rewrite (VB 10%nat (v + AREC * Z.of_nat i) E10) by (unfold LD_CEIL in *; lia).
split; [unfold AREC, LD_CEIL in *; lia|]. split; [unfold AREC, LD_CEIL in *; lia|]. split; [intros o Ho; lia|].
constructor; [|constructor].
apply (chunk_ok_val SEGS E _ (v + AREC * Z.of_nat i) 0 8 (SOff 35 0) s_i);
[cbn [sv_denot]; rewrite E35, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
rewrite Z.add_0_r. exact Ms.
+ apply pairwise_disjoint_of_extents. unfold ldb_regions, ld_lreg, ldb_rreg, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
rewrite (VB 9%nat LA E9) by lia. rewrite (VB 10%nat (v + AREC * Z.of_nat i) E10) by (unfold LD_CEIL in *; lia).
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
revert DREC. clear. intros. repeat split; lia.
+ split; [|split; [exact I | exact I]].
cbn [ldb_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hsin) as (_ & Hs4096 & Hsceil & _ & _ & _).
assert (HsC : s_i <= LD_CEIL) by (unfold req_size in Hsceil; destruct (_ =? 0); unfold LD_CEIL in *; lia).
rewrite E8, E9, E10, E18, E32, E33, E34, E35, !unsigned_lit_small by (unfold SB, LD_CEIL, AREC in *; lia).
change (2 ^ 3) with 8. change (2 ^ 4) with 16. rewrite !Z.pow_0_r, !Z.mod_1_r.
clear DREC.
revert HLAR HLA8 Hi Hn Hv4096 HvC HPr HP8 Hv16 HsR Hs4096 HsC.
unfold SB, LD_CEIL, AREC. clear. intros.
repeat match goal with |- _ /\ _ => split end; lia.
- unfold sh_ok, ldb_SH. constructor; [|constructor; [|constructor]].
+ apply (shent_ok_of_range SEGS (w_H W) memc _ ldb_Bx 9 LA 16 LA 0 16).
* exact (azs_range_addressable_x B ARx LAWS lyc Sc Hpc W memc mdc LA 16 HAR HZS).
* exact HBx.
* unfold U. cbn [sv_denot]. rewrite E9, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
* lia.
* lia.
* intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia.
+ eapply shent_ok_of_range.
* apply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 lyc Sc Hpc W memc mdc v (AREC * cap) (v + AREC * Z.of_nat i) 8 HAR Hvin);
  rewrite ?Hreq0; unfold AREC in *; lia.
* exact HBx.
* unfold U. cbn [sv_denot]. rewrite E10, Z.add_0_r, Z_to_bv_bv_unsigned.
  rewrite unsigned_lit_small by (unfold LD_CEIL in *; lia). reflexivity.
* lia.
* lia.
* intros x Hx. rewrite Hreq0 in Hvapp.
  unfold AREC, in_app, SHADOW_OFF, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. cbn in Hx.
  replace (Z.min 0 8) with 0 in Hx by reflexivity. replace (Z.max 0 8) with 8 in Hx by reflexivity. lia.
Qed.

(* ---- the body's post, at 0x85cb0 (the epilogue), over ARx: the journal is ajournal_gx_x, Hp after S and Hp'
   after S' ----
   At 0x85cb0 s0 = 16 i, s1 = l + 8, s2 = SB + (l+8)/8 (MEASURED on the symbolic state; s0 is reused for the memmove's
   destination offset, s1 / s2 for &l->n and its shadow byte), so they join the clobbered registers (LDB_CLOB);
   the epilogue reloads s0..s5 from the frame. *)
Definition ldb_post_x (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte)
(STK sp0 : Z) (FP : list (Z * Z)) ly S (Hp : list Z) W0 mem md own (lyc : alayout) (Sc : astate) (kk : Z)
(LA v n cap : Z) (i : nat) (s_i len_i : Z) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_ld_epi)) mem' (seg_rom SEGS)) md' /\
AJG STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' (kk + 1) /\
(forall r, reg_in r LDB_CLOB = false -> getr regs' r = getr regs r) /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (s_i, len_i + 1) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
frames S' = frames Sc /\ mo_le MT Sc S' (mo_free MT) /\ rp_RM RP S' kr /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - ASTACK <= a < spZ regs) ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 ~ (LA + 8 <= a < LA + 12) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall p m a, In (p, m) (ablocks B lyc Sc) -> p <= a < p + req_size m ->
 ~ (s_i <= a < s_i + req_size (len_i + 1)) -> ~ (v + AREC * Z.of_nat i <= a < v + AREC * (n - 1)) ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall k, 0 <= k < AREC * (n - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (v + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) memc (v + AREC * Z.of_nat i + AREC + k)) /\
val_mem SEGS (arm W' mem') (LA + 8) 4 (n - 1) /\ awr W' mem' LA 16 /\
apres_kept B W memc W' mem' /\
(* errno's four bytes (list_free calls list_drop in a loop and keeps errno's view across it) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) memc (as_errno B + j)).

(* the free of l->v[i].s, lifted from the allocator parameter's rule to the walk's journal *)

(* `~ in_wrange E rs a` for ss_ldb's regions: their one write window is the list head [LA, LA + 16) (the record
   cell's window is empty).  EQ: the env's register 9 is LA; Hout: a is off the head. *)
Ltac ld_nowr EQ Hout :=
let r := fresh "r" in let Hinr := fresh "Hinr" in let Hr := fresh "Hr" in
intros (r & Hinr & Hr); cbn [ss_mem ss_ldb ldb_regions In] in Hinr;
repeat match type of Hinr with
| _ \/ _ => destruct Hinr as [<- | Hinr];
  [ unfold ld_lreg, ldb_rreg in Hr; cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
    rewrite ?EQ in Hr; rewrite ?unsigned_lit_small in Hr by lia;
    apply Hout; clear - Hr; lia | ]
| False => destruct Hinr
end.


(* two live blocks at different addresses share no byte (ARx_blocks_law's pairwise disjointness) *)
Lemma ld_blk_disj_x : forall ly S Hp W mem md p1 n1 p2 n2 a,
ARx ly S Hp W mem md -> In (p1, n1) (ablocks B ly S) -> In (p2, n2) (ablocks B ly S) -> p1 <> p2 ->
p1 <= a < p1 + req_size n1 -> ~ (p2 <= a < p2 + req_size n2).
Proof.
intros ly S Hp W mem md p1 n1 p2 n2 a HAR H1 H2 Hne Ha Hb.
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md p1 n1 HAR H1) as (_ & _ & _ & _ & _ & Hpw).
pose proof (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ H1) as Hx. cbn [fst snd] in Hx.
pose proof (in_map (fun b : Z * Z => (fst b, req_size (snd b))) _ _ H2) as Hy. cbn [fst snd] in Hy.
assert (Hne2 : (p1, req_size n1) <> (p2, req_size n2)) by (intros E; injection E as E _; exact (Hne E)).
pose proof (pairwise_zdisjoint_split _ _ _ Hpw (in_split_2 _ _ _ Hx Hy Hne2)) as Hd.
unfold zdisjoint in Hd. cbn [fst snd] in Hd. lia.
Qed.

Ltac ldl := unfold LDROP_STK, LDROP_FRAME, ASTACK, AREC in *; lia.
Ltac ldz := cbn [Z.of_N N.to_nat Pos.to_nat Z.mul Pos.mul Pos.iter_op Nat.add Nat.mul]; ldl.
Ltac ld_awr_top Usp BV10 HLG :=
lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end;
apply awr_ok_x_cons_awr0; [awr_ok_tac; try (cbn [ew ewset Nat.eqb]; exact Usp)|];
apply awr_ok_x_cons_awr0; [awr_ok_tac|];
apply awr_ok_x_cons_awr0; [awr_ok_tac|];
apply awr_ok_x_cons_g; [|apply awr_ok_x_nil];
cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BV10;
let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply HLG; clear - Ha; lia.

(* list_drop(l, i) at 0x85b50: the prologue to 0x85bcc (the runner stops once, at the UBSan pointer-overflow check
   of &l->v[i], refuted by trap_ptr_sovf), the body (ld_bodyX_x: the free, the memmove, the store of n - 1) to 0x85cb0,
   the epilogue and the return; then the list at LA is ldrop_list l i (alist_at_drop). *)
(* the kit's spec at list_drop's B address, in MERGE.md (sha256 0694aca87ccd; internal record) step 2's form (A_list_dropP is BASE + AF_fr_list_drop) *)

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of each relation-dependent lemma above.  Each
   twin is its strict text with the journal and the step relation at R: ajournal_gx_x -> ajournal_gx_xR .. R,
   SRr SEGS -> SRrG SEGS R, the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG, W_kit.v paj_branch_xR), each carrier X_x -> its twin X_xR (R last), the journal lemmas their _xR
   forms, and each lemma name L -> LR; the relation-free helpers above are cited as they are.  The strict text is
   untouched. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Let RUNG := paj_run_x_xG B PST ARx LAWS R G HG 0 [].
Let RUNTOG := paj_run_to_x_xG B PST ARx LAWS R G HG 0 [].
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.
Let BRR := paj_branch_xR (PI := PI) (R := R).

(* writable_at survives a step that keeps presence, whatever the step does to the hidden set: a byte hidden after
   it reads as at a hidden or absent byte before it (YP09.v:136 wview's fallback); writable_kept_w without its wle
   premise, for the steps across a call at R, where the world relation is R, not wle *)
Lemma writable_kept_p : forall (W W' : world SEGS) (m m' : word -> option byte) a,
(apresent (w_H W) m a -> apresent (w_H W') m' a) ->
writable_at SEGS (mrestrict (w_H W) m) a -> writable_at SEGS (mrestrict (w_H W') m' ) a.
Proof.
intros W W' m m' a Hp Hw. unfold writable_at, wview, mrestrict in Hw |- *.
destruct (w_H W' (Z_to_bv 64 a)) eqn:EH'.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH; [exact Hw|].
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [|exact Hw].
  destruct (Hp (conj EH (ex_intro _ b Em))) as [HF _]. rewrite EH' in HF. discriminate HF.
- destruct (w_H W (Z_to_bv 64 a)) eqn:EH.
  + destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * destruct (Hp (conj EH (ex_intro _ b Em))) as [_ [b2 Hb2]]. rewrite Hb2. discriminate.
    * destruct (m' (Z_to_bv 64 a)); [discriminate | exact Hw].
Qed.
Lemma awr_kept_p : forall (W W' : world SEGS) m m' a nn,
(forall x, a <= x < a + nn -> apresent (w_H W) m x -> apresent (w_H W') m' x) ->
awr W m a nn -> awr W' m' a nn.
Proof.
intros W W' m m' a nn Hp H j Hj.
apply (writable_kept_p W W' m m' (a + j)); [intros Hx; exact (Hp (a + j) ltac:(lia) Hx) | exact (H j Hj)].
Qed.

Local Notation AJGR := (ajournal_gx_xR SEGS B PST ARx R G 0 []).
Definition ldb_post_xR (W : world SEGS) (regs : bvmap 5 word) (memc : word -> option byte)
(STK sp0 : Z) (FP : list (Z * Z)) ly S (Hp : list Z) W0 mem md own (lyc : alayout) (Sc : astate) (kk : Z)
(LA v n cap : Z) (i : nat) (s_i len_i : Z) (kr : nat) : world SEGS -> config -> Prop :=
fun W' c' => exists ly' S' Hp' regs' mem' md',
c' = mkCfg (mkst regs' (Z_to_bv 64 (BASE + A_ld_epi)) mem' (seg_rom SEGS)) md' /\
AJGR STK sp0 FP ly S Hp W0 mem md own ly' S' Hp' W' mem' md' (kk + 1) /\
(forall r, reg_in r LDB_CLOB = false -> getr regs' r = getr regs r) /\
(exists l1 l2, ablocks B lyc Sc = l1 ++ (s_i, len_i + 1) :: l2 /\ ablocks B ly' S' = l1 ++ l2) /\
frames S' = frames Sc /\ mo_le MT Sc S' (mo_free MT) /\ rp_RM RP S' kr /\
(forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (spZ regs - ASTACK <= a < spZ regs) ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall a, in_img SEGS a -> ~ Exists (in_zr a) (as_owned_static B) -> ~ (as_errno B <= a < as_errno B + 4) ->
 ~ (LA + 8 <= a < LA + 12) -> aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall p m a, In (p, m) (ablocks B lyc Sc) -> p <= a < p + req_size m ->
 ~ (s_i <= a < s_i + req_size (len_i + 1)) -> ~ (v + AREC * Z.of_nat i <= a < v + AREC * (n - 1)) ->
 aview SEGS (w_H W') mem' a = aview SEGS (w_H W) memc a) /\
(forall k, 0 <= k < AREC * (n - 1 - Z.of_nat i) ->
 aview SEGS (w_H W') mem' (v + AREC * Z.of_nat i + k) =
 aview SEGS (w_H W) memc (v + AREC * Z.of_nat i + AREC + k)) /\
val_mem SEGS (arm W' mem') (LA + 8) 4 (n - 1) /\ awr W' mem' LA 16 /\
apres_kept B W memc W' mem' /\
(* errno's four bytes (list_free calls list_drop in a loop and keeps errno's view across it) *)
(forall j, 0 <= j < 4 -> aview SEGS (w_H W') mem' (as_errno B + j) = aview SEGS (w_H W) memc (as_errno B + j)).

Lemma aj_free_gx_xR : forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa nb (o : Z) raw ch (kr : nat),
AJGR STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall j, 0 <= j < req_size nb -> inFP FP (pa + j)) ->
mo_ok MT Sc (mo_free MT) ->
SRrG SEGS R W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJGR STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 ((forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) memT (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) -> ~ (pa <= a < pa + req_size nb) ->
   apresent (w_H W) memT a -> apresent (w_H W2) mem2 a))).
Proof.
intros W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa nb o raw ch kr
HJ Hin Ha0 Hsp Hal Hneg Hbud Hgp Htp Hra Hraw Hch HCX HRM HCNT Hfp Hmo.
pose proof HJ as (HSTK & _ & (memS & HJi & Hag) & Hout).
rewrite !Z.add_0_r in HJi.
(* the allocator engine's stack room below the call (the rule's ACALL_PREFIX premise), from the journal *)
pose proof (aj_stack_room_xR SEGS B PST ARx STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc W memT mdc k o regsT HJi Hsp Hbud)
  as Hroom.
(* the call-boundary premise RO of the R rule, from the journal's ARx at the call state *)
pose proof (RO_ARx _ _ _ _ _ _ (proj1 HJi)) as HRO.
eapply SRrG_mono.
{ exact (AFREE_R W regsT memT STK sp0 FP ly S Hp W0 memS md own lyc Sc Hpc mdc k pa nb o raw ch kr
  HJi Hin Ha0 Hsp Hal Hneg Hbud Hroom Hgp Htp Hra Hraw Hch HRO HCX HRM HCNT Hfp Hmo). }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs & HK & Hle & HRM2 & Hpr).
exists ly2, S2, Hp2, regs2, mem2, md2. split; [reflexivity|].
split; [|split; [exact HP2 | split; [exact Hbl | split; [exact Hfrs | split; [exact HK | split; [exact Hle |
  split; [exact HRM2 | exact Hpr]]]]]]].
apply (ajournal_gx_pack_xR SEGS B PST ARx G 0 [] STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) memS);
[lia | lia | rewrite !Z.add_0_r; exact HJ2 | exact Hag | intros a Ha; lia].
Qed.

Lemma ld_bodyX_xR : forall W regs memc mdc sp0 FP ly S Hp W0 mem md own lyc Sc Hpc kk
LA v n cap (i : nat) s_i len_i raw (kr : nat),
AJGR LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc kk ->
spZ regs = sp0 - LDROP_FRAME ->
getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 (Z.of_nat i) -> getr regs 9 = w64 LA ->
getr regs 10 = w64 (v + AREC * Z.of_nat i) ->
getr regs 18 = w64 SB -> getr regs 19 = w64 (AREC * Z.of_nat i) -> getr regs 20 = w64 (SB + LA / 8) ->
getr regs 21 = w64 0 ->
0 <= Z.of_nat i < n -> n <= cap < 2 ^ 30 ->
LA mod 8 = 0 -> (forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
val_mem SEGS (arm W memc) LA 8 v -> val_mem SEGS (arm W memc) (LA + 8) 4 n ->
val_mem SEGS (arm W memc) (LA + 12) 4 cap -> awr W memc LA 16 ->
val_mem SEGS (arm W memc) (v + AREC * Z.of_nat i) 8 s_i -> 0 <= s_i < 2 ^ 64 ->
In (v, AREC * cap) (ablocks B lyc Sc) -> In (s_i, len_i + 1) (ablocks B lyc Sc) -> 0 <= len_i -> v <> s_i ->
(In (s_i, len_i + 1) (ablocks B ly S) -> forall j, 0 <= j < req_size (len_i + 1) -> inFP FP (s_i + j)) ->
(forall a, v <= a < v + AREC * cap -> inFP FP a) ->
(* the bytes the memmove moves (the intrinsic's n < 2^32): the kit's ldrop_spec premise, W_contract.v *)
AREC * (n - 1 - Z.of_nat i) < 2 ^ 32 ->
mo_ok MT Sc (mo_free MT) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
rom_view SEGS W memc ->
SRrG SEGS R W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_ld_body)) memc (seg_rom SEGS)) mdc)
(ldb_post_xR W regs memc LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc kk LA v n cap i s_i len_i kr).
Proof.
intros W regs memc mdc sp0 FP ly S Hp W0 mem md own lyc Sc Hpc kk LA v n cap i s_i len_i raw kr
HJ Hsp H1 Hraw Hra4 H3 H4 H8 H9 H10 H18 H19 H20 H21 Hi Hn HLA8 HLG HZS Mv Mn Mc Mawr Ms HsR Hvin Hsin Hlen Hvne
Hfp HvFP Hmv32 Hmo HRM HCNT Hrom.
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
(* paj_run_tok_x's generated names shadow the Section's HG (gx_ok); keep a copy under a name it cannot take *)
pose proof HG as HGok.
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc kk HJ) as HAR.
pose proof HJ as (_ & _ & (memS0 & HJi0 & _) & _). rewrite !Z.add_0_r in HJi0.
pose proof HJi0 as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop2 & Htop).
pose proof (ld_LA_range LA HLG) as HLAR.
destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & Hvapp & _ & _).
assert (Hvreq : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Hvreq in Hvceil, Hvapp.
(* the bounds the trap refutations below read, with the constants spelled out for lia *)
assert (HIB : 0 <= Z.of_nat i /\ Z.of_nat i + 1 <= n /\ n <= cap /\ cap < 2 ^ 30) by lia.
assert (HVB : 4096 <= v /\ v + 16 * cap <= 140737486618624) by (unfold AREC in *; lia).
destruct (ldb_entry_x W regs memc lyc Sc Hpc mdc LA v n cap i s_i len_i HAR H8 H9 H10 H18 H19 H20 H21 Hi Hn HLA8 HLG HZS
Mv Mn Mc Mawr Ms HsR Hvin Hsin Hlen) as [HS SHOK].
remember (Eimg (Ereg regs (ldb_extra v n cap s_i))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ldb_extra v n cap s_i)) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E1 : ew E 1 = raw) by (rewrite (EE 1%nat 1%bv eq_refl); exact H1).
assert (E2 : ew E 2 = getr regs 2) by (exact (EE 2%nat 2%bv eq_refl)).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact H3).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact H4).
assert (E8 : ew E 8 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 8%nat 8%bv eq_refl); exact H8).
assert (E9 : ew E 9 = Z_to_bv 64 LA) by (rewrite (EE 9%nat 9%bv eq_refl); exact H9).
assert (E10 : ew E 10 = Z_to_bv 64 (v + AREC * Z.of_nat i)) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E18 : ew E 18 = Z_to_bv 64 SB) by (rewrite (EE 18%nat 18%bv eq_refl); exact H18).
assert (E32 : ew E 32 = Z_to_bv 64 v) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 n) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 s_i) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE.
unfold A_ld_body.
(* ---- 0x85bcc .. the free call 0x85be8: the runner decides the alignment and shadow checks of &l->v[i] ---- *)
paj_run_tok_xR RUNG HS HJ SHOK ld_Bspan.
{ assert (BV9 : base_val E (Some 9%nat) = LA)
  by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; pose proof (ld_LA_range LA HLG); lia).
  apply awr_ok_x_cons_g.
  { unfold ld_lreg. cbn [YP09.r_base YP09.r_wlo YP09.r_whi]. rewrite BV9. intros a Ha. apply HLG. lia. }
  apply awr_ok_x_cons; [unfold ldb_rreg; cbn [YP09.r_base YP09.r_wlo YP09.r_whi]; intros a Ha; lia
  | apply awr_ok_x_nil]. }
ld_names msF HFrF HGF.
(* the run to the free wrote nothing off the list head *)
assert (HEAD : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) (ms_mem msF) a = aview SEGS (w_H W) memc a).
{ intros a Ha Hout. lazymatch type of HFrF with frame_of ?Ev ?rs _ _ =>
    rewrite (aview_kept_out Ev rs (w_H W) memc (ms_mem msF) HFrF a Ha); [reflexivity | ld_nowr E9 Hout] end. }
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (10%bv : bv 5) Q10.
rewrite HBfree.
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_free_gx_xR W _ _ LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc _ kk s_i (len_i + 1)
  (- LDROP_FRAME) (Z_to_bv 64 (BASE + 14504)) [] kr HJ Hsin)   (* 14504 = 0x38a8 = AF_fr_list_drop + 0x9c, 0x85bec *).
- rewrite Q10, E35. reflexivity.
- unfold spZ in Hsp |- *. rewrite Q2, E2. unfold LDROP_FRAME in *. lia.
- reflexivity.
- unfold LDROP_FRAME; lia.
- unfold LDROP_STK, LDROP_FRAME, ASTACK; lia.
- rewrite Q3, E3. reflexivity.
- rewrite Q4, E4. reflexivity.
- exact Q1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- eapply (achain_chain_pre lyc _ (spZ regs) (Z.of_nat i) []).
  + apply achain_low. lia.
  + unfold spZ in *. rewrite Q2, E2. unfold LDROP_STK, LDROP_FRAME, ASTACK in *. lia.
  + unfold s0Z. rewrite Q8, E8. apply unsigned_lit_small. lia.
  + unfold raZ. rewrite Q1. rewrite unsigned_lit_small by lia. lia.
- (* the free's caller context: the chain is [] (s0 = 16 i), the trace the singleton [list_drop + 0x9c] *)
  cbn [spine map]. lazymatch goal with |- In [raZ ?r] _ =>
    replace (raZ r) with (BASE + AF_fr_list_drop + 0x9c); [exact HCTX_ld_free|] end.
  unfold raZ. rewrite Q1, unsigned_lit_small by lia. first [lia | unfold AF_fr_list_drop in *; lia].
- exact HRM.
- exact HCNT.
- exact Hfp.
- exact Hmo. }
cbv beta. intros W2 c2 Hwle2 (ly2 & S2 & Hp2 & regs2 & mem2 & md2 & -> & HJ2 & HP2 & Hbl & Hfrs2 & HK & Hle & HRM2 & Hpres).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LDROP_STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (kk + 1) HJ2) as HAR2.
destruct Hpres as (Herr2 & Hpres2).
(* the list head: an image byte of G, so the free kept its view, its presence and its writability *)
assert (GIMG : forall a, LA <= a < LA + 16 -> in_img SEGS a /\ ~ Exists (in_zr a) (as_owned_static B) /\
~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha. split; [exact (proj1 (HG a (HLG a Ha)))|]. split; [exact (proj1 (proj2 (HG a (HLG a Ha))))|].
  exact (proj1 (GRT a (HLG a Ha))). }
assert (GOWN : forall a, LA <= a < LA + 16 -> ~ aowned B lyc Sc a /\ ~ aowned B ly2 S2 a).
{ intros a Ha. destruct (GIMG a Ha) as (Himg & Hno & _). split; intros Ho.
  - exact (Hno (proj1 (alx_owned_image _ _ _ LAWS lyc Sc Hpc W memc mdc a HAR Himg) Ho)).
  - exact (Hno (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 a HAR2 Himg) Ho)). }
assert (GNB : forall a, LA <= a < LA + 16 -> ~ (s_i <= a < s_i + req_size (len_i + 1))).
{ intros a Ha Hr. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc s_i (len_i + 1) a HAR Hsin Hr (proj1 (GIMG a Ha))). }
assert (GKEEP : forall a, LA <= a < LA + 16 -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W) (ms_mem msF) a).
{ intros a Ha. destruct (GIMG a Ha) as (Himg & Hno & He).
  exact (proj1 (proj2 (proj2 HK)) a Himg Hno He). }
assert (GPRES : forall a, LA <= a < LA + 16 -> apresent (w_H W) (ms_mem msF) a -> apresent (w_H W2) mem2 a).
{ intros a Ha Hpa. destruct (GIMG a Ha) as (Himg & _ & He). destruct (GOWN a Ha) as (Ho1 & Ho2).
  exact (Hpres2 a Himg Ho1 Ho2 He (GNB a Ha) Hpa). }
jafter_call_keep_pi HS 36%nat regs2 (mrestrict (w_H W2) mem2) HP2 [0]%nat HS2.
match type of HS2 with ?t -> _ => assert (HRK : t); [|specialize (HS2 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  unfold ld_lreg. split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite E9;
  rewrite unsigned_lit_small by lia.
  - intros a Ha. apply (mbyte_of_aview SEGS). apply GKEEP. lia.
  - intros a Ha Hw. apply (writable_kept_p W W2 (ms_mem msF) mem2 a); [| exact Hw].
    intros Hpa. apply GPRES; [lia | exact Hpa]. }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0)
by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (HAEa : env_agree 32 (Ereg regs (ldb_extra v n cap s_i)) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (F9 : ew Ea 9 = Z_to_bv 64 LA) by (rewrite OLDa by (cbv; lia); exact E9).
assert (F8 : ew Ea 8 = Z_to_bv 64 (Z.of_nat i)) by (rewrite OLDa by (cbv; lia); exact E8).
assert (F18 : ew Ea 18 = Z_to_bv 64 SB) by (rewrite OLDa by (cbv; lia); exact E18).
assert (F32 : ew Ea 32 = Z_to_bv 64 v) by (rewrite OLDa by (cbv; lia); exact E32).
assert (F33 : ew Ea 33 = Z_to_bv 64 n) by (rewrite OLDa by (cbv; lia); exact E33).
assert (F34 : ew Ea 34 = Z_to_bv 64 cap) by (rewrite OLDa by (cbv; lia); exact E34).
assert (F2 : ew Ea 2 = getr regs 2) by (rewrite OLDa by (cbv; lia); exact E2).
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite F2; reflexivity).
assert (U9a : bv_unsigned (ew Ea 9) = LA) by (rewrite F9; apply unsigned_lit_small; lia).
assert (BV9a : base_val Ea (Some 9%nat) = LA) by (cbn [base_val]; exact U9a).
assert (SHOK2 : sh_ok SEGS ldb_Bx ldb_SH2 Ea (mrestrict (w_H W2) mem2)).
{ unfold sh_ok, ldb_SH2. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem2 _ ldb_Bx 9 LA 16 LA 0 16).
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem2 md2 LA 16 HAR2 HZS).
  - unfold ldb_Bx. rewrite (U_atom Ea 18 SB F18) by (unfold SB; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite F9, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia. }
(* ---- 0x85bec .. the memmove call 0x85c8c: the runner stops at four UBSan checks it cannot decide (MEASURED);
   each is refuted by its lib/B/W_traps.v shape lemma.  The runs write nothing (KQ: no byte off the head moves). ---- *)
assert (KQ : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) -> aview SEGS (w_H W2) mem2 a = aview SEGS (w_H W2) mem2 a)
by (intros; reflexivity).
assert (PQ : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) mem2 x) by (intros x Hx; exact Hx).
paj_run_tok_xR RUNG HS HJ2 SHOK2 ld_Bspan. { ld_awr9 BV9a HLG. }
ld_fold9 LA U9a KQ PQ.
(* 0x85c14 beqz: the pointer-overflow check of &l->v[i] = v + 16 i (trap_ptr_sovf: i >= 0, v + 16 i >= 16 i) *)
psrr_branch_tok RUNG BRR HS SHOK2 ld_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = true |- _ =>
  assert (G8 : ew Ev 8 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact F8);
  assert (G32 : ew Ev 32 = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; exact F32);
  rewrite (trap_ptr_sovf Ev (SLit 0) _ 0 (U_lit Ev 0 ltac:(lia))
    (trap_U_sltu_ge Ev _ _ (16 * Z.of_nat i) (16 * Z.of_nat i + v)
      (ldU_o Ev 8 (Z.of_nat i) G8 ltac:(clear - HIB HVB; lia))
      (ldU_p Ev 8 (Z.of_nat i) v G8 G32 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
      ltac:(clear - HIB HVB; lia))) in Hc; discriminate Hc end. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 ld_Bspan. { ld_awr9 BV9a HLG. }
ld_fold9 LA U9a KQ PQ.
(* 0x85c40 beqz: the pointer-overflow check of &l->v[i+1] = v + 16 (i+1) (trap_ptr_sovf: i + 1 >= 0, against v) *)
psrr_branch_tok RUNG BRR HS SHOK2 ld_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = true |- _ =>
  assert (G8 : ew Ev 8 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact F8);
  assert (G32 : ew Ev 32 = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; exact F32);
  rewrite (trap_ptr_sovf Ev _ (SLit 0) 0
    (trap_U_sltu_ge Ev (SOff 32 0) _ v (16 * Z.of_nat i + 16 + v) (U_atom Ev 32 v G32 ltac:(clear - HIB HVB; lia))
      (ldU_p1 Ev 8 (Z.of_nat i) v G8 G32 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
      ltac:(clear - HIB HVB; lia))
    (U_lit Ev 0 ltac:(lia))) in Hc; discriminate Hc end. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 ld_Bspan. { ld_awr9 BV9a HLG. }
ld_fold9 LA U9a KQ PQ.
(* 0x85c70 bge: the int32 check of (n - i) - 1 (trap_decw_sext: 0 < n - i < 2^31) *)
psrr_branch_tok RUNG BRR HS SHOK2 ld_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken BC_GE (sv_denot ?Ev (SAluw ALU_ADD ?X (SLit (-1)))) _ = true |- _ =>
  assert (G8 : ew Ev 8 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact F8);
  assert (G33 : ew Ev 33 = Z_to_bv 64 n) by (cbn [ew ewset Nat.eqb]; exact F33);
  rewrite (trap_decw_sext Ev X (n - Z.of_nat i)
    (ldS_of_U Ev X (n - Z.of_nat i) (ldU_x Ev 8 (Z.of_nat i) n G8 G33 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
      ltac:(clear - HIB HVB; lia))
    ltac:(clear - HIB HVB; lia)) in Hc; discriminate Hc end. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 ld_Bspan. { ld_awr9 BV9a HLG. }
ld_fold9 LA U9a KQ PQ.
(* 0x85c84 bnez: the memmove operands' 8-alignment (trap_align8_pair: v + 16 i, v + 16 (i+1), v 16-aligned) *)
psrr_branch_tok RUNG BRR HS SHOK2 ld_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = true |- _ =>
  assert (G8 : ew Ev 8 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact F8);
  assert (G32 : ew Ev 32 = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; exact F32);
  rewrite (trap_align8_pair Ev _ _ (16 * Z.of_nat i + v) (16 * Z.of_nat i + 16 + v)
    (ldU_p Ev 8 (Z.of_nat i) v G8 G32 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
    (ldU_p1 Ev 8 (Z.of_nat i) v G8 G32 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
    (ld_mod8 v (Z.of_nat i) Hv16) (ld_mod8b v (Z.of_nat i) Hv16)) in Hc; discriminate Hc end. }
paj_run_tok_xR RUNG HS HJ2 SHOK2 ld_Bspan. { ld_awr9 BV9a HLG. }
ld_fold9 LA U9a KQ PQ.
ld_name_ms msM.
repeat match goal with Hx : branch_taken _ _ _ = false |- _ => clear Hx end.
pmkst HS.
prreg HS (1%bv : bv 5) P1. prreg HS (2%bv : bv 5) P2. prreg HS (3%bv : bv 5) P3.
prreg HS (4%bv : bv 5) P4. prreg HS (10%bv : bv 5) P10. prreg HS (11%bv : bv 5) P11.
prreg_u HS (12%bv : bv 5) P12.
(* the memmove's three arguments *)
assert (R10 : getr (ms_regs msM) 10 = w64 (v + AREC * Z.of_nat i)).
{ rewrite P10, F8, F32, ld_addr_eq by (unfold AREC, LD_CEIL in *; lia). unfold w64, AREC. f_equal; lia. }
assert (R11 : getr (ms_regs msM) 11 = w64 (v + AREC * Z.of_nat i + AREC)).
{ rewrite P11, F8, F32, ld_sll4 by lia. rewrite !YI08.alu64_add_lit. unfold w64, AREC. f_equal; lia. }
assert (R12 : getr (ms_regs msM) 12 = w64 (AREC * (n - 1 - Z.of_nat i))).
{ lazymatch type of P12 with _ = Z_to_bv 64 (U ?Ev _) =>
  assert (G8 : ew Ev 8 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact F8);
  assert (G33 : ew Ev 33 = Z_to_bv 64 n) by (cbn [ew ewset Nat.eqb]; exact F33);
  rewrite (ldU_count Ev 8 (Z.of_nat i) n G8 G33 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia)) in P12 end.
  rewrite P12. unfold w64, AREC. f_equal; lia. }
(* the vector is still live after the free, and the moved range sits inside it *)
assert (Hvin2 : In (v, AREC * cap) (ablocks B ly2 S2)).
{ destruct Hbl as (l1 & l2 & Eb1 & Eb2). rewrite Eb2. rewrite Eb1 in Hvin.
  apply in_app_or in Hvin as [Hx | [Hx | Hx]]; apply in_or_app; [left; exact Hx | | right; exact Hx].
  exfalso. injection Hx as Ex _. exact (Hvne (eq_sym Ex)). }
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LDROP_STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 (ms_mem msM) _ (kk + 1) HJ2) as HAR3.
destruct (alx_blocks _ _ _ LAWS ly2 S2 Hp2 W2 (ms_mem msM) _ _ _ HAR3 Hvin2) as (V16 & V4096 & Vceil & Vapp & Vpres & _).
assert (Vreq : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Vreq in Vceil, Vapp, Vpres.
assert (Uspm : spZ (ms_regs msM) = sp0 - LDROP_FRAME)
by (unfold spZ in *; rewrite P2, F2; lia).
assert (Hstkhi : alloc_ceiling + LDROP_STK <= sp0) by lia.
(* rom_view at the call: the runs wrote only the list head, which is in G; the free kept image bytes outside the
   allocator's statics and errno, and the statics' read-only bytes are AR's pinned const cells (ROMS) *)
assert (Hrom2 : rom_view SEGS W2 (ms_mem msM)).
{ intros a Hin. destruct (ROMS a Hin) as (Hpin & Herr & HnG).
  assert (Hd : forall r, {in_zr a r} + {~ in_zr a r}).
  { intros r. unfold in_zr. destruct (Z_le_gt_dec (fst r) a); destruct (Z_lt_ge_dec a (fst r + snd r));
    [left; lia | right; lia | right; lia | right; lia]. }
  destruct (Exists_dec (in_zr a) (as_owned_static B) Hd) as [Hown | Hos].
  { exact (rom_pinned_view_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem msM) _ a HAR3 (Hpin Hown)). }
  assert (Himg : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg) as Har.
  assert (Hout : ~ (LA <= a < LA + 16)) by (intros Hl; apply HnG; apply HLG; lia).
  rewrite (KQ a ltac:(lia) Hout).
  rewrite (proj1 (proj2 (proj2 HK)) a Himg Hos Herr).
  rewrite (HEAD a ltac:(lia) Hout).
  exact (Hrom a Hin). }
(* ---- the memmove of the records above i, 0x85c8c ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ eapply (aj_gx_entry_at_xR B PST ARx LAWS R_trans WLE_R G 0 [] ESTACK (SIGMA WS_asan_memmove)
  (fun a => v + AREC * Z.of_nat i <= a < v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i)) _
  W2 (ms_regs msM) (ms_mem msM) LDROP_STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 _ (kk + 1)
  (- LDROP_FRAME) (Z_to_bv 64 (BASE + 14668)) HGok eq_refl HJ2)   (* 14668 = 0x394c = AF_fr_list_drop + 0x140, 0x85c90 *).
- unfold LDROP_FRAME in *; lia.
- reflexivity.
- unfold LDROP_FRAME; lia.
- lia.
- unfold LDROP_STK, LDROP_FRAME, ESTACK, ASTACK; lia.
- rewrite P3. rewrite OLDa by (cbv; lia). exact E3.
- rewrite P4. rewrite OLDa by (cbv; lia). exact E4.
- exact P1.
- apply ret_ok_codeptr_v; [lia | reflexivity].
- intros a. destruct (Z_le_gt_dec (v + AREC * Z.of_nat i) a) as [Hd1|Hd1]; [|right; lia].
  destruct (Z_lt_ge_dec a (v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i))) as [Hd2|Hd2];
  [left; lia | right; lia].
- intros a Ha HGa. exfalso.
  apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap) a HAR3 Hvin2);
  [rewrite Vreq; unfold AREC in *; lia | exact (proj1 (HGok a HGa))].
- intros a Ha HnG. split; [|lia]. right; left.
  split; [apply HvFP; unfold AREC in *; lia|].
  exists v, (AREC * cap). split; [exact Hvin2 | rewrite Vreq; unfold AREC in *; lia].
- intros HPRE HSC.
  apply (AMOVE ly2 S2 Hp2 W2 (ms_regs msM) (ms_mem msM) _
    (v + AREC * Z.of_nat i) (v + AREC * Z.of_nat i + AREC) (AREC * (n - 1 - Z.of_nat i)) HPRE R10 R11 R12).
  + unfold AREC in *; lia.
  + unfold AREC in *; lia.
  + unfold AREC in *; lia.
  + intros a Ha. split; [|split].
    * apply (apresent_writable SEGS). exact (proj1 (Vpres a ltac:(unfold AREC in *; lia))).
    * exact (proj2 (Vpres a ltac:(unfold AREC in *; lia))).
    * rewrite Uspm. unfold AREC, ESTACK, LDROP_STK, LDROP_FRAME, ASTACK in *.
      lia.
  + unfold amem_range, in_app, app_addr, zone2, off_img, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite Vreq; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite Vreq; unfold AREC in *; lia | exact Hpos].
  + unfold AREC in *; lia.
  + unfold AREC in *; lia.
  + intros a Ha. split.
    * destruct (proj1 (Vpres a ltac:(unfold AREC in *; lia))) as [Hh [b Hb]].
      unfold aview, mbyte, mrestrict. rewrite Hh, Hb. discriminate.
    * rewrite Uspm. unfold AREC, ESTACK, LDROP_STK, LDROP_FRAME, ASTACK in *.
      lia.
  + unfold amem_range, in_app, app_addr, zone2, off_img, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *. lia.
  + eapply (range_addressable_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite Vreq; unfold AREC in *; lia].
  + intros Hpos. eapply (shadow_hull_vis_of_block_hp0_x SEGS B ARx LAWS HP0 ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap));
    [exact HAR3 | exact Hvin2 | unfold AREC in *; lia | rewrite Vreq; unfold AREC in *; lia | exact Hpos].
  + exact Hrom2.
  + intros Hpos. split;
    unfold amem_range, in_app, app_addr, zone2, off_img, kLowShadowBeg, kLowMemEnd, kHighMemBeg, kHighMemEnd, ASAN_CEIL, AREC in *; lia.
  + (* the destination is vector-block bytes, so no image byte *)
    intros a Ha. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap) a HAR3 Hvin2).
    rewrite Vreq. unfold AREC in *. lia. }
cbv beta. intros W3 c3 Hwle3 (-> & regs3 & mem3 & md3 & -> & HJ3 & HP3 & (Hres3 & Hmov) & Hfr3 & Hpres3).
(* the head is an image byte, so the memmove (which writes only inside the vector block) kept it *)
assert (GOFFM : forall a, LA <= a < LA + 16 ->
~ (v + AREC * Z.of_nat i <= a < v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i))).
{ intros a Ha Hr. apply (blk_img_x SEGS B ARx LAWS ly2 S2 Hp2 W2 (ms_mem msM) _ v (AREC * cap) a HAR3 Hvin2);
  [rewrite Vreq; unfold AREC in *; lia | exact (proj1 (GIMG a Ha))]. }
assert (GLOW : forall a, LA <= a < LA + 16 -> 0 <= a < 2 ^ 64 /\ ~ (sp0 - LDROP_FRAME - ESTACK <= a < sp0 - LDROP_FRAME)).
{ intros a Ha. pose proof (pa_img_range a (proj1 (GIMG a Ha))) as Har.
  unfold LDROP_FRAME, ESTACK, LDROP_STK, ASTACK in *. lia. }
jafter_call_keep_pi HS 52%nat regs3 (mrestrict (w_H W2) mem3) HP3 [0]%nat HS3.
match type of HS3 with ?t -> _ => assert (HRK : t); [|specialize (HS3 HRK); clear HRK] end.
{ cbn [ms_mem restrict]. repeat apply Forall_cons; [| apply Forall_nil].
  split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite U9a.
  - intros a Ha. apply (mbyte_of_aview SEGS).
    apply Hfr3; [apply (proj1 (GLOW a ltac:(lia))) | apply GOFFM; lia
    | intros Hc; apply (proj2 (GLOW a ltac:(lia))); lia].
  - intros a Ha Hw. apply (writable_kept_p W2 W2 (ms_mem msM) mem3 a);
    [intros Hpa; exact (Hpres3 a Hpa) | exact Hw]. }
clear HS. rewrite <- restrict_mkst_fx in HS3. rename HS3 into HS.
remember (havoc Ea 52 (map (getr regs3) CLOB)) as Eb eqn:HEb in HS.
assert (HEIb : img_env VAL A_LIM Eb) by (rewrite HEb; apply img_env_havoc; [exact HEIa | cbv; lia]).
assert (OLDb : forall m0, (m0 < 52)%nat -> ew Eb m0 = ew Ea m0)
by (intros m0 Hm0; rewrite HEb; apply YN3v.ew_havoc_old; exact Hm0).
assert (HAEb : env_agree 32 (Ereg regs (ldb_extra v n cap s_i)) Eb)
by (rewrite HEb; apply env_agree_havoc_ge; [cbv; lia | exact HAEa]).
clear HEb.
assert (K9 : ew Eb 9 = Z_to_bv 64 LA) by (rewrite OLDb by (cbv; lia); exact F9).
assert (K18 : ew Eb 18 = Z_to_bv 64 SB) by (rewrite OLDb by (cbv; lia); exact F18).
assert (K33 : ew Eb 33 = Z_to_bv 64 n) by (rewrite OLDb by (cbv; lia); exact F33).
assert (K2 : ew Eb 2 = getr regs 2) by (rewrite OLDb by (cbv; lia); exact F2).
assert (U9b : bv_unsigned (ew Eb 9) = LA) by (rewrite K9; apply unsigned_lit_small; lia).
assert (BV9b : base_val Eb (Some 9%nat) = LA) by (cbn [base_val]; exact U9b).
pose proof (ajournal_gx_AR_xR SEGS B PST ARx G 0 [] LDROP_STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem3 md3 (kk + 1) HJ3) as HAR4.
assert (SHOK3 : sh_ok SEGS ldb_Bx ldb_SH2 Eb (mrestrict (w_H W2) mem3)).
{ unfold sh_ok, ldb_SH2. constructor; [|constructor].
  apply (shent_ok_of_range SEGS (w_H W2) mem3 _ ldb_Bx 9 LA 16 LA 0 16).
  - exact (azs_range_addressable_x B ARx LAWS ly2 S2 Hp2 W2 mem3 md3 LA 16 HAR4 HZS).
  - unfold ldb_Bx. rewrite (U_atom Eb 18 SB K18) by (unfold SB; lia). reflexivity.
  - unfold U. cbn [sv_denot]. rewrite K9, Z.add_0_r, Z_to_bv_bv_unsigned. rewrite unsigned_lit_small by lia. reflexivity.
  - lia.
  - lia.
  - intros x Hx. unfold SHADOW_OFF. cbn in Hx. lia. }
(* ---- the store of n - 1 into l->n, 0x85c90 .. 0x85cac: the runner decides the int32 check of n - 1 (n >= 1) ---- *)
paj_run_to_tok_xR RUNTOG HS HJ3 SHOK3 ld_Bspan A_ld_epi. { ld_awr9 BV9b HLG. }
ld_names msE HFrE HGE.
(* at 0x85cb0 the list region's n-cell is CVal 4 (SOff 33 (-1)), i.e. n - 1 (MEASURED, vm_compute) *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok _ ltac:(cbn [ss_mem]; left; reflexivity)) as (_ & _ & _ & Hchs).
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 8 (CVal 4%N (SOff 33 (-1))))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch8.
assert (MNEW : val_mem SEGS (mrestrict (w_H W2) (ms_mem msE)) (LA + 8) 4 (n - 1)).
{ replace (LA + 8) with (base_val Eb (Some 9%nat) + 8)
  by (cbn [base_val]; rewrite K9, unsigned_lit_small by lia; lia).
  apply (val_mem_of_chunk4 Eb _ _ 8 (SOff 33 (-1)) (n - 1) Hch8); [|lia].
  rewrite (U_atom_off Eb 33 n (-1) K33) by lia. lia. }
(* ---------------------------------------------------------------- (3) the post at 0x85cb0 *)
pose proof (st_ok_pi_restrict_mkst _ _ _ _ HS eq_refl) as EMS. cbn [ss_pc] in EMS.
assert (QF : LDROP_FRAME = 64) by reflexivity. assert (QA : ASTACK = 16384) by reflexivity.
assert (QE : ESTACK = 4096) by reflexivity. assert (QS : LDROP_STK = 16448) by reflexivity.
assert (K32 : ew Eb 32 = Z_to_bv 64 v) by (rewrite OLDb by (cbv; lia); exact F32).
assert (K34 : ew Eb 34 = Z_to_bv 64 cap) by (rewrite OLDb by (cbv; lia); exact F34).
(* the head's two kept cells, read off the final state, and as the caller handed them over *)
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 0 (CVal 8%N (SOff 32 0)))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch0.
pose proof (proj1 (Forall_forall _ _) Hchs (YP09.mkChunk 12 (CVal 4%N (SOff 34 0)))
  ltac:(cbn [YP09.r_chunks In]; tauto)) as Hch12.
assert (V0F : val_mem SEGS (mrestrict (w_H W2) (ms_mem msE)) LA 8 v).
{ replace LA with (base_val Eb (Some 9%nat) + 0) by (cbn [base_val]; rewrite K9, unsigned_lit_small by lia; lia).
  apply (val_mem_of_chunk8 Eb _ _ 0 (SOff 32 0) v Hch0); [|unfold AREC in *; lia].
  rewrite (U_atom Eb 32 v K32) by (unfold AREC in *; lia). reflexivity. }
assert (V12F : val_mem SEGS (mrestrict (w_H W2) (ms_mem msE)) (LA + 12) 4 cap).
{ replace (LA + 12) with (base_val Eb (Some 9%nat) + 12)
  by (cbn [base_val]; rewrite K9, unsigned_lit_small by lia; lia).
  apply (val_mem_of_chunk4 Eb _ _ 12 (SOff 34 0) cap Hch12); [|lia].
  rewrite (U_atom Eb 34 cap K34) by lia. reflexivity. }
unfold arm in Mv, Mc.
(* the runs after the free, the memmove and the last run wrote the head, the moved range and the memmove's scratch *)
assert (TAIL : forall a, 0 <= a < 2 ^ 64 -> ~ (LA <= a < LA + 16) ->
  ~ (v + AREC * Z.of_nat i <= a < v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i)) ->
  ~ (sp0 - LDROP_FRAME - ASTACK <= a < sp0 - LDROP_FRAME) ->
  aview SEGS (w_H W2) (ms_mem msE) a = aview SEGS (w_H W2) mem2 a).
{ intros a Ha Hout Hmv Hst.
  lazymatch type of HFrE with frame_of ?Ev ?rs _ _ =>
    rewrite (aview_kept_out Ev rs (w_H W2) mem3 (ms_mem msE) HFrE a Ha); [| ld_nowr9 U9b Hout] end.
  rewrite (Hfr3 a Ha Hmv ltac:(intros Hc; apply Hst; lia)).
  exact (KQ a Ha Hout). }
(* presence, from the free's return to the epilogue *)
assert (PCH : forall x, apresent (w_H W2) mem2 x -> apresent (w_H W2) (ms_mem msE) x).
{ intros x Hpa. eapply apresent_grows; [exact HGE|]. apply Hpres3. exact (PQ x Hpa). }
pose proof (regs_kept_of_st_ok_pi _ _ _ regs _ LDB_KEPT HS HAEb ltac:(vm_compute; reflexivity)) as HKR.
cbn [ms_regs restrict] in HKR.
apply (SRr_SRrG SEGS R WLE_R). apply SRr_ret. unfold ldb_post_xR. cbv beta.
lazymatch goal with |- exists _ _ _ _ _ _, mkCfg _ ?d = _ /\ _ => exists ly2, S2, Hp2, (ms_regs msE), (ms_mem msE), d end.
split. { rewrite EMS at 1. reflexivity. }
split. { exact HJ3. }
split.
{ (* every callee-saved register but s0..s5 is the body's entry value *)
  intros r Hr. destruct (ldb_clob_kept r Hr) as [-> | Hin]; [rewrite !getr_zero; reflexivity|].
  exact (HKR r Hin). }
split. { exact Hbl. }
split. { exact Hfrs2. }
split. { exact Hle. }
split. { exact HRM2. }
split.
{ (* above the allocator's ceiling: only the scratch below sp moved *)
  intros a Ha Hst. rewrite Hsp in Hst.
  assert (Hout : ~ (LA <= a < LA + 16)) by (pose proof C1; lia).
  rewrite (TAIL a ltac:(lia) Hout ltac:(pose proof C1; unfold AREC in *; lia) Hst).
  rewrite (proj1 HK a Ha ltac:(intros Hc; apply Hst; lia)).
  exact (HEAD a ltac:(lia) Hout). }
split.
{ (* image bytes: the head's two kept cells hold their values; the rest of the image is untouched *)
  intros a Himg Hos Herr Hn8. pose proof (pa_img_range a Himg) as Har.
  destruct (Z_lt_le_dec a LA) as [Hlo | Hlo]; [| destruct (Z_lt_le_dec a (LA + 16)) as [Hhi | Hhi]].
  2: { destruct (Z_lt_le_dec a (LA + 8)) as [H8a | H8a].
       - replace a with (LA + (a - LA)) by lia.
         apply (aview_of_val_mem2 _ _ _ _ LA 8 v); [exact Mv | exact V0F | lia].
       - replace a with ((LA + 12) + (a - (LA + 12))) by lia.
         apply (aview_of_val_mem2 _ _ _ _ (LA + 12) 4 cap); [exact Mc | exact V12F | lia]. }
  all: assert (Hout : ~ (LA <= a < LA + 16)) by lia.
  all: assert (Hnb : ~ (v + AREC * Z.of_nat i <= a < v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i)))
    by (intros Hc; apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) a HAR Hvin);
        [rewrite Hvreq; unfold AREC in *; lia | exact Himg]).
  all: rewrite (TAIL a ltac:(lia) Hout Hnb ltac:(pose proof C1; lia)).
  all: rewrite (proj1 (proj2 (proj2 HK)) a Himg Hos Herr).
  all: exact (HEAD a ltac:(lia) Hout). }
split.
{ (* the other blocks' bytes, and the vector's outside the moved range *)
  intros p m a Hin Ha Hns Hnm.
  destruct (alx_blocks _ _ _ LAWS lyc Sc Hpc W memc mdc _ _ HAR Hin) as (_ & Hp4096 & Hpceil & _).
  assert (Hni : ~ in_img SEGS a) by exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc p m a HAR Hin Ha).
  assert (Hout : ~ (LA <= a < LA + 16)) by (intros Hc; exact (Hni (proj1 (GIMG a Hc)))).
  assert (Ha64 : 0 <= a < 2 ^ 64) by (pose proof C1; lia).
  rewrite (TAIL a Ha64 Hout ltac:(unfold AREC in *; lia) ltac:(pose proof C1; lia)).
  replace a with (p + (a - p)) by lia.
  rewrite (proj1 (proj2 HK) p m (a - p) Hin ltac:(lia) ltac:(cbv beta; intros Hc; apply Hns; lia)).
  replace (p + (a - p)) with a by lia. exact (HEAD a Ha64 Hout). }
split.
{ (* the moved records: the memmove's copy, off the vector as the free left it *)
  intros k Hk.
  assert (Hx1 : v <= v + AREC * Z.of_nat i + k < v + AREC * cap) by (unfold AREC in *; lia).
  assert (Hx2 : v <= v + AREC * Z.of_nat i + AREC + k < v + AREC * cap) by (unfold AREC in *; lia).
  assert (O1 : ~ (LA <= v + AREC * Z.of_nat i + k < LA + 16)).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) (v + AREC * Z.of_nat i + k) HAR Hvin);
    [rewrite Hvreq; lia | exact (proj1 (GIMG _ Hc))]. }
  assert (O2 : ~ (LA <= v + AREC * Z.of_nat i + AREC + k < LA + 16)).
  { intros Hc. apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) (v + AREC * Z.of_nat i + AREC + k) HAR Hvin);
    [rewrite Hvreq; lia | exact (proj1 (GIMG _ Hc))]. }
  assert (R1 : 0 <= v + AREC * Z.of_nat i + k < 2 ^ 64) by (pose proof C1; lia).
  assert (R2 : 0 <= v + AREC * Z.of_nat i + AREC + k < 2 ^ 64) by (pose proof C1; lia).
  lazymatch type of HFrE with frame_of ?Ev ?rs _ _ =>
    rewrite (aview_kept_out Ev rs (w_H W2) mem3 (ms_mem msE) HFrE _ R1); [| ld_nowr9 U9b O1] end.
  rewrite (Hmov k Hk).
  rewrite (KQ _ R2 O2).
  pose proof (sep_blocks_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) s_i (len_i + 1) HAR Hvin Hsin
    ltac:(intros Heq; injection Heq as Heq _; exact (Hvne Heq))) as DJ.
  unfold zdisjoint in DJ. cbn [fst snd] in DJ. rewrite Hvreq in DJ.
  replace (v + AREC * Z.of_nat i + AREC + k) with (v + (AREC * Z.of_nat i + AREC + k)) by ring.
  rewrite (proj1 (proj2 HK) v (AREC * cap) (AREC * Z.of_nat i + AREC + k) Hvin
    ltac:(rewrite Hvreq; lia) ltac:(cbv beta; intros Hc; lia)).
  replace (v + (AREC * Z.of_nat i + AREC + k)) with (v + AREC * Z.of_nat i + AREC + k) by ring.
  exact (HEAD _ R2 O2). }
split. { unfold arm. exact MNEW. }
split.
{ apply (awr_kept_p W W2 memc (ms_mem msE) LA 16); [| exact Mawr].
  intros x Hx Hpa. apply PCH. apply GPRES; [exact Hx|]. eapply apresent_grows; [exact HGF | exact Hpa]. }
split.
{ unfold apres_kept. intros a Himg Hos Herr Hpa. apply PCH.
  apply (Hpres2 a Himg).
  - intros Ho. exact (Hos (proj1 (alx_owned_image _ _ _ LAWS lyc Sc Hpc W memc mdc a HAR Himg) Ho)).
  - intros Ho. exact (Hos (proj1 (alx_owned_image _ _ _ LAWS ly2 S2 Hp2 W2 mem2 md2 a HAR2 Himg) Ho)).
  - exact Herr.
  - intros Hr. exact (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc s_i (len_i + 1) a HAR Hsin Hr Himg).
  - eapply apresent_grows; [exact HGF | exact Hpa]. }
(* errno: an image byte, off G (gx_rt), off the vector and off the stack; the free keeps it (afree_cf_rule) *)
intros j Hj.
pose proof (pal_env B TL) as (Herrlo & Herrimg & _).
assert (Himg : in_img SEGS (as_errno B + j)) by (apply Herrimg; lia).
pose proof (pa_img_range _ Himg) as Har.
assert (Hout : ~ (LA <= as_errno B + j < LA + 16)) by (intros Hl; apply (proj1 (GRT _ (HLG _ Hl))); lia).
assert (Hnb : ~ (v + AREC * Z.of_nat i <= as_errno B + j < v + AREC * Z.of_nat i + AREC * (n - 1 - Z.of_nat i)))
  by (intros Hc; apply (blk_img_x SEGS B ARx LAWS lyc Sc Hpc W memc mdc v (AREC * cap) (as_errno B + j) HAR Hvin);
      [rewrite Hvreq; unfold AREC in *; lia | exact Himg]).
rewrite (TAIL (as_errno B + j) ltac:(lia) Hout Hnb ltac:(pose proof C1; lia)).
rewrite (Herr2 j Hj).
exact (HEAD (as_errno B + j) ltac:(lia) Hout).
Qed.

Theorem pb_list_drop_xR : ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
(* kit cand8 5860616f712 (W1Verify f83b4c2732c) drops ldrop_spec's `LA + 16 <= kLowMemEnd`, so one intro name goes;
   the bound the walk needs comes from ld_LA_range (HLG) below, as it already did. *)
intros W ly S Hp regs mem md ch LA l lines i HPRE H10 H11 HL Hi HLA8 HLA4 Hmv32 HZS HLGx HVoff Hmo kr HRM HCNT Hrom.
destruct l as [v cap recs junk].
pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
pose proof HG as HGok.
pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (HLG : forall a, LA <= a < LA + 16 -> inG G a) by (intros a Ha; exact (proj1 (HLGx a Ha))).
pose proof (ld_LA_range LA HLG) as HLAR.
destruct (ld_entry_x W ly S Hp regs mem md ch LA (HarnessRep.HL v cap recs junk) lines i HPRE H10 H11 HL Hi HLA8 HZS HLG)
  as [HS SHOK].
(* the list before the call *)
pose proof HL as (M1 & M2 & M3 & Mawr & (Hn0 & Hcap) & Hvb & HND & Hvni & HRF).
unfold HarnessRep.hl_n in M2, Hn0, Hvb, Hmv32.
cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]
  in M1, M2, M3, Mawr, Hn0, Hcap, Hvb, HND, Hvni, HRF, Hi, Hmv32.
assert (HiZ : 0 <= Z.of_nat i < Z.of_nat (length recs)) by lia.
destruct Hvb as [(Hc0 & _) | (Hcpos & Hvin & _ & _)]; [lia|].
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hvin) as (Hv16 & Hv4096 & Hvceil & _ & _ & _).
assert (Hvreq : req_size (AREC * cap) = AREC * cap)
by (unfold req_size; destruct (Z.eqb_spec (AREC * cap) 0); unfold AREC in *; lia).
rewrite Hvreq in Hvceil.
pose proof (proj1 (Forall_forall _ _) HRF _ (nth_In _ (0, []) Hi)) as (Hsin & _ & _ & _).
destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hsin) as (_ & Hs4096 & Hsceil & _ & _ & _).
assert (Hsreq : req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) =
  Z.of_nat (length (snd (nth i recs (0, [])))) + 1)
by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) 0); lia).
rewrite Hsreq in Hsceil.
assert (Hs64 : 0 <= fst (nth i recs (0, [])) < 2 ^ 64) by lia.
assert (Hlen0 : 0 <= Z.of_nat (length (snd (nth i recs (0, []))))) by lia.
assert (Hvne : v <> fst (nth i recs (0, []))).
{ intros Ev. apply Hvni. rewrite Ev. apply in_map. apply nth_In. exact Hi. }
(* the bounds the trap refutation reads, with the constants spelled out for lia *)
assert (HIB : 0 <= Z.of_nat i /\ Z.of_nat i < Z.of_nat (length recs) <= cap /\ cap < 2 ^ 30) by lia.
assert (HVB : 4096 <= v /\ v + 16 * cap <= 140737486618624) by (unfold AREC in *; lia).
(* the journal: the vector and record i's text are the bytes the body may write or free *)
set (FP := [(v, v + AREC * cap); (fst (nth i recs (0, [])),
  fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1))]).
pose proof (ajournal_gx_init_xR SEGS B PST ARx R_refl G 0 [] LDROP_STK FP ly S Hp W regs mem md ch HPRE ltac:(lia) eq_refl
  ltac:(lia) ltac:(intros a Ha; lia)) as HJ.
remember (Eimg (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk)))) as E eqn:HE.
assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
assert (HAE : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) E)
by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
assert (EE : forall m (rr : bv 5), Z.of_nat m = bv_unsigned rr -> ew E m = getr regs rr)
by (intros m rr Hm; subst E; pose proof (bv_unsigned_in_range 5 rr) as Hr5; change (bv_modulus 5) with 32 in Hr5;
rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hm).
assert (E1 : ew E 1 = getr regs 1) by exact (EE 1%nat 1%bv eq_refl).
assert (E2 : ew E 2 = getr regs 2) by exact (EE 2%nat 2%bv eq_refl).
assert (E3 : ew E 3 = w64 (as_gp B)) by (rewrite (EE 3%nat 3%bv eq_refl); exact Hgp).
assert (E4 : ew E 4 = w64 (as_tp B)) by (rewrite (EE 4%nat 4%bv eq_refl); exact Htp).
assert (E10 : ew E 10 = Z_to_bv 64 LA) by (rewrite (EE 10%nat 10%bv eq_refl); exact H10).
assert (E11 : ew E 11 = Z_to_bv 64 (Z.of_nat i)) by (rewrite (EE 11%nat 11%bv eq_refl); exact H11).
assert (E32 : ew E 32 = Z_to_bv 64 v)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
assert (E33 : ew E 33 = Z_to_bv 64 (Z.of_nat (length recs)))
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
assert (E34 : ew E 34 = Z_to_bv 64 cap)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
assert (E35 : ew E 35 = Z_to_bv 64 SB)
by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 3)).
assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
clear HE EE.
assert (BV10 : base_val E (Some 10%nat) = LA)
by (cbn [base_val]; rewrite E10; apply unsigned_lit_small; lia).
unfold cfg_at. change (w64 A_list_dropP) with (Z_to_bv 64 A_list_dropP).
unfold A_list_dropP, A_list_drop.
(* ---- the prologue, 0x85b50 .. 0x85bcc ---- *)
assert (KT : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) -> ~ (LA <= a < LA + 16) ->
  aview SEGS (w_H W) mem a = aview SEGS (w_H W) mem a) by (intros; reflexivity).
assert (PT : forall x, apresent (w_H W) mem x -> apresent (w_H W) mem x) by (intros x Hx; exact Hx).
paj_run_to_tok_xR RUNTOG HS HJ SHOK ld_Bspan A_ld_body. { ld_awr_top Usp BV10 HLG. }
ld_foldT (spZ regs) LA Usp E10 KT PT.
(* 0x85bc4 beqz: the pointer-overflow check of &l->v[i] = v + 16 i (trap_ptr_sovf: i >= 0, v + 16 i >= 16 i) *)
psrr_branch_tok RUNG BRR HS SHOK ld_Bspan.
{ exfalso. lazymatch goal with Hc : branch_taken _ (sv_denot ?Ev _) _ = true |- _ =>
  assert (G11 : ew Ev 11 = Z_to_bv 64 (Z.of_nat i)) by (cbn [ew ewset Nat.eqb]; exact E11);
  assert (G32 : ew Ev 32 = Z_to_bv 64 v) by (cbn [ew ewset Nat.eqb]; exact E32);
  rewrite (trap_ptr_sovf Ev (SLit 0) _ 0 (U_lit Ev 0 ltac:(lia))
    (trap_U_sltu_ge Ev _ _ (16 * Z.of_nat i) (16 * Z.of_nat i + v)
      (ldU_o Ev 11 (Z.of_nat i) G11 ltac:(clear - HIB HVB; lia))
      (ldU_p Ev 11 (Z.of_nat i) v G11 G32 ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia) ltac:(clear - HIB HVB; lia))
      ltac:(clear - HIB HVB; lia))) in Hc; discriminate Hc end. }
paj_run_to_tok_xR RUNTOG HS HJ SHOK ld_Bspan A_ld_body. { ld_awr_top Usp BV10 HLG. }
ld_foldT (spZ regs) LA Usp E10 KT PT.
ld_name_ms msb.
repeat match goal with Hx : branch_taken _ _ _ = false |- _ => clear Hx end.
pmkst HS.
prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3.
prreg HS (4%bv : bv 5) Q4. prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9.
prreg HS (10%bv : bv 5) Q10. prreg HS (18%bv : bv 5) Q18. prreg HS (19%bv : bv 5) Q19.
prreg HS (20%bv : bv 5) Q20. prreg HS (21%bv : bv 5) Q21.
(* the registers at the body's entry *)
assert (Ub : spZ (ms_regs msb) = spZ regs - LDROP_FRAME).
{ unfold spZ at 1. rewrite Q2, Usp. rewrite unsigned_lit_small by ldl. unfold LDROP_FRAME. lia. }
assert (R1 : getr (ms_regs msb) 1 = getr regs 1) by (rewrite Q1; exact E1).
assert (R3 : getr (ms_regs msb) 3 = w64 (as_gp B)) by (rewrite Q3; exact E3).
assert (R4 : getr (ms_regs msb) 4 = w64 (as_tp B)) by (rewrite Q4; exact E4).
assert (R8 : getr (ms_regs msb) 8 = w64 (Z.of_nat i)) by (rewrite Q8; exact E11).
assert (R9 : getr (ms_regs msb) 9 = w64 LA) by (rewrite Q9; exact E10).
assert (R10 : getr (ms_regs msb) 10 = w64 (v + AREC * Z.of_nat i)).
{ rewrite Q10, E11, E32, ld_addr_eq by ldl. unfold w64, AREC. f_equal; lia. }
assert (R18 : getr (ms_regs msb) 18 = w64 SB) by (rewrite Q18; exact E35).
assert (R19 : getr (ms_regs msb) 19 = w64 (AREC * Z.of_nat i)).
{ rewrite Q19, E11, ld_sll4 by ldl. unfold w64, AREC. reflexivity. }
assert (R20 : getr (ms_regs msb) 20 = w64 (SB + LA / 8)).
{ rewrite Q20, E10, E35, ld_srl3 by lia. rewrite YI08.alu64_add_lit. unfold w64. f_equal. lia. }
assert (R21 : getr (ms_regs msb) 21 = w64 0) by (rewrite Q21; reflexivity).
(* the prologue wrote only its frame and (in the region's window, but not in fact) the list head *)
assert (HNS : forall a, a < alloc_ceiling -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs)) by (intros a Ha Hc; ldl).
assert (HBK : forall p m a, In (p, m) (ablocks B ly S) -> p <= a < p + req_size m ->
  aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem a).
{ intros p m a Hin Hr. destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hin) as (_ & Hp4 & Hpc & _).
  apply KT; [lia | apply HNS; lia |].
  intros Hl. apply (blk_img_x SEGS B ARx LAWS ly S Hp W mem md p m a HAR Hin Hr). exact (proj1 (HG a (HLG a Hl))). }
(* the list head at the body's entry, read off the list region *)
pose proof (st_ok_mem_ok SEGS _ _ _ HS) as (_ & Hrok & _).
pose proof (proj1 (Forall_forall _ _) Hrok (ld_lreg 10)
  ltac:(cbn [ss_mem]; right; right; right; left; reflexivity)) as (_ & _ & HLw & HLch).
cbn [ld_lreg YP09.r_base YP09.r_wlo YP09.r_whi YP09.r_chunks ms_mem restrict] in HLw, HLch.
rewrite BV10 in HLw, HLch.
assert (MvC : val_mem SEGS (arm W (ms_mem msb)) LA 8 v).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ v Hc) as V. rewrite Z.add_0_r in V. apply V.
  - cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MnC : val_mem SEGS (arm W (ms_mem msb)) (LA + 8) 4 (Z.of_nat (length recs))).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ (Z.of_nat (length recs)) Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (McC : val_mem SEGS (arm W (ms_mem msb)) (LA + 12) 4 cap).
{ pose proof (proj1 (Forall_forall _ _) HLch _ ltac:(right; right; left; reflexivity)) as Hc.
  pose proof (val_of_chunk_ok SEGS E _ LA _ _ _ cap Hc) as V. apply V.
  - cbn [sv_denot]. rewrite E34, Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - ldz.
  - ldz. }
assert (MawrC : awr W (ms_mem msb) LA 16) by (intros j Hj; exact (HLw j Hj)).
assert (KLA : forall a, LA <= a < LA + 8 \/ LA + 12 <= a < LA + 16 ->
  aview SEGS (w_H W) (ms_mem msb) a = aview SEGS (w_H W) mem a).
{ intros a [Ha|Ha].
  - replace a with (LA + (a - LA)) by lia.
    apply (ld_aview_agree W W mem (ms_mem msb) LA 8 v); [exact M1 | exact MvC | simpl Z.of_nat; lia].
  - replace a with ((LA + 12) + (a - (LA + 12))) by lia.
    apply (ld_aview_agree W W mem (ms_mem msb) (LA + 12) 4 cap); [exact M3 | exact McC | simpl Z.of_nat; lia]. }
(* record i's text pointer, a vector byte the prologue kept *)
pose proof (ld_rec_ptr B ly S W mem LA (HarnessRep.HL v cap recs junk) lines i HL Hi) as Ms0.
cbn [HarnessRep.hl_v HarnessRep.hl_recs] in Ms0. rewrite Z.mod_small in Ms0 by lia.
assert (MsC : val_mem SEGS (arm W (ms_mem msb)) (v + AREC * Z.of_nat i) 8 (fst (nth i recs (0, [])))).
{ unfold AREC. apply (val_mem_kept SEGS (w_H W) (w_H W) mem (ms_mem msb)); [|exact Ms0].
  intros k Hk. simpl Z.of_nat in Hk. apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl]. }
(* the ROM view: no ROM byte is in the frame or in G *)
assert (HromC : rom_view SEGS W (ms_mem msb)).
{ intros a Hin. destruct (ROMS a Hin) as (_ & _ & HnG).
  assert (Himg : in_img SEGS a) by (destruct Hin as (sg & Hsg & _ & Hr); exists sg; split; [exact Hsg | exact Hr]).
  pose proof (pa_img_range a Himg) as Har.
  rewrite (KT a ltac:(lia) ltac:(apply HNS; lia) ltac:(intros Hl; exact (HnG (HLG a Hl)))).
  exact (Hrom a Hin). }
assert (FPs : In (fst (nth i recs (0, [])), Z.of_nat (length (snd (nth i recs (0, [])))) + 1) (ablocks B ly S) ->
  forall j, 0 <= j < req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1) ->
  inFP FP (fst (nth i recs (0, [])) + j)).
{ intros _ j Hj. exists (fst (nth i recs (0, [])),
    fst (nth i recs (0, [])) + req_size (Z.of_nat (length (snd (nth i recs (0, [])))) + 1)).
  split; [right; left; reflexivity | cbn [fst snd]; lia]. }
assert (FPv : forall a, v <= a < v + AREC * cap -> inFP FP a).
{ intros a Ha. exists (v, v + AREC * cap). split; [left; reflexivity | cbn [fst snd]; lia]. }
(* ---- the body, 0x85bcc .. 0x85cb0 (ld_bodyX_xR) ---- *)
eapply (SRrG_bind SEGS R R_trans).
{ exact (ld_bodyX_xR W (ms_regs msb) (ms_mem msb) _ (spZ regs) FP ly S Hp W mem md [] ly S Hp 0 LA v (Z.of_nat (length recs)) cap i
    (fst (nth i recs (0, []))) (Z.of_nat (length (snd (nth i recs (0, []))))) (getr regs 1) kr
    HJ Ub R1 Hra Hra4 R3 R4 R8 R9 R10 R18 R19 R20 R21 HiZ (conj Hn0 Hcap) HLA8 HLG HZS MvC MnC McC MawrC MsC Hs64
    Hvin Hsin Hlen0 Hvne FPs FPv Hmv32 Hmo
    (* the free's room premise: MT_rk charges 1 for a free, so Z.to_nat (mo_free MT_rk) + kr is 1 + kr by
       conversion; its count premise is the spec's (lib/A/W_list_drop_top.v, F2's text) *)
    HRM HCNT HromC). }
cbv beta. intros W' c' Hwle' (ly' & S' & Hp' & regs' & mem' & md' & -> & HJ' & HCL & Hbl & Hfrs & Hmole & HRM' & HKhi &
  HKimg & HKblk & Hmv & Hn' & Hawr' & Hapr & Herrb).
pose proof HJ as HARb. apply ajournal_gx_AR_xR in HARb.
pose proof HJ' as HAR'. apply ajournal_gx_AR_xR in HAR'.
pose proof HJ' as (_ & _ & (memS' & HJi' & _) & _). rewrite !Z.add_0_r in HJi'.
pose proof HJi' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HPR' & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HARb) as (Kc1 & _ & Kg1 & _).
destruct (alx_const _ _ _ LAWS _ _ _ _ _ _ HAR') as (Kc2 & _ & Kg2 & _).
rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg1) as VG1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kg2) as VG2.
pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc1) as VC1. pose proof (val_mem_of_rdword SEGS _ _ _ _ Kc2) as VC2.
(* back at 0x85cb0: splice the body's result, dropping the list region (the body changed l->n); s0..s5 are not
   kept by the body, so they are havocked too, and the epilogue reloads them *)
jafter_stretch_keep_hi HS 36%nat regs' (mrestrict (w_H W') mem') LDB_CLOB A_ld_epi [0;1;2]%nat HS2.
match type of HS2 with ?P1 -> ?Q1 -> _ =>
assert (HP : P1); [|assert (HQ : Q1); [|specialize (HS2 HP HQ); clear HP HQ]] end.
{ intros r0 Hr0. cbn [ms_regs restrict]. exact (HCL r0 Hr0). }
{ cbn [ms_mem restrict].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]].
  - split; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val]; rewrite Usp.
    + intros a Ha. apply (mbyte_of_aview SEGS). apply HKhi; [ldl | rewrite Ub; ldl].
    + intros a Ha _. apply (apresent_writable SEGS). apply HPR'. ldl.
  - exact (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)) 0 0 _
      (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VG1 VG2 ltac:(lia)).
  - exact (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF 0 0 _
      (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) VC1 VC2 ltac:(lia)). }
clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
remember (havoc E 36 (map (getr regs') LDB_CLOB)) as Ea eqn:HEa in HS.
assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
assert (OLDa : forall m0, (m0 < 36)%nat -> ew Ea m0 = ew E m0)
by (intros m0 Hm0; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm0).
assert (HAEa : env_agree 32 (Ereg regs (ld_extra (HarnessRep.HL v cap recs junk))) Ea)
by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
clear HEa.
assert (Uspa : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by (cbv; lia); exact Usp).
assert (SHOK2 : sh_ok SEGS ld_Bx [] Ea (mrestrict (w_H W') mem')) by constructor.
(* ---- the epilogue, 0x85cb0 .. the ret ---- *)
paj_run_tok_xR RUNG HS HJ' SHOK2 ld_Bspan.
{ lazymatch goal with |- awr_ok_x ?E ?rs ?G ?XO ?OUT ?stk ?sp0 ?fp ?b0 ?bc ?ly ?own =>
  let rs' := eval vm_compute in rs in change (awr_ok_x E rs' G XO OUT stk sp0 fp b0 bc ly own) end.
  apply awr_ok_x_cons_awr0; [awr_ok_tac; try exact Uspa|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_cons_awr0; [awr_ok_tac|].
  apply awr_ok_x_nil. }
ld_names msZ HFrZ HGZ.
(* the epilogue wrote only the frame *)
assert (KEEP3 : forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - LDROP_FRAME <= a < spZ regs) ->
  aview SEGS (w_H W') (ms_mem msZ) a = aview SEGS (w_H W') mem' a).
{ intros a Ha Hno.
  lazymatch type of HFrZ with frame_of ?Ev ?rs _ _ =>
    apply (aview_kept_out Ev rs (w_H W') mem' (ms_mem msZ) HFrZ a Ha) end.
  intros (r & Hin & Hr). vm_compute in Hin.
  repeat (destruct Hin as [<- | Hin];
    [cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Uspa in Hr;
     unfold LDROP_FRAME in Hno; clear - Hr Hno; lia |]).
  destruct Hin. }
prreg HS (1%bv : bv 5) R1f.
apply (SRr_SRrG SEGS R WLE_R).
eapply (RET W' _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
intros mat'. unfold ldrop_post_xR. cbv beta.
exists ly', S', Hp'.
lazymatch goal with |- exists _ _ _, mkCfg (mkst ?r _ ?m _) ?d = _ /\ _ => exists r, m, d end.
split; [cbn [ms_regs]; rewrite R1f; rewrite OLDa by (cbv; lia); rewrite E1, Hra; reflexivity|].
split; [apply (ajournal_gx_materialize_xR SEGS B PST ARx LAWS Hsegs); exact HJ'|].
split.
{ lazymatch type of HS with st_ok_pi _ _ ?Ev _ _ =>
  eapply (aregs_preserved_of_st_ok SEGS _ Ev _ _ regs (ld_extra (HarnessRep.HL v cap recs junk)) HS);
  [exact HAEa | vm_compute; reflexivity] end. }
split.
{ intros a Hia Hoa Hea Hpa. apply (apresent_grows (w_H W') mem' (ms_mem msZ) a HGZ).
  apply (Hapr a Hia Hoa Hea). apply PT. exact Hpa. }
split.
{ (* errno: an image byte off G and off the frame; the body keeps it *)
  intros j Hj.
  pose proof (pal_env B TL) as (Herrlo & Herrimg & _).
  assert (Himg : in_img SEGS (as_errno B + j)) by (apply Herrimg; lia).
  pose proof (pa_img_range _ Himg) as Har.
  assert (Hout : ~ (LA <= as_errno B + j < LA + 16)) by (intros Hl; apply (proj1 (GRT _ (HLG _ Hl))); lia).
  rewrite KEEP3 by ldl.
  rewrite (Herrb j Hj).
  exact (KT (as_errno B + j) ltac:(lia) ltac:(apply HNS; lia) Hout). }
split.
{ (* the representation half: the list at LA after the call is ldrop_list l i *)
  apply (alist_at_drop B ly S W mem ly' S' W' (ms_mem msZ) LA (HarnessRep.HL v cap recs junk) lines i HL Hi);
  cbn [HarnessRep.hl_v HarnessRep.hl_cap HarnessRep.hl_recs HarnessRep.hl_junk]; unfold HarnessRep.hl_n;
  cbn [HarnessRep.hl_recs].
  - exact Hbl.
  - (* the head but its count: an image byte of G, kept by the body and by the epilogue *)
    intros a Ha. assert (HaG : LA <= a < LA + 16) by lia.
    rewrite KEEP3 by ldl.
    rewrite (HKimg a (proj1 (HG a (HLG a HaG))) (proj1 (proj2 (HG a (HLG a HaG)))) (proj1 (GRT a (HLG a HaG))) ltac:(lia)).
    exact (KLA a Ha).
  - apply (awr_kept_w W' W' mem' (ms_mem msZ) LA 16);
    [intros x _ Hpa; exact (apresent_grows _ _ _ x HGZ Hpa) | apply wle_refl | exact Hawr'].
  - apply (val_mem_kept SEGS (w_H W') (w_H W') mem' (ms_mem msZ)); [|exact Hn'].
    intros k Hk. simpl Z.of_nat in Hk. apply KEEP3; ldl.
  - (* the records above i, one record lower *)
    intros k Hk. rewrite KEEP3 by ldl. rewrite (Hmv k Hk).
    apply (HBK v (AREC * cap)); [exact Hvin | rewrite Hvreq; ldl].
  - (* the rest of the vector *)
    intros a Ha.
    assert (Hva : v <= a < v + req_size (AREC * cap)) by (rewrite Hvreq; ldl).
    rewrite KEEP3 by ldl.
    rewrite (HKblk v (AREC * cap) a Hvin Hva).
    + exact (HBK v (AREC * cap) a Hvin Hva).
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hvin Hsin Hvne Hva).
    + ldl.
  - (* the texts of the other records *)
    intros r Hr a Ha.
    cbn [ldrop_list HarnessRep.hl_recs] in Hr.
    destruct (ld_recs_drop recs i r Hi ltac:(apply NoDup_ListNoDup; exact HND) Hr) as (HrIn & Hrne).
    pose proof (proj1 (Forall_forall _ _) HRF r HrIn) as (Hrin & _ & _ & _).
    destruct (alx_blocks _ _ _ LAWS ly S Hp W mem md _ _ HAR Hrin) as (_ & Hr4096 & Hrceil & _ & _ & _).
    assert (Hrreq : req_size (Z.of_nat (length (snd r)) + 1) = Z.of_nat (length (snd r)) + 1)
    by (unfold req_size; destruct (Z.eqb_spec (Z.of_nat (length (snd r)) + 1) 0); lia).
    rewrite Hrreq in Hrceil.
    assert (Hra' : fst r <= a < fst r + req_size (Z.of_nat (length (snd r)) + 1)) by (rewrite Hrreq; lia).
    assert (Hrv : fst r <> v) by (intros Ev; apply Hvni; rewrite <- Ev; apply in_map; exact HrIn).
    rewrite KEEP3 by ldl.
    rewrite (HKblk _ _ a Hrin Hra').
    + exact (HBK _ _ a Hrin Hra').
    + exact (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hsin Hrne Hra').
    + intros Hm. apply (ld_blk_disj_x ly S Hp W mem md _ _ _ _ a HAR Hrin Hvin Hrv Hra'). rewrite Hvreq. ldl. }
split; [exact Hbl | split; [exact Hmole | exact HRM']].
Qed.

Theorem pb_list_drop_at_xR : ldrop_spec_xR B PST ARx R MT RP G (BASE + AF_fr_list_drop).
Proof. exact pb_list_drop_xR. Qed.

End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
(* the R premises at wle: the R free rule from the strict one (W_journal_x.v afree_cf_rule_c_xR_of_x), RO := True *)
Local Ltac wle_inst_r := first [ eassumption | intros; exact I | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]
  | eapply afree_cf_rule_c_xR_of_x; eassumption ].
Lemma aj_free_gx_x : forall W regsT memT STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc mdc k pa nb (o : Z) raw ch (kr : nat),
AJG STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memT mdc k ->
In (pa, nb) (ablocks B lyc Sc) -> getr regsT 10 = w64 pa ->
spZ regsT = sp0 + o -> o mod 16 = 0 -> o <= 0 -> ASTACK - o <= STK ->
getr regsT 3 = w64 (as_gp B) -> getr regsT 4 = w64 (as_tp B) ->
getr regsT 1 = raw -> YK0s.ret_ok raw ->
chain_pre lyc (aview SEGS (w_H W) memT) regsT ch ->
In (raZ regsT :: spine ch) CTX ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
(In (pa, nb) (ablocks B ly S) -> forall j, 0 <= j < req_size nb -> inFP FP (pa + j)) ->
mo_ok MT Sc (mo_free MT) ->
SRr SEGS W (mkCfg (mkst regsT (Z_to_bv 64 (pc_wrap_free (as_code B))) memT (seg_rom SEGS)) mdc)
(fun W2 c2 => exists ly2 S2 Hp2 regs2 mem2 md2,
 c2 = mkCfg (mkst regs2 raw mem2 (seg_rom SEGS)) md2 /\
 AJG STK sp0 FP ly S Hp W0 mem md own ly2 S2 Hp2 W2 mem2 md2 (k + 1) /\
 aregs_preserved regsT regs2 /\
 (exists l1 l2, ablocks B lyc Sc = l1 ++ (pa, nb) :: l2 /\ ablocks B ly2 S2 = l1 ++ l2) /\
 frames S2 = frames Sc /\
 acall_kept SEGS B lyc Sc W memT W2 mem2 (sp0 + o - ASTACK) (sp0 + o) (fun a => pa <= a < pa + req_size nb) /\
 mo_le MT Sc S2 (mo_free MT) /\ rp_RM RP S2 kr /\
 ((forall j, 0 <= j < 4 -> aview SEGS (w_H W2) mem2 (as_errno B + j) = aview SEGS (w_H W) memT (as_errno B + j)) /\
  (forall a, in_img SEGS a -> ~ aowned B lyc Sc a -> ~ aowned B ly2 S2 a ->
   ~ (as_errno B <= a < as_errno B + 4) -> ~ (pa <= a < pa + req_size nb) ->
   apresent (w_H W) memT a -> apresent (w_H W2) mem2 a))).
Proof. first [ eapply aj_free_gx_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply aj_free_gx_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Lemma ld_bodyX_x : forall W regs memc mdc sp0 FP ly S Hp W0 mem md own lyc Sc Hpc kk
LA v n cap (i : nat) s_i len_i raw (kr : nat),
AJG LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc Hpc W memc mdc kk ->
spZ regs = sp0 - LDROP_FRAME ->
getr regs 1 = raw -> YK0s.ret_ok raw -> 4096 <= bv_unsigned raw ->
getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) ->
getr regs 8 = w64 (Z.of_nat i) -> getr regs 9 = w64 LA ->
getr regs 10 = w64 (v + AREC * Z.of_nat i) ->
getr regs 18 = w64 SB -> getr regs 19 = w64 (AREC * Z.of_nat i) -> getr regs 20 = w64 (SB + LA / 8) ->
getr regs 21 = w64 0 ->
0 <= Z.of_nat i < n -> n <= cap < 2 ^ 30 ->
LA mod 8 = 0 -> (forall a, LA <= a < LA + 16 -> inG G a) -> azs B LA 16 ->
val_mem SEGS (arm W memc) LA 8 v -> val_mem SEGS (arm W memc) (LA + 8) 4 n ->
val_mem SEGS (arm W memc) (LA + 12) 4 cap -> awr W memc LA 16 ->
val_mem SEGS (arm W memc) (v + AREC * Z.of_nat i) 8 s_i -> 0 <= s_i < 2 ^ 64 ->
In (v, AREC * cap) (ablocks B lyc Sc) -> In (s_i, len_i + 1) (ablocks B lyc Sc) -> 0 <= len_i -> v <> s_i ->
(In (s_i, len_i + 1) (ablocks B ly S) -> forall j, 0 <= j < req_size (len_i + 1) -> inFP FP (s_i + j)) ->
(forall a, v <= a < v + AREC * cap -> inFP FP a) ->
(* the bytes the memmove moves (the intrinsic's n < 2^32): the kit's ldrop_spec premise, W_contract.v *)
AREC * (n - 1 - Z.of_nat i) < 2 ^ 32 ->
mo_ok MT Sc (mo_free MT) ->
rp_RM RP Sc (1 + kr) -> cnt_ok RP (ablocks B lyc Sc) ->
rom_view SEGS W memc ->
SRr SEGS W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_ld_body)) memc (seg_rom SEGS)) mdc)
(ldb_post_x W regs memc LDROP_STK sp0 FP ly S Hp W0 mem md own lyc Sc kk LA v n cap i s_i len_i kr).
Proof. first [ eapply ld_bodyX_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply ld_bodyX_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Theorem pb_list_drop_x : ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof. first [ eapply pb_list_drop_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply pb_list_drop_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
Theorem pb_list_drop_at_x : ldrop_spec_x B PST ARx MT RP G (BASE + AF_fr_list_drop).
Proof. first [ eapply pb_list_drop_at_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply pb_list_drop_at_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
End d.
(* The G-generic form: the body (ld_bodyX_x) needs ROMS at the G it runs at, i.e. no ROM byte in G, and neither
   gx_ok, gx_rt nor the relation gives that; W_journal.v's rom_out G gives ROMS, so a caller that holds gx_ok, gx_rt
   and rom_out at its G takes pb_list_drop_ro_x below (lib/A/W_list_drop_top.v's form). *)
Section e.
Variable B : asyms.
Variable PST : list (Z * Z).
Variable ARx : alayout -> astate -> list Z -> world SEGS -> (word -> option byte) -> Model -> Prop.
Context {hl : Z}.
Hypothesis LAWS : AR_laws_x SEGS B ARx hl.
Hypothesis HP0 : forall ly S Hp W mem md, ARx ly S Hp W mem md -> Hp = [].
Variable MT : ameter_ops.
Variable RP : roomp.
Hypothesis TL : PALib B.
Variable CTX : list (list Z).
Hypothesis AFREE : afree_cf_rule_c_x SEGS B PST ARx MT RP CTX.
(* fuzz_reply.asan-ubsan objdump: 0x85be8 jal __interceptor_trampoline_free; returns to 0x85bec = list_drop 0x85b50 + 0x9c *)
Hypothesis HCTX_ld_free : In [BASE + AF_fr_list_drop + 0x9c] CTX.
Hypothesis AMOVE : amemmove_realizes_x B ARx (SIGMA WS_asan_memmove).

(* ---- route R (RULE-SHAPES.md (sha256 2e856ce788dd; internal record) sec 0): the R twin of each relation-dependent lemma above.  Each
   twin is its strict text with the journal and the step relation at R: ajournal_gx_x -> ajournal_gx_xR .. R,
   SRr SEGS -> SRrG SEGS R, the runs and the branch are their SRrG forms (W_journal_x.v paj_run_x_xG /
   paj_run_to_x_xG, W_kit.v paj_branch_xR), each carrier X_x -> its twin X_xR (R last), the journal lemmas their _xR
   forms, and each lemma name L -> LR; the relation-free helpers above are cited as they are.  The strict text is
   untouched. ---- *)
Section wR.
Variable R : world SEGS -> world SEGS -> Prop.
Hypothesis R_refl : forall W, R W W.
Hypothesis R_trans : forall W1 W2 W3, R W1 W2 -> R W2 W3 -> R W1 W3.
Hypothesis WLE_R : forall W W', @wle SEGS W W' -> R W W'.
Variable RO : (word -> option byte) -> Prop.
Hypothesis RO_ARx : forall ly S Hp (W : world SEGS) mem md, ARx ly S Hp W mem md -> RO mem.
Hypothesis AFREE_R : afree_cf_rule_c_xR SEGS B PST ARx MT RP RO CTX R.

Theorem pb_list_drop_ro_xR : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_xR B PST ARx R MT RP G A_list_dropP.
Proof.
intros G HG GRT HRO. eapply pb_list_drop_xR with (R := R) (RO := RO); try eassumption.
intros a Ha. destruct (HRO a Ha) as (HnG & Hpin & Hne & _). exact (conj Hpin (conj Hne HnG)).
Qed.
End wR.

(* ---- the strict lemmas of this Section at R := wle: each is its R twin above at wle (wle_refl, wle_trans, the
   identity for WLE_R); the statements are the strict ones, checked by conversion. ---- *)
(* the R premises at wle: the R free rule from the strict one (W_journal_x.v afree_cf_rule_c_xR_of_x), RO := True *)
Local Ltac wle_inst_r := first [ eassumption | intros; exact I | intros ? ? H; exact H | intros ?; apply wle_refl
  | intros ? ? ? H1 H2; eapply wle_trans; [exact H1 | exact H2]
  | eapply afree_cf_rule_c_xR_of_x; eassumption ].
Theorem pb_list_drop_ro_x : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec_x B PST ARx MT RP G A_list_dropP.
Proof. first [ eapply pb_list_drop_ro_xR with (R := @wle SEGS) (RO := fun _ => True) | eapply pb_list_drop_ro_xR with (R := @wle SEGS) ]; wle_inst_r. Qed.
End e.

(* ---- THE AR STATEMENTS, re-derived (route (b), step 3).  First the caller-context forms over AR, a Theorem Labs lane's
   pb_list_drop_c / pb_list_drop_at_c / pb_list_drop_ro_c (commit dc072059c86, lib/B/W_list_drop.v, sha256 6a0904505010; internal record):
   their Theorem lines and Section hypotheses are k1's, byte-identical (LAWS : AR_laws stays; a Theorem Labs lane's ruling
   03:30Z: the plain names keep their B-old statements, LX0 is only on the _x names); each is a corollary of pb_list_drop_x / pb_list_drop_ro_x at ARx := ARi0
   (cgif's AR with the head set empty), PST := [], CTX := CTX_F.  Then the AR statements of the old walk,
   pb_list_drop / pb_list_drop_at / pb_list_drop_ro, byte-identical, are corollaries of the _c forms at the one-entry
   table [[BASE + AF_fr_list_drop + 0x9c]] through W_journal.v afree_cf_rule_c_weak (k1's proofs).  Each proof
   derives LX0 (the laws at ARi0) from LAWS by lib/B/YLX0.v lx_AR_laws_x_ARi0_of (a Theorem Labs lane's).  Bridges: W_contract_x.ldrop_spec_x_AR0,
   ARi0_hp0, W_journal_x.afree_cf_rule_c_x_of_AR0, W_sites_x.amemmove_realizes_x_of_AR0. ---- *)
Section dARc.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Variable CTX_F : list (list Z).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* rom_view has to cross the free call: acall_kept keeps an image byte outside the allocator's statics and errno,
   and an owned read-only byte is one of AR's pinned const cells (W_journal.v rom_pinned).  ROM bytes are off G.
   Facts about the instance and G, not about list_drop (rom_out's shape, W_journal.v); lib/A/W_list_drop.v's text. *)
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Theorem pb_list_drop_c : ldrop_spec B MT G A_list_dropP.
Proof.
apply ldrop_spec_x_AR0.
pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX_F AFREE) as AFREE0.
pose proof (amemmove_realizes_x_of_AR0 B (SIGMA WS_asan_memmove) AMOVE) as AMOVE0.
eapply pb_list_drop_x; eassumption.
Qed.
(* the kit's spec at list_drop's B address, in MERGE.md (sha256 0694aca87ccd; internal record) step 2's form (A_list_dropP is BASE + AF_fr_list_drop) *)
Theorem pb_list_drop_at_c : ldrop_spec B MT G (BASE + AF_fr_list_drop).
Proof. exact pb_list_drop_c. Qed.
End dARc.
Section eARc.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Variable CTX_F : list (list Z).
Hypothesis AFREE : afree_cf_rule_c SEGS B MT CTX_F.
Hypothesis HCTX_ld : In [BASE + AF_fr_list_drop + 0x9c] CTX_F.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Theorem pb_list_drop_ro_c : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec B MT G A_list_dropP.
Proof.
intros G HG GRT HRO. apply ldrop_spec_x_AR0.
pose proof (YLX0.lx_AR_laws_x_ARi0_of SEGS B LAWS) as LX0.
assert (HP0 : forall ly S Hp W mem md, ARi0 SEGS B ly S Hp W mem md -> Hp = []) by apply ARi0_hp0.
pose proof (afree_cf_rule_c_x_of_AR0 SEGS B MT CTX_F AFREE) as AFREE0.
pose proof (amemmove_realizes_x_of_AR0 B (SIGMA WS_asan_memmove) AMOVE) as AMOVE0.
eapply pb_list_drop_ro_x; eassumption.
Qed.
End eARc.
Section dAR.
Variable B : asyms.
Variable MT : ameter_ops.
Variable G : list (Z * Z).
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis HG : gx_ok SEGS B G.
Hypothesis GRT : gx_rt B G.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
(* rom_view has to cross the free call: acall_kept keeps an image byte outside the allocator's statics and errno,
   and an owned read-only byte is one of AR's pinned const cells (W_journal.v rom_pinned).  ROM bytes are off G.
   Facts about the instance and G, not about list_drop (rom_out's shape, W_journal.v); lib/A/W_list_drop.v's text. *)
Hypothesis ROMS : forall a, in_rom SEGS a ->
(Exists (in_zr a) (as_owned_static B) -> rom_pinned SEGS B a) /\ ~ (as_errno B <= a < as_errno B + 4) /\ ~ inG G a.
Theorem pb_list_drop : ldrop_spec B MT G A_list_dropP.
Proof.
assert (AFREEc : afree_cf_rule_c SEGS B MT [[BASE + AF_fr_list_drop + 0x9c]])
  by (apply afree_cf_rule_c_weak; exact AFREE).
assert (HCTXc : In [BASE + AF_fr_list_drop + 0x9c] [[BASE + AF_fr_list_drop + 0x9c]]) by (left; reflexivity).
eapply pb_list_drop_c; eassumption.
Qed.
(* the kit's spec at list_drop's B address, in MERGE.md (sha256 0694aca87ccd; internal record) step 2's form (A_list_dropP is BASE + AF_fr_list_drop) *)
Theorem pb_list_drop_at : ldrop_spec B MT G (BASE + AF_fr_list_drop).
Proof. exact pb_list_drop. Qed.
End dAR.
(* The G-generic form over AR: a caller that holds gx_ok, gx_rt and rom_out at its G takes it (lib/A/W_list_drop_top.v's
   form); here a corollary of pb_list_drop_ro_c at the one-entry table. *)
Section eAR.
Variable B : asyms.
Variable MT : ameter_ops.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Hypothesis AFREE : afree_cf_rule SEGS B MT.
Hypothesis AMOVE : amemmove_realizes B (SIGMA WS_asan_memmove).
Theorem pb_list_drop_ro : forall G, gx_ok SEGS B G -> gx_rt B G -> rom_out SEGS B G ->
ldrop_spec B MT G A_list_dropP.
Proof.
intros G HG GRT HRO.
assert (AFREEc : afree_cf_rule_c SEGS B MT [[BASE + AF_fr_list_drop + 0x9c]])
  by (apply afree_cf_rule_c_weak; exact AFREE).
assert (HCTXc : In [BASE + AF_fr_list_drop + 0x9c] [[BASE + AF_fr_list_drop + 0x9c]]) by (left; reflexivity).
exact (pb_list_drop_ro_c B MT LAWS TL [[BASE + AF_fr_list_drop + 0x9c]] AFREEc HCTXc AMOVE G HG GRT HRO).
Qed.
End eAR.
End b.
End a.
