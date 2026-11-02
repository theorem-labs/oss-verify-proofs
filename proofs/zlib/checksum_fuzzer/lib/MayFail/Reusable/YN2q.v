(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Rares Buhai, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/YN2q.v, with its module paths changed. *)
(* Modified by Rares Buhai, 2026-10: changed module paths to the MayFail runtime. *)
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK11.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YK0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YK15.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM06.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YM02.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YP09.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0i.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0f.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0g.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0w.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YO0s.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YO0d.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN03.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN25.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.MayFail.Reusable Require Import YN26.
From OssFuzzTheorems.Proofs.zlib.checksum_fuzzer.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
Local Open Scope mm_scope.
Section a. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Section b.
Variables (f : nat) (A : astate) (g : sptr) (i : Z) (am : ameta).
Hypothesis Hg : MT A g = Some (MUsed am).
Definition nt_mask : Z := Z.lor (am_freed am) (am_avail am).
Definition nt_C1 : bool := (nt_mask + bit i =? ones (am_last am)) && okay_to_free A g am.
Definition nt_preB : M unit :=
if nt_mask =? 0 then
massert (am_sc am <? 48) 6 ;;
hd <- get_head (HActive (am_sc am)) ;;
if osptr_eqb hd (Some g) then ret tt else queue (HActive (am_sc am)) g
else ret tt.
Definition nt_setfreed : M (option (nat * Z)) :=
am' <- getm g ;; setm g (am_set_freed (Z.lor (am_freed am') (bit i)) am') ;; ret None.
Definition nt_TB : itree astate (option (nat * Z) * astate) := bind nt_preB (fun _ => nt_setfreed) A.
Definition nt_deq : M unit :=
match am_next am with
| Some _ =>
massert (am_sc am <? 48) 5 ;;
hd <- get_head (HActive (am_sc am)) ;;
dequeue (HActive (am_sc am)) g ;;
hd' <- get_head (HActive (am_sc am)) ;;
match osptr_eqb hd (Some g), hd' with
| true, Some h => _ <- activate_group h ;; ret tt
| _, _ => ret tt
end
| None => ret tt
end.
Definition nt_free_group : M (option (nat * Z)) :=
am2 <- getm g ;;
(if am_sc am <? 48 then set_usage_of (am_sc am) (usage_of A (am_sc am) - (am_last am2 + 1)) else ret tt) ;;
mi <- (if negb (am_maplen am2 =? 0) then
step_seq ;; record_seq (am_sc am) ;; ret (Some (prid (am_mem am2), am_maplen am2 * 4096))
else
pf <- find_frame (am_mem am2) ;;
amp <- getm (fst pf) ;;
mcheck (slot_is_group (nth_slot amp (snd pf))) 10 ;;
forget_frame (fst pf) (snd pf) ;;
nontrivial_free f (fst pf) (snd pf)) ;;
free_meta g ;;
ret mi.
Definition nt_TA : itree astate (option (nat * Z) * astate) := bind nt_deq (fun _ => nt_free_group) A.
Lemma nt_tree : nontrivial_free (S f) g i A = if nt_C1 then nt_TA else nt_TB.
Proof.
cbn fix beta iota delta [nontrivial_free].
unfold bind at 1. unfold getm at 1. unfold bind at 1, get. cbn [ibind]. unfold MT in Hg. rewrite Hg. unfold ret at 1. cbn [ibind].
unfold bind at 1. unfold get. cbn [ibind]. cbn zeta. fold nt_mask. change ((nt_mask + bit i =? ones (am_last am)) && okay_to_free A g am) with nt_C1.
destruct nt_C1; reflexivity.
Qed.
Definition am_B : ameta := am_set_freed (Z.lor (am_freed am) (bit i)) am.
Definition A_B : astate := upd_meta g (MUsed am_B) A.
Lemma nt_setfreed_eval : nt_setfreed A = IRet (None, A_B).
Proof.
unfold nt_setfreed. unfold bind, getm. unfold bind, get. cbn [ibind]. unfold MT in Hg. rewrite Hg. unfold ret. cbn [ibind]. reflexivity.
Qed.
Lemma nt_TB_mask_nonzero : nt_mask <> 0 -> nt_TB = IRet (None, A_B).
Proof.
intros Hm. unfold nt_TB, nt_preB. replace (nt_mask =? 0) with false by (symmetry; apply Z.eqb_neq; exact Hm).
unfold bind at 1. unfold ret at 1. cbn [ibind]. apply nt_setfreed_eval.
Qed.
Lemma nt_TB_head : nt_mask = 0 -> am_sc am < 48 -> active_hd A (am_sc am) = Some g -> nt_TB = IRet (None, A_B).
Proof.
intros Hm Hsc Hhd. unfold nt_TB, nt_preB. rewrite Hm. cbn [Z.eqb].
unfold massert. replace (am_sc am <? 48) with true by (symmetry; apply Z.ltb_lt; exact Hsc).
unfold get_head. unfold bind, get, ret. cbn [ibind]. unfold active_hd in Hhd. rewrite Hhd.
unfold osptr_eqb. rewrite sptr_eqb_refl. cbn [ibind]. apply nt_setfreed_eval.
Qed.
End b.
End a.
