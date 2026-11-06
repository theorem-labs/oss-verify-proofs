(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1d.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob 49d6c2c40197); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W1 takes the proof H1_H8 of the image-A twin lib/A/PWorldH8.v (fm's form, origin/cold/port-fm-rtprintf-param 3e35620c52e lib/A/AD1d.v:16, :230-231, :235); W0 and tfib_AI pass it as H1H8. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1d.v, with its module paths and module names changed; 87 of its 122 lines of code are new or changed and 277 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/plugin-hostd/fuzz_reply/lib/A/AStkPres.v; 10 of its 78 lines of code are new or changed and 54 lines of the source are left out. *)
(* The stack-presence fact, image-independent part (used by A/AStkPres.v for fuzz_reply.asan and by image B's twin).
   Construction (a Theorem Labs lane's ruling, 2026-10-29): state presence over a FIXED range [usp - stack_max_size, usp), usp the
   ENTRY sp, discharge it once at the start-up hand-off, and forward it along any run by monotonicity alone.
   - stk_pres lo hi H m: every byte of [lo, hi) is apresent (YG0n.v:28: not hidden and in memory).
   - stk_pres_grows: kept when the hidden set only shrinks (hsub H' H, the world order wle, YA0n.v:25) and the visible
     memory only grows (mem_grows, which every machine run gives: YI04.v:67 msteps_mem_grows, used by the SRr_chain*
     lemmas of YCbq / YCbqG); stk_pres_world is the same in world form; stk_pres_window gives the moving window.
   - apresent_view_off_img: off the image, apresent H m a <-> aview segs H m a <> None (mbyte falls back to seg_rom,
     which is None there), so the view form of the premise and the presence form are the same fact on the stack.
   - handoff_stk_pres: at a start-up hand-off whose certificate (YA0e cs_ok) knows the write KWr (SA e (-8388608))
     (ELit 8388608) and whose hidden set is false from TOP = uE E e - 8388608 up, every byte of [TOP, uE E e) is present:
     ho_wr (YA0j.v:242) gives store_ok there, hence wview <> None, hence a byte, as no segment is there. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP09 YP0l YP08 YP03 YN3q YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK1b YG0n.
Import ListNotations.
Import AX2. Import AX2B. Import AX2S. Import APC. Import APG. Import APSG.
Unset Lia Cache. Unset Nia Cache.
Open Scope Z_scope.
(* ---- 1. the fact and its monotonicity ---- *)
Definition stk_pres (lo hi : Z) (H : word -> bool) (mem : word -> option byte) : Prop :=
  forall a, lo <= a < hi -> apresent H mem a.
Lemma stk_pres_grows : forall lo hi (H H' : word -> bool) (m m' : word -> option byte),
  stk_pres lo hi H m -> hsub H' H -> mem_grows (mrestrict H m) (mrestrict H m') -> stk_pres lo hi H' m'.
Proof.
intros lo hi H H' m m' HP Hs Hg a Ha. destruct (HP a Ha) as [Hh [b Hb]]. split.
- destruct (H' (Z_to_bv 64 a)) eqn:E; [|reflexivity]. rewrite (Hs _ E) in Hh. discriminate Hh.
- assert (X : mrestrict H m (Z_to_bv 64 a) <> None) by (unfold mrestrict; rewrite Hh, Hb; discriminate).
  specialize (Hg _ X). unfold mrestrict in Hg. rewrite Hh in Hg.
  destruct (m' (Z_to_bv 64 a)) as [b'|]; [exists b'; reflexivity | exfalso; apply Hg; reflexivity].
Qed.
Lemma stk_pres_world : forall segs lo hi (W W' : world segs) (m m' : word -> option byte),
  stk_pres lo hi (w_H W) m -> wle W W' -> mem_grows (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> stk_pres lo hi (w_H W') m'.
Proof. intros segs lo hi W W' m m' HP Hw Hg. exact (stk_pres_grows lo hi (w_H W) (w_H W') m m' HP Hw Hg). Qed.
Lemma stk_pres_sub : forall lo hi lo' hi' H m, stk_pres lo hi H m -> lo <= lo' -> hi' <= hi -> stk_pres lo' hi' H m.
Proof. intros lo hi lo' hi' H m HP H1 H2 a Ha. apply HP. lia. Qed.
(* at the read site: the moving window [s, hi) inside the fixed range *)
Lemma stk_pres_window : forall lo hi H m s, stk_pres lo hi H m -> lo <= s -> forall a, s <= a < hi -> apresent H m a.
Proof. intros lo hi H m s HP Hs a Ha. apply HP. lia. Qed.
(* extending the range upward by bytes that are visible and in memory (the start-up kit's fact for the entry image
   [usp, ly_top) above the entry sp) *)
Lemma stk_pres_extend : forall lo mid hi (H : word -> bool) (m : word -> option byte),
  stk_pres lo mid H m ->
  (forall a, mid <= a < hi -> H (Z_to_bv 64 a) = false /\ m (Z_to_bv 64 a) <> None) ->
  stk_pres lo hi H m.
Proof.
intros lo mid hi H m HP HX a Ha. destruct (Z_lt_le_dec a mid) as [Hl|Hl].
- apply HP. lia.
- destruct (HX a ltac:(lia)) as [Hh Hm]. split; [exact Hh|].
  destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity | exfalso; apply Hm; reflexivity].
Qed.

(* ---- 2. presence and the view are the same fact off the image ---- *)
Lemma apresent_view_off_img : forall segs (H : word -> bool) (m : word -> option byte) a,
  seg_rom segs (Z_to_bv 64 a) = None -> (apresent H m a <-> aview segs H m a <> None).
Proof.
intros segs H m a Hr. unfold aview, mbyte, mrestrict, apresent. split.
- intros [Hh [b Hb]]. rewrite Hh, Hb. discriminate.
- destruct (H (Z_to_bv 64 a)) eqn:Eh.
  + rewrite Hr. intros X. exfalso. apply X. reflexivity.
  + destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em.
    * intros _. split; [reflexivity | exists b; reflexivity].
    * rewrite Hr. intros X. exfalso. apply X. reflexivity.
Qed.

(* ---- 3. the discharge at a start-up hand-off ---- *)
Section h. Context {fx : YK11.FPState}.
Lemma handoff_stk_pres : forall SEGS A LIMIT TOP SINV argH FS0 E ch R FULL model,
  cs_ok SEGS A LIMIT TOP SINV argH FS0 E ch R FULL model ->
  forall e, kn_mem (KWr (SA e (-8388608)) (ELit 8388608)) ch = true ->
  TOP = uE E e - 8388608 -> 0 <= TOP ->
  (forall a, TOP <= a < uE E e -> find_segment SEGS a 1 = None) ->
  forall H : word -> bool, (forall w : word, TOP <= bv_unsigned w -> H w = false) ->
  stk_pres TOP (uE E e) H FULL.
Proof.
intros SEGS A LIMIT TOP SINV argH FS0 E ch R FULL model HC e Hk ET T0 Hseg H HH a Ha.
assert (Ue : uE E e < 2 ^ 64) by (unfold uE; pose proof (u64_range (edenot E e)); lia).
pose proof (ho_wr SEGS A LIMIT TOP SINV argH FS0 E ch R FULL model HC _ _ Hk (a - TOP) 1%nat ltac:(lia)) as W.
unfold elenZ in W. cbn [edenot] in W. rewrite u64_lit in W by lia. specialize (W ltac:(lia)).
unfold estart in W. cbn [a_base a_off] in W.
change (bv_unsigned (edenot E e)) with (uE E e) in W.
replace (uE E e + -8388608 + (a - TOP)) with a in W by lia.
match type of W with RiscvSemantics.store_ok ?S ?M ?A 1 = true =>
  assert (Wv : wview S M A <> None) by (cbn [RiscvSemantics.store_ok] in W; destruct (wview S M A); [discriminate | discriminate W]);
  unfold wview in Wv;
  match type of Wv with context [find_segment ?S0 ?z ?n] =>
    replace (find_segment S0 z n) with (@None Segment) in Wv by
      (symmetry; replace z with a by (rewrite ?u64_lit by lia; reflexivity); exact (Hseg a Ha)) end;
  destruct (M A) as [b|] eqn:EM; [|exfalso; apply Wv; reflexivity] end.
cbv [Mr mrestrict] in EM.
match type of EM with (if ?c then _ else _) = _ => destruct c end; [discriminate EM|].
split; [apply HH; rewrite u64_lit by lia; lia | exists b; exact EM].
Qed.
End h.
