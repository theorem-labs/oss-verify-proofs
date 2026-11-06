(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: copied from proofs/cgif/cgif_file_fuzzer/lib/A/AD1d.v, with its module paths changed; its addresses are still cgif_file_fuzzer.asan's. *)
(* Modified by Theorem Labs, 2026-10-29: hand-edited for route R1 (cold/h-hpreset-7-r1-memnorm bad7e00334f, 'the start-up invariant SINV0 carries memnorm to the hand-off'; R1 blob 49d6c2c40197); a re-relocation of this file from cgif must be checked against that edit. *)
(* Modified by Theorem Labs, 2026-10: for the world field w_H8 (YA0n), W1 takes the proof H1_H8 of the image-A twin lib/A/PWorldH8.v (fm's form, origin/cold/port-fm-rtprintf-param 3e35620c52e lib/A/AD1d.v:16, :230-231, :235); W0 and tfib_AI pass it as H1H8. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_preset/lib/A/AD1d.v, with its module paths and module names changed; 87 of its 122 lines of code are new or changed and 277 lines of the source are left out. *)
(* The stack-presence fact of plugin-hostd/fuzz_reply's ASan core, for the frame-pointer-chain read site (the unwinder
   reads the stack between the current sp and the stack top through aview, which off the image is presence).
   Construction (a Theorem Labs lane's ruling, 2026-10-29): state presence over a FIXED range [usp - stack_max_size, usp), usp the
   ENTRY sp, discharge it once at the start-up hand-off, and forward it along any run by monotonicity alone.
   - stk_pres lo hi H m: every byte of [lo, hi) is apresent (YG0n.v:28: not hidden and in memory).
   - stk_pres_grows: kept when the hidden set only shrinks (hsub H' H, the world order wle, YA0n.v:25) and the visible
     memory only grows (mem_grows, which every machine run gives: YI04.v:67 msteps_mem_grows, used by the SRr_chain*
     lemmas of YCbq / YCbqG); stk_pres_world is the same in world form.
   - apresent_view_off_img: off the image, apresent H m a <-> aview segs H m a <> None (mbyte falls back to seg_rom,
     which is None there), so the view form of the premise and the presence form are the same fact on the stack.
   - handoff_stk_pres: at a start-up hand-off whose certificate (YA0e cs_ok) knows the write KWr (SA e (-8388608))
     (ELit 8388608) and whose hidden set is false from TOP = uE E e - 8388608 up, every byte of [TOP, uE E e) is present:
     ho_wr (YA0j.v:242) gives store_ok there, hence wview <> None, hence a byte, as no segment is there.
   - tfib_handoff_stk_pres: the same at each of fuzz_reply.asan's 50 hand-off states (AB01.v), for W1's hidden set
     AD2i.H1 (= AD1d.W0's), over [usp - stack_max_size, usp): A/AD2i.v:79 KWR_STACK is known in every hand-off state
     (kwr_stack_all, vm_compute), and H1 is false from TOP up (AD2i.v:509 with YA0e's hid).
   Not covered: [usp, ly_top), the entry image above the entry sp (at most 3935 bytes, AD1g.v:988 uTopRel): the hand-off
   certificate states only its argH0 part (YA02.v:81-84, AB1n.v:82). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.plugin_hostd.fuzz_reply.images Require Import Asan.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK11 YP0m YP09 YP0l YP08 YP03 YN3q YK00 YK04 YA0i YA0n YK0c YK0d YK0e YK0f YK09 YA01 YA0c YA0e YA0d YA02 YA0j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK1b YG0n.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A Require Import AB12 AB1h AB13 AB01 AD2j AD2i.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YD1h.
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

(* ---- 4. fuzz_reply.asan's hand-off states ---- *)
Lemma kwr_stack_all : forallb (kn_mem KWR_STACK) HS_tfib_list = true.
Proof. vm_compute. reflexivity. Qed.
Lemma kwr_stack_hs : forall h ch, HS_tfib h = Some ch -> kn_mem KWR_STACK ch = true.
Proof. intros h ch Hh. exact (proj1 (forallb_forall _ _) kwr_stack_all ch (HS_tfib_In h ch Hh)). Qed.
Lemma tfib_seg_none_high : forall a, KHI <= a < 2 ^ 64 -> find_segment TSEGS a 1 = None.
Proof.
intros a Ha. unfold KHI in Ha. pose proof (tfib_in_hull (Z_to_bv 64 a)) as X. rewrite u64_lit in X by lia. apply X.
unfold APSG.in_hull. cbn [img_lo img_hi TFIB]. unfold KHI. apply andb_false_iff. right. apply Z.ltb_ge. lia.
Qed.
Section t. Context {fx : YK11.FPState}.
Variables (sp : word) (rdraw : EntryDraw) (brk : word) (inp : ProcInput).
Hypothesis Hsp : valid_sp sp.
Hypothesis Hva : valid_argv (in_argv inp).
Hypothesis Hve : valid_envp (in_envp inp).
Hypothesis Hfit : entry_stack_fits sp (in_argv inp) (in_envp inp).
Variable h : nat.
Variables (ch : acs) (E : env) (R : bvmap 5 word) (FULL : word -> option byte) (model : Model).
Hypothesis Hch : HS_tfib h = Some ch.
#[local] Notation argv := (in_argv inp).
#[local] Notation envp := (in_envp inp).
#[local] Notation uid := (in_uid inp).
#[local] Notation hw := (in_hwcap inp).
#[local] Notation SINV := (YA02.SINV0 TSEGS TPH sp rdraw brk argv envp uid hw).
#[local] Notation argH := (YA02.argH0 TPH sp rdraw argv envp uid hw).
#[local] Notation TOP := (YA02.TOP sp).
Hypothesis HC : cs_ok TSEGS TFIB YA02.LIMIT TOP SINV argH (in_fs inp) E ch R FULL model.
#[local] Notation usp := (bv_unsigned sp).
Lemma tfib_uS0 : uE E eSp0 = usp.
Proof.
pose proof (YA02.SINV0_sp0 TSEGS TPH sp rdraw brk argv envp uid hw Hsp Hva Hve Hfit E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as X.
rewrite eSp0_e_sp0. unfold YA02.TOP in X. lia.
Qed.
Lemma H1_false_high : forall w : word, TOP <= bv_unsigned w -> AD2i.H1 sp rdraw inp ch E model w = false.
Proof.
intros w Hw. unfold AD2i.H1. destruct (argH E w) eqn:HaH.
- cbn [negb]. rewrite andb_false_r. reflexivity.
- assert (Hh : hid TFIB TOP argH E ch model w = false).
  { unfold hid. rewrite HaH. cbn [orb]. unfold vis. rewrite (proj2 (Z.leb_le _ _) Hw). rewrite orb_true_r. reflexivity. }
  rewrite Hh. reflexivity.
Qed.
Theorem tfib_handoff_stk_pres : stk_pres (usp - stack_max_size) usp (AD2i.H1 sp rdraw inp ch E model) FULL.
Proof.
pose proof tfib_uS0 as U. pose proof Hsp as (L & Hh & _). unfold sp_window_lo in L. unfold sp_window_hi in Hh.
change stack_max_size with 8388608. replace (usp - 8388608) with TOP by (unfold YA02.TOP; lia). rewrite <- U.
apply (handoff_stk_pres TSEGS TFIB YA02.LIMIT TOP SINV argH (in_fs inp) E ch R FULL model HC eSp0 (kwr_stack_hs h ch Hch)).
- unfold YA02.TOP. lia.
- unfold YA02.TOP. lia.
- intros a Ha. apply tfib_seg_none_high. unfold YA02.TOP in Ha. unfold KHI. lia.
- exact H1_false_high.
Qed.
End t.
