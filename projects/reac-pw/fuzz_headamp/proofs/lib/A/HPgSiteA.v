(* Modified by Theorem Labs, 2026-10: proofs/reac-pw/fuzz_role/lib/A/RPgSiteA.v at commit 0de5d668c87 for reac-pw/fuzz_headamp image A: module paths changed, the rl_ / role_ prefixes renamed to hd_ / headamp_, role's one allocator site and one cut site replaced by headamp's three of each, role's string, cell and table premises replaced by headamp's parse and harness literals, read-only doubles and stack-guard cells, and the call-site lemmas of the parse contract at its two calls and of the eight check functions added. *)
(* reac-pw/fuzz_headamp image A (fuzz_headamp.asan, pinned sha256
   f3e0669d2819724922df0556b11c2dcd22d1e16fe7e0fe1535ce784b34436c47): the call-site lemmas of rule 1j-bis for the
   texts of lib/A/HPgCSpec.v, at the states those texts already state (the segment contracts' starts and ends, a
   callee contract's own premise hd_pre at its call, and the parse contract's post), with image A's record
   HPgImgA.headamp_himg_A. Each lemma shows that the stated state supplies a premise of the next call's contract.
   Proves no function (kind: statement text).
   - hd_len_bounds: the length of the pod the harness allocates, 8 <= len <= 5440 (Pod/Spa.v buf_header of the
     record Pod/Model.v pod_build makes).
   - headamp_A_site_malloc_pod / _out / _first: at C2 (0x82e60), C4 (0x82e94) and C6 (0x83740), the `jal` of the
     three allocator calls, a0 = len + (len == 0), 3 cap + 3 and 3 max(rc, 0) + (3 max(rc, 0) == 0) satisfy the
     request premise `0 <= n < MALLOC_MAX` of the allocator's contract (lib/Reusable/YG0d.v amalloc_realizes).
   - headamp_A_site_cut3 / cut5 / cut7: at C3, C5 and C7 (after each allocator call returns) the image's list
     holds when the list at the call held, the call left a0 = the new block, kept every other register the list
     names and kept the real-frame cells the list names.
   - headamp_A_site_strs: at every segment's start (hd_seg_pre), the string, cell and guard premises of the
     callee contracts M03 and M04b call: the parse's four literals (hd_parse_args at akey = 0x21460, aph = 0x21480,
     apad = 0x214a0, asens = 0x214c0), the harness's own strncmp literal 0x20f00 and strcmp literals 0x21340,
     0x21360, 0x21380 (the same four texts, Pod/Headamp.v HA_PREFIX, NAME_PHANTOM, NAME_PAD, NAME_SENS), the
     parse's two read-only doubles (HPgImgA.headamp_A_dcs) and the stack-guard cells (0x9cff8, 0x5f7d90).
   - headamp_A_site_block / _frame: at any callee's call (hd_pre), a block live at the call and a side-stack frame
     the harness holds lie below the caller's stack window, so every range inside them is outside the callee's
     own stack (HPgCSpec.hd_off_stack), and a range inside a live block has its shadow marked usable;
     headamp_A_site_frame_at: the frame for locals has the same address at every state of the harness's journal;
     headamp_A_site_block_app / _frame_app / hd_app_F: a range inside such a block or frame is application memory
     outside the image (HPgCSpec.hd_app_rng), which each of the eight check lemmas below also concludes.
   - headamp_A_site_no_overrun: check_no_overrun at 0x82ef8 (a0 = out + 3 cap) after the parse at 0x82eec, which
     writes only out[0, 3 n) with n <= cap: the guard bytes the harness wrote over the whole out block are still
     at out + 3 cap.
   - headamp_A_site_count: check_count at 0x82f08 (a0 = rc, a1 = cap, a2 = res = F + 0x180), from the parse's
     answer_ok (Pod/Headamp.v parse_props_total), its keys bound (parse_props_keys) and the res bytes of its post;
     res is 4-aligned (the frame for locals is 32-aligned).
   - headamp_A_site_cells_valid: check_cells_valid at 0x82f14 (a0 = out, a1 = rc), from answer_ok and the out
     bytes of the parse's post; out lies below 2^47.
   - headamp_A_site_plain: check_plain at 0x83790 (a0 = the second parse's answer, a1 = rc, a2 = out,
     a3 = first): the two parses answer the same o on the same bytes and cap, so a0 = a1 and out and first hold
     the same 3 rc bytes; both blocks lie below 2^47.
   - headamp_A_site_parse_args / headamp_A_site_parse_args_plain: every premise of the parse contract
     (HPgCSpec.hd_parse_args) at M03's call 0x82eec (R = F + 0x180) and at M04b's call 0x83780 (R = 0), from the
     segment's start state and its contract's own premises, the call's hd_pre and the walk's memory fact hd_kept
     between the two states (headamp_A_site_parse_core for both): the pod block (live, made since the journal's
     start, a whole number of words, apart from out, res and errno), the out block, res in the frame for locals,
     and the literals, doubles, guard cells, errno cell and read-only bytes carried from the segment's start.
   - headamp_A_site_object / _cells / _keys / _refusal: check_object at 0x836ac, check_cells at 0x836bc,
     check_keys at 0x836cc and check_refusal at 0x836d8 (res = F + 0x180, x = F + 0x1a0): on the uncorrupted
     record the parse's answer is expect_of's (hd_parse_expect, Pod/Headamp.v parse_props_build), so x's words
     (Spec/HeadBytes.v x_bytes) and res's words agree; x's granules are in scope (headamp_A_shX).
   - headamp_A_img_bytes_rsegs, headamp_A_segs_low, headamp_A_relro_img: the parse lemmas' image hypotheses at
     image A's own segments (lib/A/Img0.v). *)
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Sem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK11 YK14 YK0s YK15 YK18 YP09 YI04 YI08 YN3v YI00 YI0m YI09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YK04 YA0i YA0n.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YO09.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require Import YM05.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Reusable Require YK0o YO0f YG0q.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Lib Require Mem.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Pod Require Model Layout Spa Headamp.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.Spec Require Import HeadBytes.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Import HPgBase HPgCSpec HPgImgA.
From OSSVerify.Proofs.reac_pw.fuzz_headamp.lib.A Require Img0 HPgSat.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.

(* ===================== C2, C4, C6: the three allocator requests ===================== *)
Lemma hd_len_bounds : forall rest, 8 <= hd_len rest <= 5440.
Proof.
intros rest. unfold hd_len.
destruct (Model.pod_build rest) as [r rest'] eqn:E. cbn [fst].
pose proof (Spa.buf_header r (Model.pod_build_wf rest r rest' E)) as (_ & _ & _ & H). exact H.
Qed.

Lemma headamp_A_site_malloc_pod : forall (e : hd_env) (rest : list byte), e_len e = hd_len rest ->
hd_xv e XLenNZ = e_len e /\ 8 <= e_len e <= 5440 /\ 0 <= hd_xv e XLenNZ < MALLOC_MAX.
Proof.
intros e rest He. pose proof (hd_len_bounds rest) as Hb. rewrite <- He in Hb. cbn [hd_xv].
destruct (Z.eqb_spec (e_len e) 0) as [E0|E0]; [lia|].
unfold MALLOC_MAX. lia.
Qed.

Lemma headamp_A_site_malloc_out : forall e : hd_env, 0 <= e_cap e <= 9 ->
hd_xv e XCap33 = 3 * e_cap e + 3 /\ 3 <= hd_xv e XCap33 <= 30 /\ 0 <= hd_xv e XCap33 < MALLOC_MAX.
Proof. intros e Hc. cbn [hd_xv]. unfold MALLOC_MAX. lia. Qed.

Lemma headamp_A_site_malloc_first : forall e : hd_env, -1 <= e_rc e <= e_cap e -> 0 <= e_cap e <= 9 ->
0 < hd_xv e XRc3NZ <= 27 /\ 0 <= hd_xv e XRc3NZ < MALLOC_MAX.
Proof.
intros e Hr Hc. cbn [hd_xv]. unfold MALLOC_MAX.
destruct (Z.eqb_spec (3 * Z.max (e_rc e) 0) 0); lia.
Qed.

(* ===================== C3, C5, C7: the values after each allocator call returns ===================== *)
Ltac hd_in := solve [cbn [In]; repeat (first [left; reflexivity | right])].

Section c3. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.
(* A cut list holds in a new state when every register it names and every 8-byte cell it names is as before. *)
Lemma hd_cut_keep : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env) L,
hd_cut segs H mem regs e L ->
Forall (fun f => match fst f with
  | LReg r => getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)
  | LCell b o => forall i, 0 <= i < 8 ->
      mbyte segs (mrestrict H mem') (hd_xv e b + o + i) = mbyte segs (mrestrict H mem) (hd_xv e b + o + i)
  end) L ->
hd_cut segs H mem' regs' e L.
Proof.
intros H mem mem' regs regs' e L. unfold hd_cut.
induction L as [|[l x] L IH]; intros HC HK; [constructor|].
apply Forall_cons_iff in HC as [HC1 HC]. apply Forall_cons_iff in HK as [HK1 HK].
apply Forall_cons; [|exact (IH HC HK)].
cbn [fst snd] in HC1, HK1 |- *. destruct l as [r|b o]; cbn [hd_at] in HC1 |- *.
- rewrite HK1. exact HC1.
- intros kk Hk. rewrite (HK1 (Z.of_nat kk)) by lia. exact (HC1 kk Hk).
Qed.

Ltac hd_keep Hregs Hcells :=
  repeat (apply Forall_cons;
    [cbv beta; cbn [fst hd_xv];
     first [ (apply Hregs; [lia | hd_in])
           | (intros i Hi; apply Hcells; [hd_in | exact Hi]) ] |]);
  apply Forall_nil.

Lemma headamp_A_site_cut3 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L2 headamp_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (e_pod e) ->
(forall r, r <> 10 -> In r [8; 9; 18; 19; 20; 21; 23; 24; 26] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x20; 0x28; 0x40; 0x60; 0x90; 0xa0; 0xf0] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L3 headamp_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L2 hi_L3 headamp_himg_A] in HC |- *. unfold headamp_A_L23 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep H mem mem' regs regs' e _ HC _).
hd_keep Hregs Hcells.
Qed.

Lemma headamp_A_site_cut5 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L4 headamp_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (e_out e) ->
(forall r, r <> 10 -> In r [8; 9; 18; 19; 20; 21; 22; 23; 25; 26; 27] ->
 getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x20; 0x40; 0x60; 0x90; 0xa0; 0xf0] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L5 headamp_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L4 hi_L5 headamp_himg_A] in HC |- *. unfold headamp_A_L45 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep H mem mem' regs regs' e _ HC _).
hd_keep Hregs Hcells.
Qed.

Lemma headamp_A_site_cut7 : forall H (mem mem' : word -> option byte) (regs regs' : bvmap 5 word) (e : hd_env),
hd_cut segs H mem regs e (hi_L6 headamp_himg_A) ->
getr regs' (Z_to_bv 5 10) = w64 (e_first e) ->
(forall r, r <> 10 -> In r [8; 9; 19; 21; 22; 24; 25; 27] -> getr regs' (Z_to_bv 5 r) = getr regs (Z_to_bv 5 r)) ->
(forall o, In o [0x20; 0x60; 0xf0; 0x110; 0x118] -> forall i, 0 <= i < 8 ->
 mbyte segs (mrestrict H mem') (e_R e + o + i) = mbyte segs (mrestrict H mem) (e_R e + o + i)) ->
hd_cut segs H mem' regs' e (hi_L7 headamp_himg_A).
Proof.
intros H mem mem' regs regs' e HC H10 Hregs Hcells.
unfold hd_cut in HC |- *. cbn [hi_L6 hi_L7 headamp_himg_A] in HC |- *. unfold headamp_A_L67 in HC |- *.
apply Forall_cons_iff in HC as [_ HC]. apply Forall_cons; [exact H10|].
refine (hd_cut_keep H mem mem' regs regs' e _ HC _).
hd_keep Hregs Hcells.
Qed.
End c3.

(* ===================== M03's and M04b's callees: strings, cells and guard at a segment's start ===================== *)
Section s. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.
Lemma headamp_A_site_strs : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc sh
RLO RHI e pos,
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos ->
hd_cstr segs (w_H W) memc 0x21460 (hd_zbytes Headamp.HA_PREFIX) /\
hd_cstr segs (w_H W) memc 0x21480 (hd_zbytes Headamp.NAME_PHANTOM) /\
hd_cstr segs (w_H W) memc 0x214a0 (hd_zbytes Headamp.NAME_PAD) /\
hd_cstr segs (w_H W) memc 0x214c0 (hd_zbytes Headamp.NAME_SENS) /\
hd_cstr segs (w_H W) memc 0x20f00 (hd_zbytes Headamp.HA_PREFIX) /\
hd_cstr segs (w_H W) memc 0x21340 (hd_zbytes Headamp.NAME_PHANTOM) /\
hd_cstr segs (w_H W) memc 0x21360 (hd_zbytes Headamp.NAME_PAD) /\
hd_cstr segs (w_H W) memc 0x21380 (hd_zbytes Headamp.NAME_SENS) /\
hd_ro_cells segs (w_H W) memc headamp_A_dcs /\
hd_guard_ok (aview segs (w_H W) memc) 0x9cff8 0x5f7d90.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos HP.
destruct HP as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HS & HC & HGd & _).
cbn [hi_strs hi_cells hi_gotw hi_guard headamp_himg_A] in HS, HC, HGd.
unfold hd_ro_cells in HC.
rewrite headamp_A_key_text. destruct headamp_A_param_texts as (Tph & Tpad & Tsens). rewrite Tph, Tpad, Tsens.
assert (Hs : forall a s, In (a, s) headamp_A_strs -> hd_cstr segs (w_H W) memc a s)
  by (intros a s Hin; exact (proj1 (Forall_forall _ _) HS (a, s) Hin)).
assert (Hc : forall a v, In (a, v) headamp_A_cells -> val_mem segs (mrestrict (w_H W) memc) a 8 v)
  by (intros a v Hin; exact (proj1 (Forall_forall _ _) HC (a, v) Hin)).
do 8 (split; [apply Hs; unfold headamp_A_strs; hd_in|]).
split; [|exact HGd].
unfold hd_ro_cells, headamp_A_dcs.
apply Forall_cons; [cbv beta; cbn [fst snd]; apply Hc; unfold headamp_A_cells; hd_in|].
apply Forall_cons; [cbv beta; cbn [fst snd]; apply Hc; unfold headamp_A_cells; hd_in|].
apply Forall_nil.
Qed.
End s.

(* ===================== the four check functions the parse's answer feeds ===================== *)
(* Byte facts. *)
Lemma hd_shr_mod : forall x a b, 0 <= b -> b + 8 <= a -> Z.shiftr (x mod 2 ^ a) b mod 256 = Z.shiftr x b mod 256.
Proof.
intros x a b Hb Hab. change 256 with (2 ^ 8).
apply Z.bits_inj'. intros n Hn.
destruct (Z_lt_le_dec n 8) as [Hn8|Hn8].
- rewrite !Z.mod_pow2_bits_low by lia. rewrite !Z.shiftr_spec by lia.
  rewrite Z.mod_pow2_bits_low by lia. reflexivity.
- rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
Qed.

Lemma hd_nth_le_bytes : forall n z k, (k < n)%nat ->
nth k (map (fun b : byte => bv_unsigned b) (Z_to_le_bytes n z)) 0 = Z.shiftr z (8 * Z.of_nat k) mod 256.
Proof.
induction n as [|n IH]; intros z k Hk; [lia|].
destruct k as [|k]; cbn [Z_to_le_bytes map nth].
- rewrite Z_to_bv_unsigned. replace (8 * Z.of_nat 0) with 0 by lia. rewrite Z.shiftr_0_r.
  unfold bv_wrap, bv_modulus. reflexivity.
- rewrite IH by lia. rewrite Z.shiftr_shiftr by lia. f_equal. f_equal. lia.
Qed.

Lemma hd_nth_guard : forall n i, (i < n)%nat -> nth i (hd_zbytes (repeat GUARD_BYTE n)) 0 = bv_unsigned GUARD_BYTE.
Proof.
unfold hd_zbytes. induction n as [|n IH]; intros i Hi; [lia|].
destruct i as [|i]; cbn [repeat map nth]; [reflexivity | apply IH; lia].
Qed.

Section k. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* A value kept byte by byte under the reader. *)
Lemma hd_val_mem_kept : forall H H' (m m' : word -> option byte) a n v,
(forall i, 0 <= i < Z.of_nat n -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
val_mem segs (mrestrict H m) a n v -> val_mem segs (mrestrict H' m') a n v.
Proof.
intros H H' m m' a n v Hk Hv kk Hkk. specialize (Hv kk Hkk). specialize (Hk (Z.of_nat kk) ltac:(lia)).
cbv beta delta [aview] in Hk. rewrite Hv in Hk. cbn [option_map] in Hk.
destruct (mbyte segs (mrestrict H' m') (a + Z.of_nat kk)) as [b|] eqn:Eb; try rewrite Eb in Hk;
  cbn [option_map] in Hk; [|discriminate Hk].
injection Hk as Hb. f_equal. apply bv_eq. exact Hb.
Qed.

(* The 4-byte little-endian value at a, from the bytes of le4. *)
Lemma hd_garr8_le4 : forall m a v,
garr8 segs m a (hd_zbytes (Mem.le4 (Z_to_bv 64 v))) -> val_mem segs m a 4 (v mod 2 ^ 32).
Proof.
intros m a v Hg kk Hk.
assert (Hl : (kk < length (hd_zbytes (Mem.le4 (Z_to_bv 64 v))))%nat)
  by (unfold hd_zbytes; rewrite length_map, Mem.length_le4; exact Hk).
rewrite (garr8_mbyte segs m a _ kk Hg Hl). f_equal.
apply Mem.Z_to_bv8_mod. unfold hd_zbytes, Mem.le4. rewrite hd_nth_le_bytes by lia.
unfold YO0f.le_byte. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (Z.of_N 64) with 64.
rewrite !hd_shr_mod by lia. reflexivity.
Qed.

(* At any callee's call (its premise hd_pre): a block live at the call lies below the caller's stack window; every
   range inside it has its shadow marked usable and lies outside the callee's own stack. *)
Lemma headamp_A_site_block : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc p n,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (p, n) (ablocks B lyc Sc) ->
4096 <= p /\ p + req_size n <= sp0 - STK /\ sp0 - STK <= spZ regs - T /\ 0 <= STK /\ sp0 <= 2 ^ 47 /\
(forall a m, p <= a -> a + m <= p + req_size n ->
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF a m /\ hd_off_stack regs T a m).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc p n HP Hin.
destruct HP as (HJ & _ & _ & _ & _ & _ & Hlo & _ & _).
destruct HJ as (HAR & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & HSTK & Hc1 & Hc2 & Hc3 & Hc4 & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc p n HAR Hin) as (_ & Hp4 & Hpc & _).
split; [exact Hp4|]. split; [lia|]. split; [exact Hlo|]. split; [exact HSTK|]. split; [lia|].
intros a m Ha Ham. split.
- exact (YCbq.range_addressable_of_block segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc p n a m HAR Hin Ha Ham).
- intros x Hx. lia.
Qed.

(* At any callee's call: a side-stack frame the harness holds is 32-aligned and lies below the caller's stack
   window, so every range inside it lies outside the callee's own stack. *)
Lemma headamp_A_site_frame : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc
cid pos,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (cid, pos) own ->
frame_addr lyc cid pos mod 32 = 0 /\ 4096 <= frame_addr lyc cid pos /\
frame_addr lyc cid pos + fs_frame_bytes cid <= sp0 - STK /\
(forall a m, frame_addr lyc cid pos <= a -> a + m <= frame_addr lyc cid pos + fs_frame_bytes cid ->
 hd_off_stack regs T a m).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc cid pos HP Hown.
destruct HP as (HJ & _ & _ & _ & _ & _ & Hlo & _ & _).
destruct HJ as (HAR & _ & _ & _ & _ & Hfr & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hc1 & Hc2 & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (al_frames _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc cid pos HAR Hin) as (Hal & _).
destruct (al_sep _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc HAR) as (_ & Hf).
pose proof (proj1 (Forall_forall _ _) Hf (cid, pos) Hin) as (Hf1 & Hf2). cbn [fst snd] in Hf1, Hf2.
split; [exact Hal|]. split; [exact Hf1|]. split; [lia|].
intros a m Ha Ham x Hx. lia.
Qed.

(* HPgCSpec.hd_app_rng for a range inside a block live at a callee's call: the block is application memory
   (YG0d.v AR_blocks_law, in_app; YG0f.v in_app_sub) outside the image (AR_client_img_law). *)
Lemma headamp_A_site_block_app : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc
p n a m,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (p, n) (ablocks B lyc Sc) -> p <= a -> 0 <= m -> a + m <= p + req_size n -> hd_app_rng segs a m.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc p n a m HP Hin Ha Hm Ham.
destruct HP as (HJ & _). destruct HJ as (HAR & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc p n HAR Hin) as (_ & _ & _ & Happ & _).
split; [exact (in_app_sub _ _ _ _ Happ Ha Hm Ham)|].
intros x Hx.
assert (Hcin : exists p0 n0, In (p0, n0) (ablocks B lyc Sc) /\ p0 <= x < p0 + req_size n0)
  by (exists p, n; split; [exact Hin | lia]).
exact (proj2 (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc x HAR (or_introl Hcin))).
Qed.

(* HPgCSpec.hd_app_rng for a range inside a side-stack frame the caller holds (YG0d.v AR_frames_law through
   YCbq.v frames_bounds, in_app; AR_client_img_law). *)
Lemma headamp_A_site_frame_app : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc
cid pos a m,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (cid, pos) own -> frame_addr lyc cid pos <= a -> 0 <= m -> a + m <= frame_addr lyc cid pos + fs_frame_bytes cid ->
hd_app_rng segs a m.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc cid pos a m HP Hown Ha Hm Ham.
destruct HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hin : In (cid, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
destruct (YCbq.frames_bounds segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc cid pos HAR Hin) as (_ & _ & Happ).
split; [exact (in_app_sub _ _ _ _ Happ Ha Hm Ham)|].
intros x Hx.
assert (Hcin : exists cid0 pos0, In (cid0, pos0) (frames Sc) /\
  frame_addr lyc cid0 pos0 <= x < frame_addr lyc cid0 pos0 + fs_frame_bytes cid0)
  by (exists cid, pos; split; [exact Hin | lia]).
exact (proj2 (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc x HAR (or_intror (or_introl Hcin)))).
Qed.

(* The same for the harness's frame for locals F (class 4, 1024 bytes). *)
Lemma hd_app_F : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc (e : hd_env) pos,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
forall a m, e_F e <= a -> 0 <= m -> a + m <= e_F e + 1024 -> hd_app_rng segs a m.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc e pos HP Hown HF a m H1 H2 H3.
apply (headamp_A_site_frame_app STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc _ _ a m HP Hown).
- rewrite <- HF. exact H1.
- exact H2.
- rewrite <- HF. change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024. exact H3.
Qed.

(* The frame for locals has the same address at every state of the harness's journal: two journals from the same
   entry (ly, S) end at layouts with the entry's frame base (YG0f.v layout_le keeps ly_F). So hd_seg_pre's
   `e_F e = frame_addr lyc (hi_cid I) pos` at a segment's start gives the same equation at any callee's call inside
   it, the form headamp_A_site_no_overrun and headamp_A_site_count take. *)
Lemma headamp_A_site_frame_at : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k
STK' sp0' FP' W0' mem0' md0' own' ly' S' W' mem' md' k' cid pos,
ajournal segs B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k ->
ajournal segs B STK' sp0' FP' ly S W0' mem0' md0' own' ly' S' W' mem' md' k' ->
frame_addr ly' cid pos = frame_addr lyc cid pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k STK' sp0' FP' W0' mem0' md0' own' ly' S' W' mem' md' k'
  cid pos HJ1 HJ2.
destruct HJ1 as (_ & L1 & _). destruct HJ2 as (_ & L2 & _).
destruct L1 as (_ & _ & _ & _ & _ & F1 & _). destruct L2 as (_ & _ & _ & _ & _ & F2 & _).
unfold frame_addr. rewrite F1, F2. reflexivity.
Qed.

(* The shadow byte of the granule g of a frame for locals whose shadow bytes are sh. *)
Lemma hd_fsh_granule : forall H mem F sh g s,
hd_fsh segs H mem F sh -> F mod 8 = 0 -> 0 <= g < Z.of_nat (length sh) -> nth (Z.to_nat g) sh 0 = s ->
forall x, F + 8 * g <= x < F + 8 * g + 8 -> aview segs H mem (shadow_of_addr SHADOW_OFF x) = Some s.
Proof.
intros H mem F sh g s Hsh Hal Hg Hs x Hx.
assert (Hq : x / 8 = F / 8 + g).
{ pose proof (Z.div_mod F 8 ltac:(lia)) as HF.
  symmetry. apply Z.div_unique with (r := x - 8 * (F / 8 + g)); [left|]; lia. }
unfold shadow_of_addr. rewrite Hq. rewrite <- Hs. specialize (Hsh g Hg). unfold shadow_addr in Hsh.
rewrite <- Hsh. f_equal. lia.
Qed.

(* check_no_overrun(out + 3 cap) at 0x82ef8, after the parse at 0x82eec. The parse call's own premise (hd_pre at
   T_parse_STK), the frame for locals the harness holds (res = F + 0x180 is the parse's fourth argument), the out
   block live at the parse call and filled with the guard byte before it, and the memory clause of the parse's
   post (HPgCSpec.hd_parse_post at O = out, R = F + 0x180) give the guard bytes at out + 3 cap after the parse;
   check_no_overrun's own premise (hd_pre at T_check_STK) with the out block live gives the shadow and stack
   clauses. *)
Lemma headamp_A_site_no_overrun : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
k2 (regs2 : bvmap 5 word) lyc2 Sc2 W2 mem2 mdc2 (e : hd_env) (pos : Z) (props : option (list byte)) (o : answer),
api_env segs B ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 -> o = Headamp.parse_props props (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (repeat GUARD_BYTE (Z.to_nat (3 * (e_cap e + 1))))) ->
(forall a, 0 <= a < 2 ^ 64 -> ~ (spZ regs - T_parse_STK <= a < spZ regs) ->
 ~ ((e_out e <= a < e_out e + 3 * Z.of_nat (length (ans_cells o))) \/
    (e_F e + 0x180 <> 0 /\ e_F e + 0x180 <= a < e_F e + 0x180 + 12) \/
    (as_errno B <= a < as_errno B + 4)) ->
 aview segs (w_H W2) mem2 a = aview segs (w_H W) memc a) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2 ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc2 Sc2) ->
garr8 segs (mrestrict (w_H W2) mem2) (e_out e + 3 * e_cap e) (hd_zbytes (repeat GUARD_BYTE 3)) /\
range_addressable (aview segs (w_H W2) mem2) SHADOW_OFF (e_out e + 3 * e_cap e) 3 /\
hd_off_stack regs2 T_check_STK (e_out e + 3 * e_cap e) 3 /\ hd_app_rng segs (e_out e + 3 * e_cap e) 3.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc k2 regs2 lyc2 Sc2 W2 mem2 mdc2 e pos props o
  HAPI HP Hown HF Hin Hcap Ho Hg Hmem HP2 Hin2.
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hfb : fs_frame_bytes (hi_cid headamp_himg_A) = 1024) by reflexivity.
pose proof (Headamp.parse_props_total props (e_cap e) ltac:(lia)) as Hok. rewrite <- Ho in Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : Z.of_nat (length (ans_cells o)) <= e_cap e)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
pose proof (headamp_A_site_block STK sp0 FP ly S W0 mem0 md0 own k T_parse_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & Hlo & HSTK & Hsp & _).
pose proof (headamp_A_site_block STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2 _ _ HP2 Hin2)
  as (_ & _ & _ & _ & _ & Hra2).
assert (Hsep : e_out e + 3 * (e_cap e + 1) <= e_F e \/ e_F e + 1024 <= e_out e).
{ pose proof HP as (HJ & _).
  pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
  assert (Hfin : In (hi_cid headamp_himg_A, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
  pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ _ _ HAR Hin Hfin) as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF, Hrq, Hfb in Hz. exact Hz. }
assert (Herr : forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ (as_errno B <= a < as_errno B + 4)).
{ intros a Ha He. destruct HAPI as (_ & HAi & _).
  pose proof HP as (HJ & _). pose proof HJ as (HAR & _).
  assert (Hcin : exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n)
    by (exists (e_out e), (3 * (e_cap e + 1)); split; [exact Hin | lia]).
  destruct (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc a HAR (or_introl Hcin)) as (_ & Hni).
  exact (Hni (HAi a He)). }
split; [|split; [|split]].
- intros j Hj.
  assert (Hj3 : (j < 3)%nat) by (unfold hd_zbytes in Hj; rewrite length_map, repeat_length in Hj; exact Hj).
  rewrite hd_nth_guard by exact Hj3.
  assert (Hi : (Z.to_nat (3 * e_cap e) + j < length (hd_zbytes (repeat GUARD_BYTE (Z.to_nat (3 * (e_cap e + 1))))))%nat)
    by (unfold hd_zbytes; rewrite length_map, repeat_length; lia).
  destruct (Hg _ Hi) as (Hv & Hr). rewrite hd_nth_guard in Hv, Hr by lia.
  replace (e_out e + Z.of_nat (Z.to_nat (3 * e_cap e) + j)) with (e_out e + 3 * e_cap e + Z.of_nat j) in Hv by lia.
  split; [|exact Hr].
  apply (hd_val_mem_kept (w_H W) (w_H W2) memc mem2 _ 1 _); [|exact Hv].
  intros i0 Hi0. apply Hmem.
  + lia.
  + lia.
  + intros [HE|[HE|HE]].
    * lia.
    * lia.
    * exact (Herr (e_out e + 3 * e_cap e + Z.of_nat j + i0) ltac:(lia) HE).
- apply (proj1 (Hra2 (e_out e + 3 * e_cap e) 3 ltac:(lia) ltac:(lia))).
- apply (proj2 (Hra2 (e_out e + 3 * e_cap e) 3 ltac:(lia) ltac:(lia))).
- apply (headamp_A_site_block_app STK sp0 FP ly S W0 mem0 md0 own k2 T_check_STK regs2 lyc2 Sc2 W2 mem2 mdc2
    _ _ _ _ HP2 Hin2); lia.
Qed.

(* check_count(rc, cap, res) at 0x82f08: from the parse's answer_ok and keys bound, the res bytes of the parse's
   post at F + 0x180 (carried to the call), and the frame's shadow at the call (the res granules 0x30 and 0x31 in
   scope: hi_shB); check_count's own premise hd_pre gives the stack clause. *)
Lemma headamp_A_site_count : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
hd_fsh segs (w_H W) memc (e_F e) (hi_shB headamp_himg_A) ->
Model.pod_rec_wf r -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x180) (hd_zbytes (ans_res_bytes o)) ->
-1 <= ans_rc o <= e_cap e /\ e_cap e < 2 ^ 31 /\
(0 <= ans_rc o -> (e_F e + 0x180) mod 4 = 0 /\
 val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x180) 4 (ans_rc o mod 2 ^ 32) /\
 val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x180 + 4) 4 (ans_keys o mod 2 ^ 32) /\
 ans_rc o <= ans_keys o < 2 ^ 31 /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x180) 8 /\
 hd_off_stack regs T_check_STK (e_F e + 0x180) 8 /\ hd_app_rng segs (e_F e + 0x180) 8).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcap Ho Hg.
assert (Hk : 0 <= ans_keys o <= 5440).
{ pose proof (Headamp.parse_props_keys (hd_props (e_null e) (Model.buf r)) (e_cap e)) as Hk0. rewrite <- Ho in Hk0.
  assert (Hk1 : 0 <= ans_keys o <=
    match hd_props (e_null e) (Model.buf r) with Some bs => Z.of_nat (length bs) | None => 0 end)
    by (destruct o as [[? ?] [[? ?] ?]]; exact Hk0).
  revert Hk1. unfold hd_props. destruct (e_null e =? 0); cbv beta iota; intros Hk1; [|lia].
  pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hb). lia. }
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [lia|].
intros Hrc. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & Hn & Hrk)]; [lia|].
destruct (headamp_A_site_frame STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hown)
  as (Hal & H4k & Hbelow & Hoff).
rewrite <- HF in Hal, H4k, Hbelow, Hoff.
assert (Hfb : fs_frame_bytes (hi_cid headamp_himg_A) = 1024) by reflexivity.
rewrite Hfb in Hbelow, Hoff.
split; [symmetry; apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + 96) 0); [left; lia|];
  pose proof (Z.div_mod (e_F e) 32 ltac:(lia)); lia|].
unfold ans_res_bytes, ha_res_bytes, hd_zbytes in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [G1 G2]. apply garr8_app in G2 as [G2 G3].
rewrite length_map, Mem.length_le4 in G2. change (Z.of_nat 4) with 4 in G2.
split; [rewrite <- Hn; exact (hd_garr8_le4 _ _ _ G1)|].
split; [exact (hd_garr8_le4 _ _ _ G2)|].
split; [lia|].
split.
- intros x Hx. exists 0. split; [|left; reflexivity].
  apply (hd_fsh_granule (w_H W) memc (e_F e) (hi_shB headamp_himg_A) 48 0 Hsh).
  + lia.
  + split; [lia | vm_compute; reflexivity].
  + vm_compute. reflexivity.
  + lia.
- split; [apply Hoff; lia|].
  apply (hd_app_F STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF); lia.
Qed.

(* check_cells_valid(out, rc) at 0x82f14: from the parse's answer_ok and the out bytes of its post (carried to the
   call); check_cells_valid's own premise hd_pre with the out block live gives the shadow and stack clauses. *)
Lemma headamp_A_site_cells_valid : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (props : option (list byte)) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 -> o = Headamp.parse_props props (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) ->
- 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
(0 < ans_rc o ->
 Z.of_nat (length (ans_cells o)) = ans_rc o /\ Forall Headamp.cell_valid (ans_cells o) /\
 0 <= e_out e /\ e_out e + 3 * ans_rc o <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * ans_rc o) /\ hd_app_rng segs (e_out e) (3 * ans_rc o)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e props o HP Hin Hcap Ho Hg.
pose proof (Headamp.parse_props_total props (e_cap e) ltac:(lia)) as Hok. rewrite <- Ho in Hok.
apply answer_ok_parts in Hok as (Hcase & Hval).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & _ & HSTK & Hsp & Hra).
rewrite Hrq in Hra, Hbelow.
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
intros Hrc. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & _)]; [lia|].
split; [lia|]. split; [exact Hval|]. split; [lia|]. split; [lia|]. split; [exact Hg|].
split; [exact (proj1 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
split; [exact (proj2 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
apply (headamp_A_site_block_app STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ _ _ HP Hin);
  lia.
Qed.

(* check_plain(plain, rc, out, first) at 0x83790: the first parse's answer o1 (its cells copied into first by M04a,
   e_rc its answer) and the second parse's answer o2 (its cells in out, its answer in a0) are parse_props of the
   same bytes at the same cap, so o2 = o1: a0 = a1 = rc and out and first hold the same 3 rc bytes.
   check_plain's own premise hd_pre with the out and first blocks live gives the shadow and stack clauses. *)
Lemma headamp_A_site_plain : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (props : option (list byte)) (o1 o2 : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
In (e_first e, hd_xv e XRc3NZ) (ablocks B lyc Sc) ->
0 <= e_cap e <= 9 ->
o1 = Headamp.parse_props props (e_cap e) -> o2 = Headamp.parse_props props (e_cap e) ->
e_rc e = ans_rc o1 ->
garr8 segs (mrestrict (w_H W) memc) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o2))) ->
ans_rc o2 = e_rc e /\ - 2 ^ 31 <= e_rc e < 2 ^ 31 /\
(0 < e_rc e ->
 Z.of_nat (length (hd_zbytes (ha_cells_bytes (ans_cells o1)))) = 3 * e_rc e /\
 0 <= e_out e /\ e_out e + 3 * e_rc e <= 2 ^ 63 /\ 0 <= e_first e /\ e_first e + 3 * e_rc e <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) /\
 garr8 segs (mrestrict (w_H W) memc) (e_first e) (hd_zbytes (ha_cells_bytes (ans_cells o1))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * e_rc e) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_first e) (3 * e_rc e) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * e_rc e) /\ hd_off_stack regs T_check_STK (e_first e) (3 * e_rc e) /\
 hd_app_rng segs (e_out e) (3 * e_rc e) /\ hd_app_rng segs (e_first e) (3 * e_rc e) /\
 (e_out e + 3 * e_rc e <= e_first e \/ e_first e + 3 * e_rc e <= e_out e)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e props o1 o2 HP Hin Hinf Hcap Ho1 Ho2 Hrc Hf Hg.
rewrite Ho2, <- Ho1 in Hg |- *. clear Ho2.
pose proof (Headamp.parse_props_total props (e_cap e) ltac:(lia)) as Hok. rewrite <- Ho1 in Hok.
apply answer_ok_parts in Hok as (Hcase & _).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & _ & HSTK & Hsp & Hra).
pose proof (headamp_A_site_block STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hinf)
  as (Hf4 & Hfbelow & _ & _ & _ & Hrf).
rewrite Hrq in Hra, Hbelow.
split; [symmetry; exact Hrc|].
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
intros Hpos. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & _)]; [lia|].
assert (Hrf3 : req_size (hd_xv e XRc3NZ) = 3 * e_rc e).
{ cbn [hd_xv]. unfold req_size. rewrite Z.max_l by lia.
  destruct (Z.eqb_spec (3 * e_rc e) 0); [lia|]. destruct (Z.eqb_spec (3 * e_rc e + 0) 0); lia. }
rewrite Hrf3 in Hrf, Hfbelow.
split; [unfold hd_zbytes; rewrite length_map, length_ha_cells_bytes; lia|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hg|]. split; [exact Hf|].
destruct (Hra (e_out e) (3 * e_rc e) ltac:(lia) ltac:(lia)) as (Hra1 & Hra2).
destruct (Hrf (e_first e) (3 * e_rc e) ltac:(lia) ltac:(lia)) as (Hrf1 & Hrf2).
split; [exact Hra1|]. split; [exact Hrf1|]. split; [exact Hra2|]. split; [exact Hrf2|].
split; [apply (headamp_A_site_block_app STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  _ _ _ _ HP Hin); lia|].
split; [apply (headamp_A_site_block_app STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  _ _ _ _ HP Hinf); lia|].
(* out and first are two entries of the live blocks with different sizes (3 (cap + 1) > 3 rc), so AR keeps them
   apart (YCbq.v sep_blocks, from AR_sep_law). *)
assert (Hx : hd_xv e XRc3NZ = 3 * e_rc e)
  by (cbn [hd_xv]; rewrite Z.max_l by lia; destruct (Z.eqb_spec (3 * e_rc e) 0); lia).
assert (Hne : (e_out e, 3 * (e_cap e + 1)) <> (e_first e, hd_xv e XRc3NZ)).
{ rewrite Hx. intros Heq. injection Heq as E1 E2. lia. }
pose proof HP as (HJ & _). pose proof HJ as (HAR & _).
pose proof (YCbq.sep_blocks segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ _ _ HAR Hin Hinf Hne) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite Hrq, Hrf3 in Hz. lia.
Qed.
End k.

(* ================ the parse's arguments at its two calls, and the four checks against x ================
   Both parse calls lie inside a segment, after code that wrote memory: M03 (from C5) writes out with the guard
   byte (memset 0x82eb0), res with 0x5a (memset 0x82ecc) and the res granules 0x30, 0x31 := 0x00, 0x04 (0x82eb8,
   0x82ebc) before its parse at 0x82eec; M04b (from C8) writes out with the guard byte (memset 0x83770) before its
   parse at 0x83780. So each parse lemma takes the segment's start state (hd_seg_pre and the segment contract's own
   premises), the call's own premise hd_pre, the blocks as at the start, and the walk's memory fact between the
   two states (hd_kept: every byte outside the callees' stack below R, the segment's write ranges and the out
   block reads as at the start), and derives every premise of the parse contract at the call. The four checks
   against x (check_object 0x836ac, check_cells 0x836bc, check_keys 0x836cc, check_refusal 0x836d8) run after
   the non-corrupt path brought the seventeen x granules 0x34 .. 0x44 into scope (0x82f38 .. 0x82f78, each := 0)
   and expect_of wrote x; their lemmas take x's bytes as M03's walk gives them there. *)

(* On a record left uncorrupted, the parse's answer on the harness's argument is expect_of's (Pod/Headamp.v
   parse_props_build, from the record's well-formedness, which the segment contracts state). *)
Lemma hd_parse_expect : forall r cap null, Model.pod_rec_wf r -> Model.corrupt r = false ->
Headamp.parse_props (hd_props null (Model.buf r)) cap = Headamp.expect_model (negb (null =? 0)) cap r.
Proof.
intros r cap null Hw Hc. unfold hd_props. destruct (null =? 0); cbn [negb].
- cbn [Headamp.parse_props]. unfold Model.buf. unfold Model.corrupt in Hc.
  destruct (Model.p_corr r) as [c|]; [discriminate Hc|]. apply Headamp.parse_model_encode_any. exact Hw.
- reflexivity.
Qed.

(* Every pod buffer is a whole number of 8-byte words (Pod/Spa.v buf_header, Pod/Model.v pod_encode_len). *)
Lemma hd_buf_len8 : forall r, Model.pod_rec_wf r -> Z.of_nat (length (Model.buf r)) mod 8 = 0.
Proof.
intros r Hw. pose proof (Spa.buf_header r Hw) as (HL & _). rewrite HL.
destruct r as [s ps co]. destruct Hw as (_ & Hps & Hes & Hl3 & _).
cbn [Model.p_props] in Hps, Hes, Hl3.
assert (Hps' : Forall (fun kv => Model.pval_wf (snd kv)) ps)
  by (eapply Forall_impl; [|exact Hps]; intros kv [_ Hv]; exact Hv).
pose proof (Model.pod_encode_len s ps co Hps' Hes Hl3) as (_ & _ & Hd).
apply (proj2 (Z.mod_divide _ 8 ltac:(lia))). exact Hd.
Qed.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable segs : list Segment.
Variable B : asyms.

(* The walk's memory fact between a segment's start (W, memc) and a state inside it (W', memc'): every byte outside
   the callees' stack below R, the write ranges ws and the out block reads as at the start. *)
Definition hd_kept (e : hd_env) (ws : list (hd_x * Z * Z)) (W : world segs) (memc : word -> option byte)
(W' : world segs) (memc' : word -> option byte) : Prop :=
forall a, 0 <= a < 2 ^ 64 -> ~ (e_R e - T_SEG_STK <= a < e_R e) ->
~ (hd_inw e ws a \/ (e_out e <= a < e_out e + 3 * (e_cap e + 1))) ->
aview segs (w_H W') memc' a = aview segs (w_H W) memc a.

(* hd_kept holds at the segment's start itself (satisfiable at every instance). *)
Lemma hd_kept_refl : forall e ws W memc, hd_kept e ws W memc W memc.
Proof. intros e ws W memc a _ _ _. reflexivity. Qed.

(* What a state inside a segment has (hd_cctx_of): its AR, the out block, the frame for locals, R above the
   allocator ceiling. *)
Definition hd_cctx (lyc : alayout) (Sc : astate) (W : world segs) (memc : word -> option byte) (mdc : Model)
(e : hd_env) (pos : Z) : Prop :=
AR segs B lyc Sc W memc mdc /\ In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) /\
In (hi_cid headamp_himg_A, pos) (frames Sc) /\ e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos /\
alloc_ceiling <= e_R e - T_SEG_STK /\ 0 <= e_cap e <= 9.

(* The image bytes the parse's callees read that no string of the record covers: the parse's two doubles, the
   stack-guard GOT word and the guard (headamp_A_img_bytes_rsegs shows it at image A's segments). *)
Definition headamp_A_img_bytes : Prop :=
forall a, In a [0x10340; 0x10378; 0x9cff8; 0x5f7d90] -> forall i, 0 <= i < 8 -> in_img segs (a + i).

Lemma hd_pre_sp0 : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
0 <= STK /\ sp0 <= 2 ^ 47 /\ alloc_ceiling <= sp0 - STK.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc HP. destruct HP as (HJ & _).
destruct HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & H0 & H1 & H2 & H3 & H4 & _). lia.
Qed.

Lemma hd_cctx_of : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc sh RLO RHI
(e : hd_env) (pos : Z) k' T (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_cctx lyc' Sc' W' memc' mdc' e pos.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos k' T regs' lyc' Sc' W' memc' mdc'
  HS HO HP HPm.
destruct HS as (HJ & _ & _ & _ & _ & _ & _ & _ & HRS & Hown & HF & _ & Hcap & _).
destruct HP as (HJ' & _).
pose proof HJ' as (HAR' & _ & _ & _ & _ & Hfr' & _).
pose proof HJ as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hstk & _).
destruct Hstk as (_ & _ & Hc1 & Hc2 & _).
destruct HO as (_ & HOin & _).
split; [exact HAR'|].
split; [exact (Permutation_in _ (Permutation_sym HPm) HOin)|].
split; [rewrite Hfr'; apply in_or_app; left; exact Hown|].
split; [rewrite HF; symmetry; eapply headamp_A_site_frame_at; [exact HJ | exact HJ']|].
split; [lia | exact Hcap].
Qed.

Lemma hd_cctx_facts : forall lyc Sc W memc mdc e pos, hd_cctx lyc Sc W memc mdc e pos ->
e_out e mod 8 = 0 /\ 4096 <= e_out e /\ e_out e + 3 * (e_cap e + 1) <= alloc_ceiling /\
(e_out e + 3 * (e_cap e + 1) <= kLowShadowBeg \/ kHighMemBeg <= e_out e) /\
e_F e mod 8 = 0 /\ e_F e mod 32 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= alloc_ceiling /\
(e_F e + 1024 <= kLowShadowBeg \/ kHighMemBeg <= e_F e) /\
(forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ in_img segs a) /\
(forall a, e_F e <= a < e_F e + 1024 -> ~ in_img segs a) /\
(0x7fff7f800000 <= alloc_ceiling <= 0x7fffff800000) /\ alloc_ceiling <= e_R e - T_SEG_STK /\ 0 <= e_cap e <= 9.
Proof.
intros lyc Sc W memc mdc e pos (HAR & HO & Hfin & HF & HRc & Hcap).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
assert (Hfb : fs_frame_bytes (hi_cid headamp_himg_A) = 1024) by reflexivity.
pose proof YCbq.asan_consts as (C1 & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ HAR HO) as (Hm16 & H4 & Hce & Happ & _).
rewrite Hrq in Hce, Happ.
destruct (YCbq.frames_bounds segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ HAR Hfin) as (F4 & Fce & Fapp).
destruct (al_frames _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ HAR Hfin) as (F32 & _).
rewrite <- HF in F4, Fce, Fapp, F32. rewrite Hfb in Fce, Fapp.
unfold in_app, ASAN_CEIL in Happ, Fapp.
assert (Hci : forall a, e_out e <= a < e_out e + 3 * (e_cap e + 1) -> ~ in_img segs a).
{ intros a Ha.
  assert (Hcin : exists p n, In (p, n) (ablocks B lyc Sc) /\ p <= a < p + req_size n)
    by (exists (e_out e), (3 * (e_cap e + 1)); rewrite Hrq; split; [exact HO | lia]).
  exact (proj2 (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc a HAR (or_introl Hcin))). }
assert (Hcf : forall a, e_F e <= a < e_F e + 1024 -> ~ in_img segs a).
{ intros a Ha.
  assert (Hcin : exists cid pos, In (cid, pos) (frames Sc) /\
    frame_addr lyc cid pos <= a < frame_addr lyc cid pos + fs_frame_bytes cid)
    by (exists (hi_cid headamp_himg_A), pos; rewrite <- HF, Hfb; split; [exact Hfin | lia]).
  exact (proj2 (al_client_img _ _ (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc a HAR (or_intror (or_introl Hcin)))). }
assert (F8 : e_F e mod 8 = 0).
{ symmetry. apply (Z.mod_unique _ 8 (4 * (e_F e / 32)) 0); [left; lia|].
  pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). lia. }
assert (O8 : e_out e mod 8 = 0).
{ symmetry. apply (Z.mod_unique _ 8 (2 * (e_out e / 16)) 0); [left; lia|].
  pose proof (Z.div_mod (e_out e) 16 ltac:(lia)). lia. }
split; [exact O8|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact F8|]. split; [exact F32|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hci|]. split; [exact Hcf|]. split; [exact C1|]. split; [exact HRc | exact Hcap].
Qed.

Lemma hd_inw_w3 : forall e a, hd_inw e (hi_w3 headamp_himg_A) a ->
(e_F e + 0x180 <= a < e_F e + 0x228) \/ (shadow_addr (e_F e) + 0x30 <= a < shadow_addr (e_F e) + 0x45) \/
(e_R e <= a < e_R e + 0x120).
Proof.
intros e a H. unfold hd_inw in H. cbn [hi_w3 headamp_himg_A] in H.
rewrite !Exists_cons, Exists_nil in H. cbn [fst snd hd_xv] in H. lia.
Qed.

Lemma hd_block_not_img : forall ly S W mem md p n a, AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
p <= a < p + req_size n -> ~ in_img segs a.
Proof.
intros ly S W mem md p n a HAR Hin Ha.
assert (Hcin : exists p0 n0, In (p0, n0) (ablocks B ly S) /\ p0 <= a < p0 + req_size n0)
  by (exists p, n; split; [exact Hin | exact Ha]).
exact (proj2 (al_client_img _ _ (YG0q.AR_laws_ok segs B) ly S W mem md a HAR (or_introl Hcin))).
Qed.

(* A byte below the allocator ceiling, outside res and x, outside their shadow granules and outside out, reads as
   at the segment's start. *)
Lemma hd_kept_at : forall lyc' Sc' W' memc' mdc' e pos W memc a,
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
0 <= a < alloc_ceiling ->
~ (e_F e + 0x180 <= a < e_F e + 0x228) -> ~ (shadow_addr (e_F e) + 0x30 <= a < shadow_addr (e_F e) + 0x45) ->
~ (e_out e <= a < e_out e + 3 * (e_cap e + 1)) ->
aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a Hc HM Ha H1 H2 H3.
pose proof Hc as (_ & _ & _ & _ & HRc & _).
pose proof YCbq.asan_consts as (C1 & _).
unfold hd_kept in HM. apply HM.
- lia.
- unfold T_SEG_STK, ASTACK in *. lia.
- intros [Hw|Ho]; [|exact (H3 Ho)].
  apply hd_inw_w3 in Hw. destruct Hw as [Hw|[Hw|Hw]]; [exact (H1 Hw) | exact (H2 Hw) |].
  unfold T_SEG_STK, ASTACK in *. lia.
Qed.

Lemma hd_kept_img : forall lyc' Sc' W' memc' mdc' e pos W memc a,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
in_img segs a -> aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a Hlow Hc HM Ha.
pose proof (Hlow a Ha) as Hab.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
apply (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- unfold kLowMemEnd in Hab. lia.
- intros Hx. exact (Fni a ltac:(lia) Ha).
- unfold shadow_addr, SHADOW_OFF, kLowMemEnd in *. pose proof (Z.div_pos (e_F e) 8 ltac:(lia) ltac:(lia)). lia.
- intros Hx. exact (Oni a Hx Ha).
Qed.

Lemma hd_kept_shimg : forall lyc' Sc' W' memc' mdc' e pos W memc x,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
in_img segs x ->
aview segs (w_H W') memc' (shadow_of_addr SHADOW_OFF x) = aview segs (w_H W) memc (shadow_of_addr SHADOW_OFF x).
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc x Hlow Hc HM Hx.
pose proof (Hlow x Hx) as Hxb.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
apply (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc (shadow_of_addr SHADOW_OFF x) Hc HM);
  unfold shadow_of_addr, shadow_addr, SHADOW_OFF, kLowMemEnd, kLowShadowBeg, kHighMemBeg in *.
- lia.
- lia.
- intros Hs. apply (Fni x); [lia | exact Hx].
- lia.
Qed.

Lemma hd_kept_tail : forall lyc' Sc' W' memc' mdc' e pos W memc x a,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
in_img segs x -> x < a < x - x mod 8 + 8 ->
aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc x a Hlow Hc HM Hx Ha.
pose proof (Hlow x Hx) as Hxb.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF. pose proof (Z.div_mod (e_out e) 8 ltac:(lia)) as DO.
unfold kLowMemEnd in Hxb.
apply (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- lia.
- intros Hs. apply (Fni x); [lia | exact Hx].
- unfold shadow_addr, SHADOW_OFF. pose proof (Z.div_pos (e_F e) 8 ltac:(lia) ltac:(lia)). lia.
- intros Hs. apply (Oni x); [lia | exact Hx].
Qed.

(* A shadow byte of the low application range reads at the call when it read at the start: either the walk kept
   it, or it is one of the frame's shadow granules, which the walk has at the call. *)
Lemma hd_kept_hull : forall lyc' Sc' W' memc' mdc' e pos W memc u,
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
(forall i, 0x30 <= i < 0x45 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
kLowShadowBeg <= u < kHighMemBeg -> aview segs (w_H W) memc u <> None -> aview segs (w_H W') memc' u <> None.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc u Hc HM Hfr Hu Hn.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
destruct (Z_le_gt_dec (shadow_addr (e_F e) + 0x30) u) as [H1|H1];
  [destruct (Z_lt_le_dec u (shadow_addr (e_F e) + 0x45)) as [H2|H2]|].
- replace u with (shadow_addr (e_F e) + (u - shadow_addr (e_F e))) by lia. apply Hfr. lia.
- rewrite (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc u Hc HM);
    [exact Hn | unfold kLowShadowBeg, kHighMemBeg in *; lia ..].
- rewrite (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc u Hc HM);
    [exact Hn | unfold kLowShadowBeg, kHighMemBeg in *; lia ..].
Qed.

(* A byte of a block live at the call, apart from out, reads as at the segment's start. *)
Lemma hd_kept_block : forall lyc' Sc' W' memc' mdc' e pos W memc p n a,
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
In (p, n) (ablocks B lyc' Sc') -> (p + req_size n <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= p) ->
p <= a < p + req_size n -> aview segs (w_H W') memc' a = aview segs (w_H W) memc a.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc p n a Hc HM Hin Hap Ha.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR & _ & Hfin & HF & _).
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR Hin) as (_ & P4 & Pce & Papp & _).
pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ _ _ HAR Hin Hfin) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF in Hz.
change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024 in Hz.
unfold in_app, ASAN_CEIL in Papp.
pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
apply (hd_kept_at lyc' Sc' W' memc' mdc' e pos W memc a Hc HM).
- lia.
- lia.
- unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- lia.
Qed.

Lemma hd_garr8_kept : forall H H' (m m' : word -> option byte) a l,
(forall j, (j < length l)%nat -> aview segs H' m' (a + Z.of_nat j) = aview segs H m (a + Z.of_nat j)) ->
garr8 segs (mrestrict H m) a l -> garr8 segs (mrestrict H' m') a l.
Proof.
intros H H' m m' a l Hk Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
eapply hd_val_mem_kept; [|exact Hv].
intros i Hi. assert (i = 0) as -> by lia. rewrite Z.add_0_r. exact (Hk j Hj).
Qed.

(* hd_cstr carries over when its bytes and NUL, the shadow of its len + 1 bytes and its tail read the same and
   every shadow byte of its hull still reads. *)
Lemma hd_cstr_kept : forall H H' (m m' : word -> option byte) a s,
hd_cstr segs H m a s ->
(forall i, 0 <= i <= Z.of_nat (length s) -> aview segs H' m' (a + i) = aview segs H m (a + i)) ->
(forall x, a <= x < a + Z.of_nat (length s) + 1 ->
 aview segs H' m' (shadow_of_addr SHADOW_OFF x) = aview segs H m (shadow_of_addr SHADOW_OFF x)) ->
(forall u, shadow_addr a / 8 * 8 <= u < shadow_addr (a + (Z.of_nat (length s) + 1) - 1) / 8 * 8 + 8 ->
 aview segs H m u <> None -> aview segs H' m' u <> None) ->
(forall u, a + Z.of_nat (length s) < u < a + Z.of_nat (length s) - (a + Z.of_nat (length s)) mod 8 + 8 ->
 aview segs H' m' u = aview segs H m u) ->
hd_cstr segs H' m' a s.
Proof.
intros H H' m m' a s (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10) Eb Es Eh Et.
split; [intros i Hi; rewrite Eb by lia; exact (C1 i Hi)|].
split; [rewrite Eb by lia; exact C2|].
split; [exact C3|]. split; [exact C4|]. split; [exact C5|]. split; [exact C6|]. split; [exact C7|].
split; [eapply range_addressable_agree; [|exact C8]; intros x Hx; apply Es; lia|].
split; [intros u Hu; apply Eh; [exact Hu | exact (C9 u Hu)]|].
intros u Hu. rewrite Et by exact Hu. exact (C10 u Hu).
Qed.

Lemma hd_cstr_call : forall lyc' Sc' W' memc' mdc' e pos W memc a s,
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) ->
hd_cctx lyc' Sc' W' memc' mdc' e pos -> hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
(forall i, 0x30 <= i < 0x45 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
hd_cstr segs (w_H W) memc a s -> hd_cstr segs (w_H W') memc' a s.
Proof.
intros lyc' Sc' W' memc' mdc' e pos W memc a s Hlow Hc HM Hfr Hs.
pose proof Hs as (_ & _ & _ & Ha0 & _ & Himg & _).
pose proof (Hlow _ (Himg 0 ltac:(lia))) as Hlo.
pose proof (Hlow _ (Himg (Z.of_nat (length s)) ltac:(lia))) as Hhi.
rewrite Z.add_0_r in Hlo.
apply (hd_cstr_kept _ _ _ _ a s Hs).
- intros i Hi. exact (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc (a + i) Hlow Hc HM (Himg i Hi)).
- intros x Hx. apply (hd_kept_shimg lyc' Sc' W' memc' mdc' e pos W memc x Hlow Hc HM).
  replace x with (a + (x - a)) by lia. apply Himg. lia.
- intros u Hu Hn. apply (hd_kept_hull lyc' Sc' W' memc' mdc' e pos W memc u Hc HM Hfr); [|exact Hn].
  unfold shadow_addr, SHADOW_OFF in Hu. unfold kLowShadowBeg, kHighMemBeg. unfold kLowMemEnd in Hlo, Hhi.
  pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)).
  pose proof (Z.div_mod (a + (Z.of_nat (length s) + 1) - 1) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (a + (Z.of_nat (length s) + 1) - 1) 8 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + a / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + a / 8) 8 ltac:(lia)).
  pose proof (Z.div_mod (0x7fff8000 + (a + (Z.of_nat (length s) + 1) - 1) / 8) 8 ltac:(lia)).
  pose proof (Z.mod_pos_bound (0x7fff8000 + (a + (Z.of_nat (length s) + 1) - 1) / 8) 8 ltac:(lia)).
  lia.
- intros u Hu. apply (hd_kept_tail lyc' Sc' W' memc' mdc' e pos W memc (a + Z.of_nat (length s)) u Hlow Hc HM);
    [apply Himg; lia | exact Hu].
Qed.

Lemma hd_rdword_kept : forall (rd rd' : reader) a, (forall i, 0 <= i < 8 -> rd' (a + i) = rd (a + i)) ->
rdword rd' a = rdword rd a.
Proof.
intros rd rd' a H. unfold rdword.
assert (E0 : rd' a = rd a) by (rewrite <- (Z.add_0_r a); apply H; lia).
rewrite E0, (H 1), (H 2), (H 3), (H 4), (H 5), (H 6), (H 7) by lia. reflexivity.
Qed.

(* The parse contract's premises at a call inside a segment, from the segment's start state, the segment contract's
   own premises on the pod and out blocks, the call's hd_pre and the walk's memory fact; R and its two clauses are
   the call's (headamp_A_site_parse_args gives them for M03's R = F + 0x180, headamp_A_site_parse_args_plain for
   M04b's R = 0). *)
Lemma headamp_A_site_parse_core : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
sh RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc' (R : Z),
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_A_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A sh RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
(forall i, 0x30 <= i < 0x45 -> aview segs (w_H W') memc' (shadow_addr (e_F e) + i) <> None) ->
(R = 0 \/ (hd_wcell STK sp0 lyc' own (spZ regs') T_parse_STK R 12 /\ R mod 4 = 0 /\
 range_addressable (aview segs (w_H W') memc') SHADOW_OFF R 12)) ->
(R = 0 \/ e_pod e + e_len e <= R \/ R + 12 <= e_pod e) ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A)
  (e_null e) (e_pod e) (e_out e) R (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc' R
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM Hfr HR HPR.
pose proof (hd_cctx_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR' & _).
pose proof (headamp_A_site_strs segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc sh RLO RHI e pos HS)
  as (S1 & S2 & S3 & S4 & _ & _ & _ & _ & Hdcs & Hgd).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Haro & _).
pose proof (Spa.buf_header r Hwf) as (_ & _ & Hu32 & Hlb).
pose proof (hd_buf_len8 r Hwf) as Hl8.
rewrite <- Hlen in Hu32, Hlb, Hl8.
destruct HPf as (Hp0 & Hpin & Hpout).
destruct HOf as (Ho0 & Hoin & Hoout).
assert (Hpin' : In (e_pod e, e_len e) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPm) Hpin).
assert (Hoin' : In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc' Sc'))
  by exact (Permutation_in _ (Permutation_sym HPm) Hoin).
assert (Hrqp : req_size (e_len e) = e_len e) by (unfold req_size; destruct (Z.eqb_spec (e_len e) 0); lia).
assert (Hrqo : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
  _ _ HP Hpin') as (P4 & Pbelow & _ & PSTK & Psp & Pra).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
  _ _ HP Hoin') as (_ & _ & _ & _ & _ & Ora).
rewrite Hrqp in Pbelow, Pra. rewrite Hrqo in Ora.
destruct (al_blocks _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR' Hpin') as (Pm16 & _ & _ & Papp & _).
destruct (al_shadow _ _ (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ HAR' Hpin') as (_ & Phull).
rewrite Hrqp in Papp, Phull. unfold in_app, ASAN_CEIL in Papp.
assert (Hpe : e_pod e + e_len e <= as_errno B \/ as_errno B + 4 <= e_pod e).
{ destruct HAPI as (_ & HEi & _).
  destruct (Z_le_gt_dec (e_pod e + e_len e) (as_errno B)) as [H1|H1]; [left; exact H1|].
  destruct (Z_le_gt_dec (as_errno B + 4) (e_pod e)) as [H2|H2]; [right; exact H2|].
  exfalso.
  apply (hd_block_not_img lyc' Sc' W' memc' mdc' (e_pod e) (e_len e) (Z.max (e_pod e) (as_errno B)) HAR' Hpin').
  - rewrite Hrqp. lia.
  - apply HEi. lia. }
unfold hd_parse_args. rewrite <- Hlen.
split.
{ intros _.
  split; [lia|]. split; [exact Pm16|]. split; [lia|]. split; [exact Hl8|]. split; [exact Hu32|].
  split; [lia|].
  split.
  { apply (hd_garr8_kept (w_H W) (w_H W') memc memc'); [|exact Hpod].
    intros j Hj. unfold hd_zbytes in Hj. rewrite length_map in Hj.
    apply (hd_kept_block lyc' Sc' W' memc' mdc' e pos W memc (e_pod e) (e_len e) _ Hc HM Hpin');
      rewrite Hrqp; [exact Hap | lia]. }
  split; [exact Hpin'|]. split; [exact Hap|]. split; [exact HPR|]. split; [exact Hpe|].
  split; [exact (proj1 (Pra (e_pod e) (e_len e) ltac:(lia) ltac:(lia)))|].
  split; [exact Phull|].
  split; [unfold amem_range, kLowMemEnd, kLowShadowBeg, kHighMemBeg, kHighMemEnd in *; lia|].
  exact (proj2 (Pra (e_pod e) (e_len e) ltac:(lia) ltac:(lia))). }
split; [exact Hcap|].
split; [split; [exact Ho0 | split; [exact Hoin' | exact Hoout]]|].
split; [exact (proj1 (Ora (e_out e) (3 * (e_cap e + 1)) ltac:(lia) ltac:(lia)))|].
split; [exact (proj2 (Ora (e_out e) (3 * (e_cap e + 1)) ltac:(lia) ltac:(lia)))|].
split; [exact HR|].
cbn [hi_akey hi_aph hi_apad hi_asens hi_gotw hi_guard hi_dcs headamp_himg_A].
split; [exact (hd_cstr_call lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S1)|].
split; [exact (hd_cstr_call lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S2)|].
split; [exact (hd_cstr_call lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S3)|].
split; [exact (hd_cstr_call lyc' Sc' W' memc' mdc' e pos W memc _ _ Hlow Hc HM Hfr S4)|].
split.
{ unfold hd_ro_cells in *. rewrite Forall_forall in Hdcs |- *. intros c Hcin.
  eapply hd_val_mem_kept; [|exact (Hdcs c Hcin)].
  intros i Hi. apply (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
  unfold headamp_A_dcs in Hcin. cbn [In] in Hcin.
  destruct Hcin as [<-|[<-|[]]]; cbn [fst]; (apply HIMG; [hd_in | lia]). }
split.
{ unfold hd_guard_ok in *. destruct Hgd as (G1 & can & G2). split.
  - rewrite (hd_rdword_kept (aview segs (w_H W) memc) (aview segs (w_H W') memc') 0x9cff8); [exact G1|].
    intros i Hi. apply (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
    apply HIMG; [hd_in | exact Hi].
  - exists can.
    rewrite (hd_rdword_kept (aview segs (w_H W) memc) (aview segs (w_H W') memc') 0x5f7d90); [exact G2|].
    intros i Hi. apply (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM).
    apply HIMG; [hd_in | exact Hi]. }
split.
{ destruct HAPI as (_ & HEi & _). intros kk Hkk.
  rewrite (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc _ Hlow Hc HM); [exact (Herr kk Hkk)|].
  apply HEi. lia. }
split.
{ intros a Hro Hos Hne.
  rewrite (hd_kept_img lyc' Sc' W' memc' mdc' e pos W memc a Hlow Hc HM); [exact (Haro a Hro Hos Hne)|].
  destruct Hro as [(sg & Hsg & _ & Hr)|Hr]; [exists sg; split; [exact Hsg | exact Hr] | exact (Hrelro a Hr)]. }
exact Hfrm.
Qed.

Lemma headamp_A_shB_facts : length (hi_shB headamp_himg_A) = 80%nat /\ nth 48 (hi_shB headamp_himg_A) 0 = 0 /\
nth 49 (hi_shB headamp_himg_A) 0 = 4.
Proof. split; [|split]; vm_compute; reflexivity. Qed.

(* The 12 bytes of res (F + 0x180) are addressable when the frame's shadow has the res granules 0x30, 0x31 at
   0x00, 0x04. *)
Lemma hd_res_addressable : forall H mem F sh, hd_fsh segs H mem F sh -> F mod 8 = 0 ->
length sh = 80%nat -> nth 48 sh 0 = 0 -> nth 49 sh 0 = 4 ->
forall a m, F + 0x180 <= a -> a + m <= F + 0x18c -> range_addressable (aview segs H mem) SHADOW_OFF a m.
Proof.
intros H mem F sh Hsh Hal Hl H48 H49 a m Ha Ham x Hx.
pose proof (Z.div_mod F 8 ltac:(lia)) as HF.
destruct (Z_lt_le_dec x (F + 0x188)) as [Hlt|Hge].
- exists 0. split; [|left; reflexivity].
  apply (hd_fsh_granule segs H mem F sh 48 0 Hsh Hal); [rewrite Hl; lia | exact H48 | lia].
- exists 4. split.
  + apply (hd_fsh_granule segs H mem F sh 49 4 Hsh Hal); [rewrite Hl; lia | exact H49 | lia].
  + right. assert (Hm : x mod 8 = x - (F + 0x188)).
    { symmetry. apply (Z.mod_unique x 8 (F / 8 + 49) (x - (F + 0x188))); [left; lia | lia]. }
    lia.
Qed.

(* The parse contract's premises at M03's call 0x82eec (a0 = the parse's first argument, a1 = out, a2 = cap,
   a3 = res = F + 0x180): res is a cell of the class-4 frame for locals, 4-aligned, below the stack window, with its
   granules at 0x00, 0x04 (the walk's hd_fsh at the call, hi_shB), and apart from the pod (YCbq.v
   sep_block_frame). *)
Lemma headamp_A_site_parse_args : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_A_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A (hi_shA headamp_himg_A)
  RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept e (hi_w3 headamp_himg_A) W memc W' memc' ->
hd_fsh segs (w_H W') memc' (e_F e) (hi_shB headamp_himg_A) ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A)
  (e_null e) (e_pod e) (e_out e) (e_F e + 0x180) (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc'
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM Hsh'.
pose proof (hd_cctx_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof Hc as (HAR' & _ & Hfin & HF' & _).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hown & _).
pose proof HPf as (_ & Hpin & _).
assert (Hpin' : In (e_pod e, e_len e) (ablocks B lyc' Sc')) by exact (Permutation_in _ (Permutation_sym HPm) Hpin).
pose proof headamp_A_shB_facts as (Bl & B48 & B49).
apply (headamp_A_site_parse_core STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos ev r
  k' regs' lyc' Sc' W' memc' mdc' (e_F e + 0x180) Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm
  HM).
- intros i Hi. rewrite (Hsh' i); [discriminate|]. rewrite Bl. lia.
- right. split; [|split].
  + destruct (headamp_A_site_frame segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc'
      _ _ HP Hown) as (_ & _ & Hbelow & _).
    pose proof HP as (_ & _ & _ & _ & _ & _ & Hlo & _).
    rewrite <- HF' in Hbelow. change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024 in Hbelow.
    unfold hd_wcell. split.
    * right. exists (hi_cid headamp_himg_A), pos. split; [exact Hown|]. rewrite <- HF'.
      change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024. cbn [hi_cid headamp_himg_A]. lia.
    * right. lia.
  + symmetry. apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + 96) 0); [left; lia|].
    pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). lia.
  + apply (hd_res_addressable (w_H W') memc' (e_F e) (hi_shB headamp_himg_A) Hsh' F8 Bl B48 B49); lia.
- right.
  pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc' Sc' W' memc' mdc' _ _ _ _ HAR' Hpin' Hfin)
    as Hz.
  unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF' in Hz.
  change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024 in Hz.
  assert (Hrqp : req_size (e_len e) = e_len e).
  { pose proof (Spa.buf_header r Hwf) as (_ & _ & _ & Hb). rewrite <- Hlen in Hb.
    unfold req_size. destruct (Z.eqb_spec (e_len e) 0); lia. }
  rewrite Hrqp in Hz. lia.
Qed.

(* The parse contract's premises at M04b's call 0x83780 (R = 0): M04b's own write ranges are hi_w5 (none on image
   A), and the frame's shadow at the call is the segment start's (hi_shB). *)
Lemma headamp_A_site_parse_args_plain : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc
mdc RLO RHI (e : hd_env) (pos ev : Z) (r : Model.pod_rec) k' (regs' : bvmap 5 word) lyc' Sc' W' memc' mdc',
(forall a, in_img segs a -> 0 <= a < kLowMemEnd) -> (forall a, RLO <= a < RHI -> in_img segs a) ->
api_env segs B -> headamp_A_img_bytes ->
hd_seg_pre segs B STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc headamp_himg_A (hi_shB headamp_himg_A)
  RLO RHI e pos ->
Model.pod_rec_wf r -> e_len e = Z.of_nat (length (Model.buf r)) ->
garr8 segs (mrestrict (w_H W) memc) (e_pod e) (hd_zbytes (Model.buf r)) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_pod e) (e_len e) ->
hd_fresh_block (ablocks B ly S) (ablocks B lyc Sc) (e_out e) (3 * (e_cap e + 1)) ->
(e_pod e + e_len e <= e_out e \/ e_out e + 3 * (e_cap e + 1) <= e_pod e) ->
rd32 (aview segs (w_H W) memc) (as_errno B) ev -> YK0o.frm_zero (@fp_csr fx) ->
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k' T_parse_STK regs' lyc' Sc' W' memc' mdc' ->
Permutation (ablocks B lyc' Sc') (ablocks B lyc Sc) ->
hd_kept e (hi_w5 headamp_himg_A) W memc W' memc' ->
hd_parse_args segs B STK sp0 ly S lyc' Sc' W' memc' own regs' RLO RHI
  (hi_akey headamp_himg_A) (hi_aph headamp_himg_A) (hi_apad headamp_himg_A) (hi_asens headamp_himg_A)
  (hi_gotw headamp_himg_A) (hi_guard headamp_himg_A) (hi_dcs headamp_himg_A)
  (e_null e) (e_pod e) (e_out e) 0 (e_cap e) ev (Model.buf r).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc RLO RHI e pos ev r k' regs' lyc' Sc' W' memc' mdc'
  Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM5.
assert (HM : hd_kept e (hi_w3 headamp_himg_A) W memc W' memc').
{ unfold hd_kept in *. intros a Ha Hs Hn. apply HM5; [exact Ha | exact Hs |].
  intros [Hw|Ho]; [|apply Hn; right; exact Ho].
  unfold hd_inw in Hw. cbn [hi_w5 headamp_himg_A] in Hw. inversion Hw. }
pose proof (hd_cctx_of STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos
  k' T_parse_STK regs' lyc' Sc' W' memc' mdc' HS HOf HP HPm) as Hc.
pose proof (hd_cctx_facts _ _ _ _ _ _ _ Hc)
  as (O8 & O4 & Oce & Oapp & F8 & F32 & F4 & Fce & Fapp & Oni & Fni & C1 & HRc & Hcap).
pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsh0 & _).
pose proof headamp_A_shB_facts as (Bl & _ & _).
apply (headamp_A_site_parse_core STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc _ RLO RHI e pos ev r
  k' regs' lyc' Sc' W' memc' mdc' 0 Hlow Hrelro HAPI HIMG HS Hwf Hlen Hpod HPf HOf Hap Herr Hfrm HP HPm HM).
- intros i Hi.
  assert (Hi' : 0 <= i < Z.of_nat (length (hi_shB headamp_himg_A))) by (rewrite Bl; lia).
  pose proof (Z.div_mod (e_F e) 8 ltac:(lia)) as DF.
  unfold hd_kept in HM5. rewrite HM5.
  + rewrite (Hsh0 i Hi'). discriminate.
  + unfold shadow_addr, SHADOW_OFF. lia.
  + unfold shadow_addr, SHADOW_OFF, T_SEG_STK, ASTACK in *. lia.
  + intros [Hw|Ho]; [unfold hd_inw in Hw; cbn [hi_w5 headamp_himg_A] in Hw; inversion Hw|].
    unfold shadow_addr, SHADOW_OFF, kLowShadowBeg, kHighMemBeg in *. lia.
- left. reflexivity.
- left. reflexivity.
Qed.

(* ---- the four checks against x ---- *)
(* The frame's shadow at the four calls: hi_shB with the seventeen x granules 0x34 .. 0x44 in scope (0x82f38 ..
   0x82f78 store 0 into each). *)
Definition headamp_A_shX : list Z := firstn 52 headamp_A_shB ++ repeat 0 17 ++ skipn 69 headamp_A_shB.

Lemma headamp_A_shX_facts : length headamp_A_shX = 80%nat /\ nth 48 headamp_A_shX 0 = 0 /\
nth 49 headamp_A_shX 0 = 4 /\ (forall g, (52 <= g < 69)%nat -> nth g headamp_A_shX 0 = 0).
Proof.
split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|]. split; [vm_compute; reflexivity|].
intros g Hg.
assert (E : forallb (fun k => Z.eqb (nth k headamp_A_shX 0) 0) (seq 52 17) = true) by (vm_compute; reflexivity).
rewrite forallb_forall in E. apply Z.eqb_eq. apply E. apply in_seq. lia.
Qed.

(* The 136 bytes of x (F + 0x1a0) are addressable when the seventeen x granules are 0. *)
Lemma hd_x_addressable : forall H mem F sh, hd_fsh segs H mem F sh -> F mod 8 = 0 -> length sh = 80%nat ->
(forall g, (52 <= g < 69)%nat -> nth g sh 0 = 0) ->
forall a m, F + 0x1a0 <= a -> a + m <= F + 0x228 -> range_addressable (aview segs H mem) SHADOW_OFF a m.
Proof.
intros H mem F sh Hsh Hal Hl Hg a m Ha Ham x Hx. exists 0. split; [|left; reflexivity].
pose proof (Z.div_mod (x - F) 8 ltac:(lia)) as D. pose proof (Z.mod_pos_bound (x - F) 8 ltac:(lia)) as M.
apply (hd_fsh_granule segs H mem F sh ((x - F) / 8) 0 Hsh Hal).
- rewrite Hl. lia.
- apply Hg. lia.
- lia.
Qed.

Lemma hd_garr8_at : forall m a b l, a = b -> garr8 segs m a l -> garr8 segs m b l.
Proof. intros m a b l -> H. exact H. Qed.

(* The three words of res. *)
Lemma hd_res_words : forall m a o, garr8 segs m a (hd_zbytes (ans_res_bytes o)) ->
val_mem segs m a 4 (ans_n o mod 2 ^ 32) /\ val_mem segs m (a + 4) 4 (ans_keys o mod 2 ^ 32) /\
val_mem segs m (a + 8) 4 (ans_rf o mod 2 ^ 32).
Proof.
intros m a o Hg. unfold ans_res_bytes, ha_res_bytes, hd_zbytes in Hg. rewrite !map_app in Hg.
apply garr8_app in Hg as [G0 Hg]. apply garr8_app in Hg as [G1 G2].
rewrite ?length_map, ?Mem.length_le4 in G1. rewrite ?length_map, ?Mem.length_le4 in G2.
split; [exact (hd_garr8_le4 segs _ _ _ G0)|].
split; [exact (hd_garr8_le4 segs _ _ _ G1)|].
apply (hd_garr8_le4 segs). eapply hd_garr8_at; [|exact G2]. lia.
Qed.

(* x's rc word, its cells and its keys and refusal words (struct expect, Spec/HeadBytes.v x_bytes). *)
Lemma hd_x_words : forall m a o, (length (ans_cells o) <= 10)%nat ->
garr8 segs m a (hd_zbytes (x_bytes o)) ->
val_mem segs m a 4 (ans_rc o mod 2 ^ 32) /\
garr8 segs m (a + 4) (hd_zbytes (x_cells_bytes (ans_cells o))) /\
val_mem segs m (a + X_KEYS_OFF) 4 (ans_keys o mod 2 ^ 32) /\
val_mem segs m (a + X_RF_OFF) 4 (ans_rf o mod 2 ^ 32).
Proof.
intros m a o Hl Hx. unfold x_bytes, ans_res_bytes, ha_res_bytes, hd_zbytes in Hx. rewrite !map_app in Hx.
apply garr8_app in Hx as [G0 Hx]. apply garr8_app in Hx as [G1 Hx]. apply garr8_app in Hx as [G2 Hx].
apply garr8_app in Hx as [G3 Hx]. apply garr8_app in Hx as [G4 G5].
rewrite ?length_map, ?Mem.length_le4, ?length_x_cells_bytes, ?repeat_length in G1.
rewrite ?length_map, ?Mem.length_le4, ?length_x_cells_bytes, ?repeat_length in G2.
rewrite ?length_map, ?Mem.length_le4, ?length_x_cells_bytes, ?repeat_length in G3.
rewrite ?length_map, ?Mem.length_le4, ?length_x_cells_bytes, ?repeat_length in G4.
rewrite ?length_map, ?Mem.length_le4, ?length_x_cells_bytes, ?repeat_length in G5.
unfold X_CELLS in G3, G4, G5.
split; [exact (hd_garr8_le4 segs _ _ _ G0)|].
split; [eapply hd_garr8_at; [|exact G1]; lia|].
split; [apply (hd_garr8_le4 segs); eapply hd_garr8_at; [|exact G4]; unfold X_KEYS_OFF; lia|].
apply (hd_garr8_le4 segs); eapply hd_garr8_at; [|exact G5]; unfold X_RF_OFF; lia.
Qed.

(* The frame for locals at any callee's call: aligned, below the stack window. *)
Lemma hd_check_frame : forall STK sp0 FP ly S W0 mem0 md0 own k T (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) pos,
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
e_F e mod 8 = 0 /\ 4096 <= e_F e /\ e_F e + 1024 <= 2 ^ 47 /\
(forall a m, e_F e <= a -> a + m <= e_F e + 1024 -> hd_off_stack regs T a m) /\
(forall c, c mod 4 = 0 -> (e_F e + c) mod 4 = 0).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc e pos HP Hown HF.
destruct (headamp_A_site_frame segs B STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc _ _ HP Hown)
  as (Hal & H4k & Hbelow & Hoff).
pose proof (hd_pre_sp0 STK sp0 FP ly S W0 mem0 md0 own k T regs lyc Sc W memc mdc HP) as (HSTK & Hsp & _).
rewrite <- HF in Hal, H4k, Hbelow, Hoff.
change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024 in Hbelow, Hoff.
split.
{ symmetry. apply (Z.mod_unique _ 8 (4 * (e_F e / 32)) 0); [left; lia|].
  pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). lia. }
split; [exact H4k|]. split; [lia|]. split; [exact Hoff|].
intros c Hc. symmetry. apply (Z.mod_unique _ 4 (8 * (e_F e / 32) + c / 4) 0); [left; lia|].
pose proof (Z.div_mod (e_F e) 32 ltac:(lia)). pose proof (Z.div_mod c 4 ltac:(lia)). lia.
Qed.

(* check_object(rc, res, x) at 0x836ac: x->rc = expect_of's rc = the parse's rc (hd_parse_expect: the record is
   uncorrupted on this path), so (rc = -1) and (x->rc = -1) agree and the contract's xrc is ans_rc o; for rc = -1
   res holds (0, 0, REFUSE_NONE). *)
Lemma headamp_A_site_object : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_A_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x180) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x1a0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
- 2 ^ 31 <= ans_rc o < 2 ^ 31 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x1a0) 4 (ans_rc o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x1a0) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x1a0) 4 /\ hd_app_rng segs (e_F e + 0x1a0) 4 /\ (e_F e + 0x1a0) mod 4 = 0 /\
(ans_rc o = -1 -> (e_F e + 0x180) mod 4 = 0 /\
 garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x180) (hd_zbytes (ha_res_bytes 0 0 0)) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x180) 12 /\
 hd_off_stack regs T_check_STK (e_F e + 0x180) 12 /\ hd_app_rng segs (e_F e + 0x180) 12 /\
 (e_F e + 0x180 + 12 <= e_F e + 0x1a0 \/ e_F e + 0x1a0 + 4 <= e_F e + 0x180)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words _ _ _ Hlc Hx) as (X0 & _ & _ & _).
destruct (hd_check_frame STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_A_shX_facts as (Xl & X48 & X49 & Xg).
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [exact X0|].
split; [apply (hd_x_addressable _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
split; [apply Hm4; reflexivity|].
intros Hm1. destruct Hcase as [(_ & _ & Hn & Hk & Hrf)|(Hr0 & _)]; [|lia].
split; [apply Hm4; reflexivity|].
split; [unfold ans_res_bytes in Hres; rewrite Hn, Hk, Hrf in Hres; exact Hres|].
split; [apply (hd_res_addressable _ _ _ _ Hsh F8 Xl X48 X49); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
lia.
Qed.

(* check_cells(out, rc, x) at 0x836bc: rc = x->rc <= cap <= 9 (so rc <= 10), out holds the parse's cells and x's
   cells are expect_of's, the same list; out is a live block and x lies in the frame, both below 2^47. *)
Lemma headamp_A_site_cells : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_A_shX ->
In (e_out e, 3 * (e_cap e + 1)) (ablocks B lyc Sc) ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x1a0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
- 2 ^ 31 <= ans_rc o <= 10 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x1a0) 4 (ans_rc o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x1a0) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x1a0) 4 /\ hd_app_rng segs (e_F e + 0x1a0) 4 /\ (e_F e + 0x1a0) mod 4 = 0 /\
(0 < ans_rc o ->
 Z.of_nat (length (ans_cells o)) = ans_rc o /\ Forall cell_bytes_ok (ans_cells o) /\
 0 <= e_out e /\ e_out e + 3 * ans_rc o <= 2 ^ 63 /\
 0 <= e_F e + 0x1a0 /\ e_F e + 0x1a0 + 4 + 12 * ans_rc o <= 2 ^ 63 /\
 garr8 segs (mrestrict (w_H W) memc) (e_out e) (hd_zbytes (ha_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_out e) (3 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_out e) (3 * ans_rc o) /\ hd_app_rng segs (e_out e) (3 * ans_rc o) /\
 garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x1a0 + 4) (hd_zbytes (x_cells_bytes (ans_cells o))) /\
 range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x1a0 + 4) (12 * ans_rc o) /\
 hd_off_stack regs T_check_STK (e_F e + 0x1a0 + 4) (12 * ans_rc o) /\
 hd_app_rng segs (e_F e + 0x1a0 + 4) (12 * ans_rc o) /\
 (e_out e + 3 * ans_rc o <= e_F e + 0x1a0 \/ e_F e + 0x1a0 + 4 + 12 * ans_rc o <= e_out e)).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hin Hwf Hcor Hcap Ho Hout Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & Hval).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words _ _ _ Hlc Hx) as (X0 & X1 & _ & _).
destruct (hd_check_frame STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_A_shX_facts as (Xl & X48 & X49 & Xg).
assert (Hrq : req_size (3 * (e_cap e + 1)) = 3 * (e_cap e + 1))
  by (unfold req_size; destruct (Z.eqb_spec (3 * (e_cap e + 1)) 0); lia).
pose proof (headamp_A_site_block segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc _ _ HP Hin)
  as (Hp4 & Hbelow & _ & HSTK & Hsp & Hra).
rewrite Hrq in Hbelow, Hra.
split; [destruct Hcase as [(Hm1 & _)|(Hr0 & _)]; lia|].
split; [exact X0|].
split; [apply (hd_x_addressable _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
split; [apply Hm4; reflexivity|].
intros Hpos. destruct Hcase as [(Hm1 & _)|(Hr0 & Hrl & _)]; [lia|].
split; [lia|].
split; [eapply Forall_impl; [|exact Hval]; exact cell_valid_bytes_ok|].
split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
split; [exact Hout|].
split; [exact (proj1 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
split; [exact (proj2 (Hra (e_out e) (3 * ans_rc o) ltac:(lia) ltac:(lia)))|].
split; [apply (headamp_A_site_block_app segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc
  _ _ _ _ HP Hin); lia|].
split; [exact X1|].
split; [apply (hd_x_addressable _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
(* out is a live block and x lies in the frame for locals: AR keeps them apart (YCbq.v sep_block_frame). *)
pose proof HP as (HJ & _). pose proof HJ as (HAR & _ & _ & _ & _ & Hfr & _).
assert (Hfin : In (hi_cid headamp_himg_A, pos) (frames Sc)) by (rewrite Hfr; apply in_or_app; left; exact Hown).
pose proof (YCbq.sep_block_frame segs B (YG0q.AR_laws_ok segs B) lyc Sc W memc mdc _ _ _ _ HAR Hin Hfin) as Hz.
unfold zdisjoint in Hz. cbn [fst snd] in Hz. rewrite <- HF in Hz.
change (fs_frame_bytes (hi_cid headamp_himg_A)) with 1024 in Hz. rewrite Hrq in Hz. lia.
Qed.

(* check_keys(res, x) at 0x836cc and check_refusal(res, x) at 0x836d8: res->keys / res->refusal (the parse's) and
   x->keys / x->refusal (expect_of's) are the same word, the contract's v. *)
Lemma headamp_A_site_keys : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_A_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x180) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x1a0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
(e_F e + 0x180) mod 4 = 0 /\ (e_F e + 0x1a0) mod 4 = 0 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x180 + 4) 4 (ans_keys o mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x1a0 + X_KEYS_OFF) 4 (ans_keys o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x180 + 4) 4 /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x1a0 + X_KEYS_OFF) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x180 + 4) 4 /\ hd_off_stack regs T_check_STK (e_F e + 0x1a0 + X_KEYS_OFF) 4 /\
hd_app_rng segs (e_F e + 0x180 + 4) 4 /\ hd_app_rng segs (e_F e + 0x1a0 + X_KEYS_OFF) 4 /\
(e_F e + 0x180 + 4 + 4 <= e_F e + 0x1a0 + X_KEYS_OFF \/ e_F e + 0x1a0 + X_KEYS_OFF + 4 <= e_F e + 0x180 + 4).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words _ _ _ Hlc Hx) as (_ & _ & XK & _).
destruct (hd_res_words _ _ _ Hres) as (_ & RK & _).
destruct (hd_check_frame STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_A_shX_facts as (Xl & X48 & X49 & Xg).
unfold X_KEYS_OFF in *.
split; [apply Hm4; reflexivity|]. split; [apply Hm4; reflexivity|].
split; [exact RK|]. split; [exact XK|].
split; [apply (hd_res_addressable _ _ _ _ Hsh F8 Xl X48 X49); lia|].
split; [apply (hd_x_addressable _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|]. split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
lia.
Qed.

Lemma headamp_A_site_refusal : forall STK sp0 FP ly S W0 mem0 md0 own k (regs : bvmap 5 word) lyc Sc W memc mdc
(e : hd_env) (pos : Z) (r : Model.pod_rec) (o : answer),
hd_pre segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc ->
In (hi_cid headamp_himg_A, pos) own -> e_F e = frame_addr lyc (hi_cid headamp_himg_A) pos ->
hd_fsh segs (w_H W) memc (e_F e) headamp_A_shX ->
Model.pod_rec_wf r -> Model.corrupt r = false -> 0 <= e_cap e <= 9 ->
o = Headamp.parse_props (hd_props (e_null e) (Model.buf r)) (e_cap e) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x180) (hd_zbytes (ans_res_bytes o)) ->
garr8 segs (mrestrict (w_H W) memc) (e_F e + 0x1a0)
  (hd_zbytes (x_bytes (Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r))) ->
(e_F e + 0x180) mod 4 = 0 /\ (e_F e + 0x1a0) mod 4 = 0 /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x180 + 8) 4 (ans_rf o mod 2 ^ 32) /\
val_mem segs (mrestrict (w_H W) memc) (e_F e + 0x1a0 + X_RF_OFF) 4 (ans_rf o mod 2 ^ 32) /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x180 + 8) 4 /\
range_addressable (aview segs (w_H W) memc) SHADOW_OFF (e_F e + 0x1a0 + X_RF_OFF) 4 /\
hd_off_stack regs T_check_STK (e_F e + 0x180 + 8) 4 /\ hd_off_stack regs T_check_STK (e_F e + 0x1a0 + X_RF_OFF) 4 /\
hd_app_rng segs (e_F e + 0x180 + 8) 4 /\ hd_app_rng segs (e_F e + 0x1a0 + X_RF_OFF) 4 /\
(e_F e + 0x180 + 8 + 4 <= e_F e + 0x1a0 + X_RF_OFF \/ e_F e + 0x1a0 + X_RF_OFF + 4 <= e_F e + 0x180 + 8).
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own k regs lyc Sc W memc mdc e pos r o HP Hown HF Hsh Hwf Hcor Hcap Ho Hres Hx.
assert (E : Headamp.expect_model (negb (e_null e =? 0)) (e_cap e) r = o)
  by (rewrite Ho; symmetry; apply hd_parse_expect; assumption).
rewrite E in Hx.
pose proof (Headamp.parse_props_total (hd_props (e_null e) (Model.buf r)) (e_cap e) ltac:(lia)) as Hok.
rewrite <- Ho in Hok. apply answer_ok_parts in Hok as (Hcase & _).
assert (Hlc : (length (ans_cells o) <= 10)%nat)
  by (destruct Hcase as [(_ & Hc & _)|(Hr & Hl & _)]; [rewrite Hc; cbn [length]; lia | lia]).
destruct (hd_x_words _ _ _ Hlc Hx) as (_ & _ & _ & XR).
destruct (hd_res_words _ _ _ Hres) as (_ & _ & RR).
destruct (hd_check_frame STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF)
  as (F8 & F4 & Ftop & Hoff & Hm4).
pose proof headamp_A_shX_facts as (Xl & X48 & X49 & Xg).
unfold X_RF_OFF in *.
split; [apply Hm4; reflexivity|]. split; [apply Hm4; reflexivity|].
split; [exact RR|]. split; [exact XR|].
split; [apply (hd_res_addressable _ _ _ _ Hsh F8 Xl X48 X49); lia|].
split; [apply (hd_x_addressable _ _ _ _ Hsh F8 Xl Xg); lia|].
split; [apply Hoff; lia|]. split; [apply Hoff; lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
split; [apply (hd_app_F segs B STK sp0 FP ly S W0 mem0 md0 own k T_check_STK regs lyc Sc W memc mdc e pos HP Hown HF);
  lia|].
lia.
Qed.
End p.

(* The image hypotheses of the parse lemmas hold at image A's own segments (lib/A/Img0.v, the snapshot of the
   pinned fuzz_headamp.asan): the parse's two doubles, the stack-guard GOT word and the guard lie in loaded
   segments; every loaded segment lies below kLowMemEnd (YCbq.v's segs_low); the read-only window of lib/A/HPgLib.v,
   0x9bc80 .. 0x9d068 (RO_LO .. RO_HI), lies in one loaded segment. *)
Lemma headamp_A_img_bytes_rsegs : headamp_A_img_bytes Img0.rsegs.
Proof.
intros a Ha i Hi. cbn [In] in Ha.
destruct Ha as [<-|[<-|[<-|[<-|[]]]]];
  (apply (HPgSat.img_chk_ok Img0.rsegs _ 8); [vm_compute; reflexivity | lia]).
Qed.

Lemma headamp_A_segs_low : forall a, in_img Img0.rsegs a -> 0 <= a < kLowMemEnd.
Proof.
assert (E : forallb (fun sg => Z.of_N (seg_base sg) + Z.of_N (seg_size sg) <=? kLowMemEnd) Img0.rsegs = true)
  by (vm_compute; reflexivity).
intros a (sg & Hin & Hr). rewrite forallb_forall in E. specialize (E sg Hin). apply Z.leb_le in E. lia.
Qed.

Lemma headamp_A_relro_img : forall a, 0x9bc80 <= a < 0x9d068 -> in_img Img0.rsegs a.
Proof.
assert (E : existsb (fun sg => (Z.of_N (seg_base sg) <=? 0x9bc80) &&
  (0x9d068 <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) Img0.rsegs = true) by (vm_compute; reflexivity).
intros a Ha. apply existsb_exists in E as (sg & Hin & Hb). apply andb_prop in Hb as [H1 H2].
apply Z.leb_le in H1. apply Z.leb_le in H2. exists sg. split; [exact Hin | lia].
Qed.

Print Assumptions hd_len_bounds.
Print Assumptions headamp_A_site_malloc_pod.
Print Assumptions headamp_A_site_malloc_out.
Print Assumptions headamp_A_site_malloc_first.
Print Assumptions hd_cut_keep.
Print Assumptions headamp_A_site_cut3.
Print Assumptions headamp_A_site_cut5.
Print Assumptions headamp_A_site_cut7.
Print Assumptions headamp_A_site_strs.
Print Assumptions hd_shr_mod.
Print Assumptions hd_nth_le_bytes.
Print Assumptions hd_nth_guard.
Print Assumptions hd_val_mem_kept.
Print Assumptions hd_garr8_le4.
Print Assumptions headamp_A_site_block.
Print Assumptions headamp_A_site_frame.
Print Assumptions headamp_A_site_block_app.
Print Assumptions headamp_A_site_frame_app.
Print Assumptions hd_app_F.
Print Assumptions headamp_A_site_frame_at.
Print Assumptions hd_fsh_granule.
Print Assumptions headamp_A_site_no_overrun.
Print Assumptions headamp_A_site_count.
Print Assumptions headamp_A_site_cells_valid.
Print Assumptions headamp_A_site_plain.
Print Assumptions hd_parse_expect.
Print Assumptions hd_buf_len8.
Print Assumptions hd_kept_refl.
Print Assumptions hd_pre_sp0.
Print Assumptions hd_cctx_of.
Print Assumptions hd_cctx_facts.
Print Assumptions hd_inw_w3.
Print Assumptions hd_block_not_img.
Print Assumptions hd_kept_at.
Print Assumptions hd_kept_img.
Print Assumptions hd_kept_shimg.
Print Assumptions hd_kept_tail.
Print Assumptions hd_kept_hull.
Print Assumptions hd_kept_block.
Print Assumptions hd_garr8_kept.
Print Assumptions hd_cstr_kept.
Print Assumptions hd_cstr_call.
Print Assumptions hd_rdword_kept.
Print Assumptions headamp_A_site_parse_core.
Print Assumptions headamp_A_shB_facts.
Print Assumptions hd_res_addressable.
Print Assumptions headamp_A_site_parse_args.
Print Assumptions headamp_A_site_parse_args_plain.
Print Assumptions headamp_A_shX_facts.
Print Assumptions hd_x_addressable.
Print Assumptions hd_garr8_at.
Print Assumptions hd_res_words.
Print Assumptions hd_x_words.
Print Assumptions hd_check_frame.
Print Assumptions headamp_A_site_object.
Print Assumptions headamp_A_site_cells.
Print Assumptions headamp_A_site_keys.
Print Assumptions headamp_A_site_refusal.
Print Assumptions headamp_A_img_bytes_rsegs.
Print Assumptions headamp_A_segs_low.
Print Assumptions headamp_A_relro_img.
