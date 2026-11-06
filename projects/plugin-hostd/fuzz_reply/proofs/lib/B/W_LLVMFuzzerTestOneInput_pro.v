(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: SEG_PRO of the ASan+UBSan walk of fuzz_reply's LLVMFuzzerTestOneInput, image B
   (lib/B/W_LLVMFuzzerTestOneInput_cut.v:942, `forall cx, lf_base cx -> SRr segs (c_W cx) (lf_entry cx) (INV_H cx 0)`)
   - the prologue 0x84408-0x845e0 (fuzz_reply.c:671-685), from the entry to the loop head H.  The image-B twin of
   lib/A/W_LLVMFuzzerTestOneInput_pro.v (a working branch fff279dd36e), in the form of the cut's worked
   dispatch lf_seg_jt and of that twin's five pieces.  Every B fact below is read from B's own disassembly
   (the objdump of the pinned image fuzz_reply.asan-ubsan, sha256 10ffb5f9202ae2bd...)
   and from lib/B's listing, never by offset arithmetic from image A.
   Rule 24: no released, delivered-package or cold lemma proves this statement (proof-index, 2026-10-29: 0 named / 0
   released / the delivered package 0 on 0x84408, 0x84478, 0x84590 and on __asan_stack_malloc_1 at this function).  An OLD-FRAME B
   donor exists (a working branch fc302b5d067, structure only); no citable proof.  Its files lib/B/Prog/SlotEntry.v,
   SlotEntryDefs.v and SlotEntryAlloc.v (a_call_pre / a_call_post over ALI, no afn_pre / ajournal_gx / AR_laws / SRr)
   decompose this very prologue as: entry state -> __asan_stack_malloc_1 at 0x84478 with a0 = 128 (class 1, its flag
   byte and the frame's shadow) -> the size test AE_TEST 0x84530 -> op_add's entry with the globals reset (g_client
   3; g_client_broken, g_gone, g_send_dead, g_send_eintr, g_nfd, g_send_max 0) -> AE_OPRET 0x84594.  That
   decomposition is the one walked here; no text, lemma or proof step was copied from it.

   The segment: the frame (320 bytes, sp aligned down to 32, s1 = F), the ASan fake frame of class 1
   (__asan_stack_malloc_1 at 0x84478, 128 bytes) with its header and shadow, the size refusal (n >> 26 <> 0 at
   0x84530, to 0x85014) refuted by the contract's n < 2^26, the globals' reset (g_client = 3, g_client_broken,
   g_nfd, g_send_max, g_gone, g_send_dead, g_send_eintr = 0), op_add() at 0x84590, and the loop's set-up
   (0x84594-0x845dc: the frame slots F+48, F+96, F+120, F+128, F+136, F+152 and the registers s2, s7, s9, s10), to
   the head 0x845e0.
   lf_seg_pro (the statement of _cut.v's SEG_PRO) is proved here; the pieces are pro_entry (the entry state), the
   walk to __asan_stack_malloc_1 and the fake-frame seat, the global stores and the token run to op_add's entry,
   pro_at_call (op_add's entry state), pro_mid (op_add at its own G, oa_spec_g at pro_G, its journal lifted to G_fr)
   and pro_fin (the loop's set-up 0x84594-0x845dc, to the head).

   ------------------------------------------------------------------ B against A (the twin), fact by fact
   (2) THE LOOP TEST IS AT THE HEAD.  B's `beqz s5,84e64` IS the head instruction (0x845e0), so the prologue walks
       into INV_H whatever n is: B's SEG_PRO lands on INV_H ALONE, with 0 <= lm_k m = 0 <= c_n cx.  A's pro_fin had
       to split on `beqz s5` at 0x84244 and land on INV_H \/ INV_X; B has NO empty-input exit of its own and no
       `\/ INV_X` here.
   (3) NO `full` FLAG.  B stores every frame slot before the head, so aframe_at has no flag and pro_aframe proves
       the whole frame at the single cut point; A's `pro_aframe cx full` and its `full = false` case are gone.
   (4) B'S REGISTERS AND FRAME SLOTS.  s11 = SB (A: s10), s9 = t = 0 (A: s11), s7 = 1 (A: t2), s4 / t1 the cursor
       and the bytes left (A: t3 / t4), s5 = n at entry, s6 = p, s10 = HI_G_NOUT (A: s9), s2 = HI_G_SRC, s3 = FF+32,
       s8 = SB + FF/8.  B has no g_nsrc high half in a register (A: s7) and no modulus register (A: s4 = 10).
       Frame: F+32 HI_G_CLIENT, F+40 HI_G_SDEAD, F+48 g_s, F+56 HI_G_SEINTR, F+64 HI_G_GONE, F+72 HI_G_SMAX,
       F+80 the fake frame, F+96 SB + FF/8, F+104 FF, F+120 SB + g_s/8, F+128 g_s+4, F+136 DIV10,
       F+152 SB + (g_s+4)/8, F+184 FF (A: F+24/32/48/56/64/72/80/88/96/104/112/120/128/136/152/184).
       So the walk's two frame windows are F+[32,192) before op_add (A: F+[24,208)) and F+[48,160) after it.
   (6) B's FAKE FRAME IS REAL: B calls __asan_stack_malloc_1 ITSELF at 0x84478 (li a0,128 at 0x84474) and keeps the
       frame, its flag word at F+104 / FF+120, the 16 shadow bytes and the header, exactly as A does.  (The port's
       note that the fake frame belongs to `wake` alone is FALSE for this function: 0x84474-0x84488 and 0x8506c.)
   The auipc hi slots this file names, read from B's listing (A_HI j) and checked by vm_compute at PB_fr:
     A_HI 56/57 the GOT slots of the shadow base (A_OBJ 0) and of the stack-use-after-return word (A_OBJ 6);
     A_HI 58 -> A_OBJ 22 = 0x1239d (the fake frame's magic word), A_HI 59 -> A_TEXT + 0x20c4 = 0x84408;
     A_HI 60 = 0xa2540 (g_client = +32), 61 = 0x5d9548 (g_client_broken = -2024), 62 = 0x5d954c (g_nfd = -1964),
     63 = 0x5d9550 (g_send_max = -1936), 64 = 0x5d955c (g_gone = -1916), 65 = 0x5d9564 (g_send_dead = -1892),
     66 = 0x5d956c (g_send_eintr = -1868), 67 -> A_OBJ 19 = g_s, 68 -> A_OBJ 23 = 0x10320 (the /10 multiplier),
     69 = HI_G_NOUT, 70 = HI_G_SRC.
   TRAP COUNT 0: the cut's trap table gives SEG_PRO no UBSan trap branch (the size test at 0x84530 is the C
   `if (size > 64 MiB) return 0`, not a trap edge, and it is refuted by the contract's n < 2 ^ 26).

   ------------------------------------------------------------------ what this file takes (all Section hypotheses)
     LAWS / HG / RINV / LS / the contract parameters - _cut's Section w, verbatim;
     OA - op_add's published G-generic contract, lib/B/W_op_add.v oa_spec_g (pb_op_add_g), taken at pro_G;
     TL, TLF, ML, SMP, FFL - the allocator instance (lib/B/W_kit.v PALib, lib/B/W_frame.v PALibF, model_laws,
       stack_malloc_progressP, frame_flag_lawP);
     ASM1 - astack_malloc_pres segs B 1 (lib/B/W_frame.v), the class-1 fake-frame site rule;
     GWL, ERRL - _cut's shared laws glob_wr_law / errno_law, verbatim;
     HEV, HZS, HGOBJ, HRO, GSHV - the instance facts, in lib/A's texts at lib/B's names, but HRO (rom_out at G_fr,
       the B sibling's text) for lib/A's ROM_PIN + HROM_G: rom_out names the sink head's AOFL_HEAD, a Context
       parameter here, so only the instance's head decides it (see the hypotheses below);
     HFP_pro, LS_pro_oa, LS_pro, RI_pro - the four model obligations, in the B form (no `full`, k = 0 at the head).
   lib/B has no latch file at this base, so the transport kit lib/A's pro file read from
   lib/A/W_LLVMFuzzerTestOneInput_latch.v (its lt_ lemmas) is restated here at image B's names, as
   lib/B/W_LLVMFuzzerTestOneInput_add.v (a working branch e234f421174) restates it. *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YK1j.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn YP0b YP0a YP07.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YN3v YI04 YI00.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0v.
(* YG0s: frame_facts / client_byte_not_img, for the frame-vs-image bound at image B's top (pro_frm_img_hi) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YG0s.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
(* the same YCbq as lib/B/W_journal.v and the cut (Reusable's) *)
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
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import HarnessRep RelayRep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import W_rep W_contract W_frame W_op_add.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require ReplyGuardB.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import
W_LLVMFuzzerTestOneInput_cut W_LLVMFuzzerTestOneInput_G.
(* the key-text helpers the relay entry's footprint names (lib/B/W_rep.v's) *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.Prog Require Import gestures_end_b_c.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Open Scope bv_scope.
Open Scope Z_scope.
(* the program interface's stack bound, from the generated lib/B/YCfn.v (the cut's local notation) *)
Local Notation LLVMF_STK := YCfn.LLVMF_STK.

(* ------------------------------------------------------------------ the segment's addresses (offsets from fr_B0) *)
Definition A_pro : Z := AF_fr_LLVMFuzzerTestOneInput.                    (* 0x84408 the entry *)
Definition A_pro_ret : Z := AF_fr_LLVMFuzzerTestOneInput + 0x18c.        (* 0x84594 after op_add() *)
(* the frame: s1 = F = (sp0 - 320) rounded down to 32; the slots the prologue stores lie in [F + 32, F + 192) *)
Definition pro_F (regs : bvmap 5 word) : Z := (spZ regs - 320) - (spZ regs - 320) mod 32.

(* ------------------------------------------------------------------ list and range helpers *)
Lemma pro_nd_app : forall (A : Type) (l1 l2 : list A) x, List.NoDup (l1 ++ l2) -> In x l1 -> ~ In x l2.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 x Hnd Hx Hx2; [destruct Hx|].
  cbn [app] in Hnd. inversion Hnd as [|? ? Hni Hnd']; subst.
  destruct Hx as [<- | Hx]; [apply Hni; apply in_or_app; right; exact Hx2 | exact (IH l2 x Hnd' Hx Hx2)].
Qed.
Lemma pro_nd_appr : forall (A : Type) (l1 l2 : list A), List.NoDup (l1 ++ l2) -> List.NoDup l2.
Proof.
  intros A l1. induction l1 as [|y l1 IH]; intros l2 Hnd; [exact Hnd|].
  cbn [app] in Hnd. apply NoDup_cons_iff in Hnd as [_ Hnd]. exact (IH l2 Hnd).
Qed.
(* no range of G meets [lo, lo + n) *)
Definition pro_apart (lo n : Z) (G : list (Z * Z)) : bool :=
  forallb (fun r => (fst r + snd r <=? lo) || (lo + n <=? fst r)) G.
Lemma pro_apart_ok : forall lo n G, pro_apart lo n G = true -> forall a, inG G a -> ~ (lo <= a < lo + n).
Proof.
  intros lo n G H a Ha Hr. unfold pro_apart in H. rewrite forallb_forall in H.
  unfold inG in Ha. apply Exists_exists in Ha as (r & Hin & Hz). specialize (H r Hin).
  apply orb_true_iff in H as [H | H]; apply Z.leb_le in H; unfold in_zr in Hz; lia.
Qed.
(* every range of G1 lies inside one of G2 *)
Lemma pro_sub_of_b : forall G1 G2, forallb (fun r => rng_inb (fst r) (snd r) G2) G1 = true ->
  forall a, inG G1 a -> inG G2 a.
Proof.
  intros G1 G2 H a Ha. unfold inG in Ha. apply Exists_exists in Ha as (r & Hr & Hz).
  rewrite forallb_forall in H. exact (rng_cover_zr (fst r) (snd r) G2 (H r Hr) a Hz).
Qed.
Lemma pro_inG_rng : forall G lo n a, In (lo, n) G -> lo <= a < lo + n -> inG G a.
Proof. intros G lo n a Hin Ha. unfold inG. apply Exists_exists. exists (lo, n). split; [exact Hin | exact Ha]. Qed.

(* ------------------------------------------------------------------ op_add's own globals (ARM_add's ad_G) *)
(* op_add writes g_s's four slots, g_nfd and relay_add's four words; it never names errno, so gx_prog can hold.
   The same list as lib/B/W_LLVMFuzzerTestOneInput_add.v's ad_G. *)
Definition pro_G : list (Z * Z) := [(rg_s fr_globals, 4 * ASRC); (A_NFD, 4)] ++ RA_G fr_globals.
Lemma pro_G_eq : pro_G = [(0x5d8e60, 384); (0x5d8da0, 4); (0x5d9040, 12); (0x5d8d20, 4); (0x5d8d80, 4); (0x5d8d40, 8)].
Proof. reflexivity. Qed.
Lemma pro_G_obj : forall a, inG pro_G a -> inG G_fr_obj a.
Proof. apply pro_sub_of_b. vm_compute. reflexivity. Qed.
(* the cells the prologue keeps from the entry to op_add's call: the four sources, the stream's counters,
   g_wake[1], g_thread_up, g_listen and relay_add's globals *)
Definition G_keep : list (Z * Z) :=
  [(rg_s fr_globals, 4 * ASRC); (rg_nout fr_globals, 8); (rg_capout fr_globals, 8); (rg_out fr_globals, 8);
   (rg_wake fr_globals + 4, 4); (AG_THREAD_UP, 1); (AG_LISTEN, 4)] ++ RA_G fr_globals.
(* the cells op_add keeps: the stream's, g_gone, g_wake[1], g_thread_up, g_listen *)
Definition G_pst : list (Z * Z) :=
  [(rg_send_max fr_globals, 8); (rg_nout fr_globals, 8); (rg_capout fr_globals, 8); (rg_out fr_globals, 8);
   (rg_client fr_globals, 4); (rg_client_broken fr_globals, 1); (rg_send_dead fr_globals, 1);
   (rg_send_eintr fr_globals, 1); (rg_gone fr_globals, 1); (rg_wake fr_globals + 4, 4); (AG_THREAD_UP, 1);
   (AG_LISTEN, 4)].
Lemma G_keep_obj : forall a, inG G_keep a -> inG G_fr_obj a.
Proof. apply pro_sub_of_b. vm_compute. reflexivity. Qed.
Lemma G_pst_obj : forall a, inG G_pst a -> inG G_fr_obj a.
Proof. apply pro_sub_of_b. vm_compute. reflexivity. Qed.
Lemma G_pst_oa : forall a, inG G_pst a -> ~ inG pro_G a.
Proof.
  intros a Ha HO. pose proof (rng_all_in (fun x => negb (inGb pro_G x)) G_pst a ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply negb_true_iff in H. apply inGb_false in H. exact (H HO).
Qed.
Lemma G_obj_rng : forall a, inG G_fr_obj a -> 0x10000 <= a < 0x5fc000.
Proof.
  intros a Ha.
  pose proof (rng_all_in (fun x => (0x10000 <=? x) && (x <? 0x5fc000)) G_fr_obj a
    ltac:(vm_compute; reflexivity) Ha) as H.
  cbv beta in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia.
Qed.
(* the seven global stores of 0x84558-0x8458c, as byte ranges *)
Definition pro_gst_out (a : Z) : Prop :=
  ~ (0xa2560 <= a < 0xa2564) /\ ~ (0x5d8d60 <= a < 0x5d8d61) /\ ~ (0x5d8da0 <= a < 0x5d8da4) /\
  ~ (0x5d8dc0 <= a < 0x5d8dc8) /\ ~ (0x5d8de0 <= a < 0x5d8de1) /\ ~ (0x5d8e00 <= a < 0x5d8e01) /\
  ~ (0x5d8e20 <= a < 0x5d8e21).
Definition pro_gstb (x : Z) : bool :=
  negb (((0xa2560 <=? x) && (x <? 0xa2564)) || ((0x5d8d60 <=? x) && (x <? 0x5d8d61)) ||
        ((0x5d8da0 <=? x) && (x <? 0x5d8da4)) || ((0x5d8dc0 <=? x) && (x <? 0x5d8dc8)) ||
        ((0x5d8de0 <=? x) && (x <? 0x5d8de1)) || ((0x5d8e00 <=? x) && (x <? 0x5d8e01)) ||
        ((0x5d8e20 <=? x) && (x <? 0x5d8e21))).
Lemma rng_bfalse : forall lo hi a, ((lo <=? a) && (a <? hi)) = false -> ~ (lo <= a < hi).
Proof. intros lo hi a H [H1 H2]. rewrite (proj2 (Z.leb_le _ _) H1), (proj2 (Z.ltb_lt _ _) H2) in H. discriminate H. Qed.
Lemma pro_gstb_ok : forall a, pro_gstb a = true -> pro_gst_out a.
Proof.
  intros a H. unfold pro_gstb in H. apply negb_true_iff in H. rewrite !orb_false_iff in H.
  destruct H as ((((((H1 & H2) & H3) & H4) & H5) & H6) & H7).
  repeat split; apply rng_bfalse; assumption.
Qed.
Lemma G_keep_gst : forall a, inG G_keep a -> pro_gst_out a.
Proof. intros a Ha. apply pro_gstb_ok. exact (rng_all_in pro_gstb G_keep a ltac:(vm_compute; reflexivity) Ha). Qed.

Section kit.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
#[local] Notation segs := (@pa_segs _ fr_prog_listing PB_fr).
Variable B : asyms.
Hypothesis LAWS : AR_laws segs B.

(* off the image, a byte that is writable is present, so its view carries its writability *)
Lemma ad_wr_offimg : forall (H : word -> bool) (m : word -> option byte) a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> writable_at segs (mrestrict H m) a -> apresent H m a.
Proof.
  intros H m a Ha Hni Hw.
  assert (Hseg : wview segs (fun _ => None) (Z_to_bv 64 a) = None).
  { unfold wview. cbv beta iota.
    destruct (find_segment segs (bv_unsigned (Z_to_bv 64 a)) 1) as [seg|] eqn:Ef; [|reflexivity].
    exfalso. apply Hni. exists seg. pose proof (find_segment_in _ _ _ _ Ef) as Hin.
    pose proof (find_segment_range _ _ _ _ Ef) as Hr. rewrite unsigned_lit_small in Hr by lia.
    split; [exact Hin | lia]. }
  unfold writable_at, mrestrict in Hw. unfold apresent.
  destruct (H (Z_to_bv 64 a)) eqn:Eh.
  - exfalso. apply Hw. unfold wview in Hseg |- *. rewrite ?Eh. exact Hseg.
  - destruct (m (Z_to_bv 64 a)) as [b|] eqn:Em; [split; [reflexivity | exists b; reflexivity]|].
    exfalso. apply Hw. unfold wview in Hseg |- *. rewrite ?Eh, ?Em. exact Hseg.
Qed.
Lemma ad_offimg_kept : forall (W W' : world segs) mem mem' a,
  0 <= a < 2 ^ 64 -> ~ in_img segs a -> aview segs (w_H W') mem' a = aview segs (w_H W) mem a ->
  abyte_kept W mem W' mem' a.
Proof.
  intros W W' mem mem' a Ha Hni Hv. split; [exact Hv|]. intros Hw.
  apply apresent_writable. apply (apresent_transfer segs (w_H W) (w_H W') mem mem' a Ha Hni Hv).
  exact (ad_wr_offimg (w_H W) mem a Ha Hni Hw).
Qed.
Lemma ad_sv8_view : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8, arm in *.
  apply (val_mem_moved segs (w_H W) (w_H W') mem mem' a a 8 v); [|exact Hv].
  intros j Hj. apply HK. cbn in Hj. lia.
Qed.
Lemma ad_vm_view : forall (W W' : world segs) mem mem' a (n : nat) v,
  (forall x, a <= x < a + Z.of_nat n -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  val_mem segs (arm W mem) a n v -> val_mem segs (arm W' mem') a n v.
Proof.
  intros W W' mem mem' a n v HK Hv. unfold arm in *.
  apply (val_mem_moved segs (w_H W) (w_H W') mem mem' a a n v); [|exact Hv].
  intros j Hj. apply HK. lia.
Qed.

(* ---- the transport kit (lib/A/W_LLVMFuzzerTestOneInput_latch.v's, at image B's names): every byte the cut
   invariant reads outside the caller's own frame -- the globals, the relay's table, the harness's sources, the heap
   blocks, the input and the fake frame with its shadow -- lies below alloc_ceiling + 8 ---- *)
Definition CEIL8 : Z := alloc_ceiling + 8.
Definition lt_fp_low (fp : list (Z * Z)) : Prop := Forall (fun r => 0 <= fst r /\ snd r <= CEIL8) fp.
Lemma lt_ceil_lo : 0x7fff7f800000 <= alloc_ceiling.
Proof. pose proof asan_consts as (C1 & _). lia. Qed.
Lemma lt_ceil_hi : CEIL8 < 2 ^ 64.
Proof. unfold CEIL8. pose proof asan_consts as (C1 & _). lia. Qed.
(* a bound on a range of fuzz_reply.asan-ubsan's globals *)
Ltac lt_low :=
  cbn [fst snd gfp]; unfold CEIL8 in *;
  cbn [fr_globals fr_globals_b rg_s rg_src rg_nsrc rg_capsrc rg_out rg_nout rg_capout rg_send_max rg_send_eintr
       rg_send_dead rg_gone rg_client rg_client_broken rg_lock rg_wake] in *;
  pose proof lt_ceil_lo; lia.
Lemma lt_fp_low_nil : lt_fp_low []. Proof. constructor. Qed.
Lemma lt_fp_low_cons : forall r fp, 0 <= fst r -> snd r <= CEIL8 -> lt_fp_low fp -> lt_fp_low (r :: fp).
Proof. intros r fp H1 H2 H3. constructor; [split; assumption | exact H3]. Qed.
Lemma lt_fp_low_app : forall f1 f2, lt_fp_low f1 -> lt_fp_low f2 -> lt_fp_low (f1 ++ f2).
Proof. intros f1 f2 H1 H2. apply Forall_app. split; assumption. Qed.
Lemma lt_fp_low_forall : forall fp, lt_fp_low fp <-> (forall r, In r fp -> 0 <= fst r /\ snd r <= CEIL8).
Proof. intros fp. unfold lt_fp_low. apply Forall_forall. Qed.
Lemma lt_akept_of_low : forall (W : world segs) mem (W' : world segs) mem' fp,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> lt_fp_low fp -> akept W mem W' mem' fp.
Proof.
  intros W mem W' mem' fp HK Hl r Hr a Ha. rewrite lt_fp_low_forall in Hl.
  destruct (Hl r Hr) as [H1 H2]. apply HK. lia.
Qed.
Lemma lt_akept_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= CEIL8 ->
  akept W mem W' mem' [(lo, hi)].
Proof.
  intros W W' mem mem' lo hi HK H1 H2. apply lt_akept_of_low; [exact HK|].
  apply lt_fp_low_cons; [cbn; lia | cbn; lia | apply lt_fp_low_nil].
Qed.
Lemma lt_akept_of_rng : forall (W W' : world segs) mem mem' lo hi,
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> 0 <= lo -> hi <= CEIL8 ->
  forall x, lo <= x < hi -> abyte_kept W mem W' mem' x.
Proof. intros W W' mem mem' lo hi HK H1 H2 x Hx. apply HK. lia. Qed.

(* a live block: its bytes lie in the heap *)
Lemma lt_blk : forall ly S (W : world segs) mem md p n,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) ->
  4096 <= p /\ p + req_size n <= alloc_ceiling /\ 0 <= n <= req_size n.
Proof.
  intros ly S W mem md p n HAR Hin.
  destruct (al_blocks _ _ LAWS ly S W mem md p n HAR Hin) as (_ & H1 & H2 & _ & _ & _ & H3).
  pose proof (req_size_pos n ltac:(lia)) as [Hr1 Hr2]. split; [lia|]. split; [lia | lia].
Qed.
Lemma lt_bzs_len : forall l, Z.of_nat (length (bzs l)) = Z.of_nat (length l).
Proof. intros l. unfold bzs. rewrite length_map. reflexivity. Qed.
Lemma lt_text_rec_len : forall r, length (text_rec r) = 16%nat.
Proof. intros r. unfold text_rec. rewrite length_app. reflexivity. Qed.
Lemma lt_concat_len : forall rs, length (concat (map text_rec rs)) = (16 * length rs)%nat.
Proof.
  induction rs as [|r rs IH]; [reflexivity|].
  cbn [map concat]. rewrite length_app, lt_text_rec_len, IH. cbn [length]. lia.
Qed.
Lemma lt_key_ptrs_len : forall ks, length (gestures_end_b_c.key_ptrs ks) = (8 * length ks)%nat.
Proof.
  induction ks as [|k ks IH]; [reflexivity|].
  unfold gestures_end_b_c.key_ptrs in *. cbn [map concat]. rewrite length_app, IH, Mem.length_le8.
  cbn [length]. lia.
Qed.

(* ---- struct list ---- *)
Lemma lt_alist : forall ly S (W : world segs) mem md LA l lines,
  AR segs B ly S W mem md -> alist_at B ly S W mem LA l lines -> 0 <= LA -> LA + 16 <= CEIL8 ->
  lt_fp_low (alist_fp LA l) /\ (forall b, In b (alist_blks l) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md LA l lines HAR (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H9) HL0 HL1.
  assert (HREC : lt_fp_low (map (fun r => gfp (fst r) (bzs (snd r ++ [Z_to_bv 8 0]))) (hl_recs l))
                 /\ (forall b, In b (map (fun r => (fst r, Z.of_nat (length (snd r)) + 1)) (hl_recs l)) ->
                       In b (ablocks B ly S))).
  { rewrite Forall_forall in H9. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (x & <- & Hx).
      destruct (H9 x Hx) as (K1 & _). destruct (lt_blk ly S W mem md _ _ HAR K1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (x & <- & Hx). exact (proj1 (H9 x Hx)). }
  destruct HREC as [HR1 HR2].
  unfold alist_fp, alist_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; lia|]. apply lt_fp_low_app; [|exact HR1].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & Hj & Hg)]; [lia|].
    destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
    cbn [gfp fst snd]. rewrite lt_bzs_len, length_app, lt_concat_len.
    unfold hl_n in Hj. unfold AREC in *. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb]; [|exact (HR2 b Hb)].
    destruct (Z.eqb_spec (hl_cap l) 0) as [Hc|Hc]; [destruct Hb|].
    destruct H6 as [[Hc0 _] | (Hcp & Hin & _)]; [lia|].
    destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- struct source ---- *)
Lemma lt_asrc : forall ly S (W : world segs) mem md HA h,
  AR segs B ly S W mem md -> asrc_at B ly S W mem HA h -> 0 <= HA -> HA + ASRC <= CEIL8 ->
  lt_fp_low (asrc_fp HA h) /\ (forall b, In b (asrc_blks h) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md HA h HAR HS HL0 HL1.
  pose proof HS as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hpend & _ & _ & _ & _ & _ & _ & _ & Hpb & Hpj & _ &
                    _ & Hexp & Hheld & _).
  destruct (lt_alist ly S W mem md (HA + 16) (hs_pending h) false HAR Hpend ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [A1 A2].
  destruct (lt_alist ly S W mem md (HA + 64) (hs_expected h) true HAR Hexp ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [E1 E2].
  destruct (lt_alist ly S W mem md (HA + 80) (hs_held h) true HAR Hheld ltac:(unfold ASRC in *; lia)
                     ltac:(unfold ASRC in *; lia)) as [H1 H2].
  destruct (lt_blk ly S W mem md _ _ HAR Hpb) as (P1 & P2 & P3).
  unfold asrc_fp, asrc_blks. split.
  - apply lt_fp_low_cons; [cbn; lia | cbn; unfold ASRC in *; lia|].
    apply lt_fp_low_cons.
    + cbn [gfp fst]. lia.
    + cbn [gfp snd]. rewrite lt_bzs_len, Hpj. unfold APARTIAL, CEIL8 in *. lia.
    + apply lt_fp_low_app; [exact A1|]. apply lt_fp_low_app; [exact E1 | exact H1].
  - intros b [<- | Hb]; [exact Hpb|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (A2 b Hb)|].
    apply in_app_or in Hb as [Hb | Hb]; [exact (E2 b Hb) | exact (H2 b Hb)].
Qed.

(* ---- one source_t of the relay's table ---- *)
Lemma lt_aentry : forall ly S (W : world segs) mem md e,
  AR segs B ly S W mem md -> aentry_ok B ly S W mem e ->
  lt_fp_low (aentry_fp e) /\ (forall b, In b (aentry_blks e) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md e HAR (K1 & K2 & K3 & K4 & K5 & K6 & K7 & K8 & K9 & K10 & K11 & K12 & K13 & K14 & K15).
  assert (HK : lt_fp_low (map (fun k => gfp (key_addr k) (bzs (key_text k ++ [Z_to_bv 8 0]))) (re_keys e))
               /\ (forall b, In b (map (fun k => (key_addr k, Z.of_nat (length (key_text k)) + 1)) (re_keys e)) ->
                     In b (ablocks B ly S))).
  { rewrite Forall_forall in K15. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_map_iff in Hr as (k & <- & Hk).
      destruct (K15 k Hk) as (M1 & _).
      destruct (lt_blk ly S W mem md _ _ HAR M1) as (P1 & P2 & P3).
      cbn [gfp fst snd]. rewrite lt_bzs_len, length_app. cbn [length].
      unfold CEIL8 in *. split; [lia | lia].
    - intros b Hb. apply in_map_iff in Hb as (k & <- & Hk). exact (proj1 (K15 k Hk)). }
  destruct HK as [HK1 HK2]. unfold aentry_fp, aentry_blks. split.
  - apply lt_fp_low_app.
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & Hj & Hg)]; [lia|].
      destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
      apply lt_fp_low_cons; [cbn; lia | | apply lt_fp_low_nil].
      cbn [gfp snd]. rewrite lt_bzs_len, length_app. unfold CEIL8 in *. lia.
    + apply lt_fp_low_cons; [| |exact HK1].
      * cbn [gfp fst]. destruct K12 as [(Hz & _) | (Hz & Hin & _)]; [lia|].
        destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & _). lia.
      * cbn [gfp snd]. rewrite lt_bzs_len, lt_key_ptrs_len.
        destruct K12 as [(Hz & Hks) | (Hz & Hin & Hk1 & Hk2 & Hg)].
        { rewrite Hz, Hks. cbn [length]. unfold CEIL8. pose proof lt_ceil_lo. lia. }
        destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
        unfold re_nheld in Hk1. unfold CEIL8 in *. lia.
  - intros b Hb. apply in_app_or in Hb as [Hb | Hb].
    + destruct (Z.eqb_spec (re_cap e) 0) as [Hc|Hc]; [destruct Hb|].
      destruct K10 as [(Hc0 & _) | (Hcp & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
    + apply in_app_or in Hb as [Hb | Hb]; [|exact (HK2 b Hb)].
      destruct (Z.eqb_spec (re_hp e) 0) as [Hz|Hz]; [destruct Hb|].
      destruct K12 as [(Hz0 & _) | (_ & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.

(* ---- the relay's table, at fuzz_reply.asan-ubsan's globals ---- *)
Lemma lt_arelay : forall ly S (W : world segs) mem md G es,
  AR segs B ly S W mem md -> arelay_at B fr_globals ly S W mem G es ->
  lt_fp_low (arelay_fp fr_globals G es) /\ (forall b, In b (arelay_blks G es) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md G es HAR (R1 & R2 & R3 & R4 & R5 & R6 & R7 & R8 & R9 & R10 & R11).
  destruct (lt_blk ly S W mem md _ _ HAR R8) as (P1 & P2 & P3).
  assert (HE : lt_fp_low (concat (map aentry_fp es))
               /\ (forall b, In b (concat (map aentry_blks es)) -> In b (ablocks B ly S))).
  { rewrite Forall_forall in R10. split.
    - rewrite lt_fp_low_forall. intros r Hr. apply in_concat in Hr as (f & Hf & Hr).
      apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry ly S W mem md e HAR (R10 e He)) as [F1 _].
      rewrite lt_fp_low_forall in F1. exact (F1 r Hr).
    - intros b Hb. apply in_concat in Hb as (f & Hf & Hb). apply in_map_iff in Hf as (e & <- & He).
      destruct (lt_aentry ly S W mem md e HAR (R10 e He)) as [_ F2]. exact (F2 b Hb). }
  destruct HE as [HE1 HE2]. unfold arelay_fp, arelay_blks. split.
  - apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [lt_low | lt_low|].
    apply lt_fp_low_cons; [cbn; lia | cbn [fst snd]; unfold ATABLE, CEIL8 in *; lia | exact HE1].
  - intros b [<- | Hb]; [exact R8 | exact (HE2 b Hb)].
Qed.

(* ---- the controller's stream ---- *)
Lemma lt_aout : forall ly S (W : world segs) mem md c O mx no cap out,
  AR segs B ly S W mem md -> aout_at B fr_globals ly S W mem c O mx no cap out ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  lt_fp_low (aout_fp B fr_globals cap out) /\ (forall b, In b (aout_blks cap out) -> In b (ablocks B ly S)).
Proof.
  intros ly S W mem md c O mx no cap out HAR HO HE0 HE1.
  pose proof HO as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ &
                    _ & Hblk).
  unfold aout_fp, aout_blks. split.
  - do 9 (apply lt_fp_low_cons; [lt_low | lt_low|]).
    destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [apply lt_fp_low_nil|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & junk & Hj & Hg)]; [lia|].
    destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
    apply lt_fp_low_cons; [cbn; lia | cbn; unfold CEIL8 in *; lia | apply lt_fp_low_nil].
  - intros b Hb. destruct (Z.eqb_spec cap 0) as [Hc|Hc]; [destruct Hb|].
    destruct Hblk as [(Hc0 & _) | (Hcp & Hno & Hin & _)]; [lia|]. destruct Hb as [<- | []]. exact Hin.
Qed.


(* ---- the model, across a stretch that keeps every byte below alloc_ceiling + 8 ---- *)
Lemma lt_amodel_kept : forall ly S (W : world segs) mem md (W' : world segs) mem' m,
  AR segs B ly S W mem md -> amodel_at B ly S W mem m ->
  0 <= as_errno B -> as_errno B + 4 <= CEIL8 ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  amodel_at B ly S W' mem' m.
Proof.
  intros ly S W mem md W' mem' m HAR (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10) HE0 HE1 KEEP.
  split; [exact M1|]. split.
  { intros i Hi. specialize (M2 i Hi). unfold aslot in *.
    assert (HB0 : 0 <= rg_s fr_RG + ASRC * Z.of_nat i) by (unfold fr_RG; cbn; unfold ASRC; lia).
    assert (HB1 : rg_s fr_RG + ASRC * Z.of_nat i + ASRC <= CEIL8)
      by (unfold fr_RG, CEIL8; cbn; unfold ASRC; pose proof lt_ceil_lo; lia).
    destruct (nth i (lm_hs m) None) as [h|].
    - destruct (lt_asrc ly S W mem md _ h HAR M2 HB0 HB1) as [F1 F2].
      exact (asrc_at_kept B ly S W mem ly S W' mem' _ h M2 (lt_akept_of_low _ _ _ _ _ KEEP F1) F2).
    - destruct M2 as [G1 G2]. split.
      + apply (akept_garr8 W mem); [|exact G1]. intros x Hx. rewrite repeat_length in Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia.
      + apply (akept_awr W mem); [|exact G2]. intros x Hx.
        apply (lt_akept_of_rng W W' mem mem' (rg_s fr_RG + ASRC * Z.of_nat i)
                 (rg_s fr_RG + ASRC * Z.of_nat i + ASRC) KEEP HB0 HB1). unfold ASRC in *. lia. }
  split.
  { destruct (lt_arelay ly S W mem md (lm_G m) (lm_es m) HAR M3) as [F1 F2].
    exact (arelay_at_kept B fr_globals ly S W mem ly S W' mem' _ _ M3
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { destruct (lt_aout ly S W mem md _ _ _ _ _ _ HAR M4 HE0 HE1) as [F1 F2].
    exact (aout_at_kept B fr_globals ly S W mem ly S W' mem' _ _ _ _ _ _ M4
             (lt_akept_of_low _ _ _ _ _ KEEP F1) F2). }
  split.
  { apply (agone_at_kept fr_globals W mem W' mem' _ M5).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (alock_at_kept fr_globals W mem W' mem' _ M6).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (awake_at_kept fr_globals W mem W' mem' M7).
    apply lt_akept_rng; [exact KEEP | cbn; lia | unfold CEIL8; cbn; pose proof lt_ceil_lo; lia]. }
  split.
  { apply (akept_vm W mem); [|exact M8]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { apply (akept_awr W mem); [|exact M9]. intros x Hx. apply KEEP.
    unfold AG_NFD, CEIL8 in *. pose proof lt_ceil_lo. lia. }
  destruct M10 as (M10 & M11 & (lst & M12) & M13).
  split; [exact M10|].
  split.
  { apply (akept_vm W mem); [|exact M11]. intros x Hx. apply KEEP.
    unfold AG_THREAD_UP, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  split.
  { exists lst. apply (akept_vm W mem); [|exact M12]. intros x Hx. apply KEEP.
    unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia. }
  apply (akept_awr W mem); [|exact M13]. intros x Hx. apply KEEP.
  unfold AG_LISTEN, CEIL8 in *. pose proof lt_ceil_lo. lia.
Qed.

(* ---- the frame, the fake frame and its shadow ---- *)
Lemma lt_sv8_kept : forall (W W' : world segs) mem mem' a v,
  (forall x, a <= x < a + 8 -> abyte_kept W mem W' mem' x) -> sv8 W mem a v -> sv8 W' mem' a v.
Proof.
  intros W W' mem mem' a v HK Hv. unfold sv8 in *. apply (akept_vm W mem); [|exact Hv].
  intros x Hx. apply HK. cbn in Hx. lia.
Qed.
(* ---- the input block, the read-only image, the jump table ---- *)
Lemma lt_ainput_kept : forall cx ly S (W : world segs) mem md (W' : world segs) mem',
  AR segs B ly S W mem md -> ainput_at B cx ly S W mem ->
  Z.of_nat (length (c_pl cx)) = c_n cx ->
  (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  ainput_at B cx ly S W' mem'.
Proof.
  intros cx ly S W mem md W' mem' HAR (I1 & I2) Hlen KEEP.
  split; [exact I1|]. apply (akept_garr8 W mem); [|exact I2].
  intros x Hx. rewrite length_map in Hx. rewrite Hlen in Hx. apply KEEP.
  destruct I1 as [(Hn & Hp) | (Hn & Hin)]; [lia|].
  destruct (lt_blk ly S W mem md _ _ HAR Hin) as (P1 & P2 & P3).
  unfold CEIL8. lia.
Qed.
Lemma lt_rom_kept : forall (W W' : world segs) mem mem',
  rom_view segs W mem -> (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) ->
  rom_view segs W' mem'.
Proof.
  intros W W' mem mem' HR KEEP a Ha. rewrite <- (HR a Ha).
  assert (Hin : in_img segs a) by (destruct Ha as (sg & H1 & _ & H3); exists sg; split; assumption).
  pose proof (pa_segs_low a Hin) as Hlow. pose proof lt_ceil_lo.
  exact (proj1 (KEEP a ltac:(unfold CEIL8, kLowMemEnd in *; lia))).
Qed.
Lemma lt_jt_kept : forall (W W' : world segs) mem mem',
  jt_rom W mem -> (forall a, 0 <= a < CEIL8 -> abyte_kept W mem W' mem' a) -> jt_rom W' mem'.
Proof.
  intros W W' mem mem' HJ KEEP i Hi. apply (akept_vm W mem); [|exact (HJ i Hi)].
  intros x Hx. apply KEEP. unfold fr_jtab, CEIL8 in *. pose proof lt_ceil_lo. cbn in Hx. lia.
Qed.

(* the live blocks are pairwise distinct *)
Lemma ad_nodup : forall ly S W mem md, AR segs B ly S W mem md -> List.NoDup (ablocks B ly S).
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
(* a byte of a live block other than the relay table is outside a footprint inside that table *)
Lemma ad_fp_avoid : forall ly S W mem md p n T FP j,
  AR segs B ly S W mem md -> In (p, n) (ablocks B ly S) -> In (T, ATABLE) (ablocks B ly S) -> (p, n) <> (T, ATABLE) ->
  (forall a, inFP FP a -> T <= a < T + ATABLE) -> 0 <= j < req_size n -> ~ inFP FP (p + j).
Proof.
  intros ly S W mem md p n T FP j HAR Hp HT Hne HFP Hj Hf. apply HFP in Hf.
  pose proof (sep_blocks segs B LAWS ly S W mem md p n T ATABLE HAR Hp HT Hne) as Hd.
  unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd. unfold ATABLE in Hf. lia.
Qed.

(* what a callee taken at its own G' keeps of a frame of the caller's state: the journal's frame clause, read
   through the overlay of ajournal_gx (an off-image byte is not one of G') *)
Lemma ad_call_keep_frm : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k
    cid pos a,
  gx_ok segs B G' ->
  ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
  In (cid, pos) (frames S0) ->
  (in_zr a (frame_rng ly0 (cid, pos)) \/ in_zr a (shadow_addr (frame_addr ly0 cid pos), fs_frame_bytes cid / 8)) ->
  ~ inFP FP a -> 0 <= a < 2 ^ 64 -> ~ in_img segs a ->
  aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
  intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k cid pos a HGok HJx Hin Hr Hnf Ha Hni.
  destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F4 & _).
  rewrite (F4 cid pos a Hin Hr Hnf).
  apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
  apply inGb_false. rewrite unsigned_lit_small by lia. intros HGa. exact (Hni (proj1 (HGok a HGa))).
Qed.

End kit.


(* ------------------------------------------------------------------ the walk *)
Section pro.
Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
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
Hypothesis HG : gx_ok segs B G_fr.
Variable LS : lfcx -> Z -> lmod -> alayout -> astate -> Prop.
Variable RINV : lfcx -> Z -> lmod -> Prop.

(* ---- op_add: lib/B/W_op_add.v's published G-generic contract oa_spec_g (pb_op_add_g), at PI := PB_fr, as
   lib/B/W_LLVMFuzzerTestOneInput_add.v takes it ---- *)
Hypothesis OA : oa_spec_g (PI := PB_fr) B MT (BASE + AF_fr_op_add).

(* ------------------------------------------------------------------ the other lanes' facts *)
Hypothesis TL : PALib B.                            (* the allocator instance (lib/B/W_kit.v) *)
Hypothesis TLF : PALibF B.                          (* its fake-stack fields (lib/B/W_frame.v) *)
Hypothesis ML : model_laws (as_universe B).
Hypothesis SMP : stack_malloc_progressP B.
Hypothesis ASM1 : astack_malloc_pres segs B 1.      (* W5's form, lib/B/W_frame.v; class 1 is this entry's *)
Hypothesis FFL : frame_flag_lawP segs B.
(* _cut's two shared facts (W_LLVMFuzzerTestOneInput_cut.v glob_wr_law / errno_law), verbatim *)
Hypothesis GWL : glob_wr_law G_fr.
(* discharged by lib/B/W_LLVMFuzzerTestOneInput_G.v c_glob_wr (at G_fr := G_fr_c B) *)
Hypothesis ERRL : errno_law B.
(* discharged by the B twin of zz_ERRL (A: w8-integ 825c723c13f addI.v:242) *)
(* ---- the instance facts, in lib/A's texts at lib/B's names; lib/A's ROM_PIN and HROM_G are one fact here, the
   B sibling's HRO (lib/B/W_LLVMFuzzerTestOneInput_add.v), because rom_out's last conjunct names the sink head's
   AOFL_HEAD, which is a Context parameter of this Section: only the instance's head (YE2k.tfib_sink_head,
   ofl_head 0x5fa0e8) decides it, so it cannot be computed here as lib/A's pro_rom_out does ---- *)
Hypothesis HEV : as_errno B = TFIB_ERRNO_B.
(* discharged by lib/B/YF0m.v ts_errno (as lib/B/W_LLVMFuzzerTestOneInput_G.v's HEV premise) *)
Hypothesis HZS : azs B (rg_s fr_RG) (4 * ASRC).
(* discharged by lib/B/W_LLVMFuzzerTestOneInput_G.v c_HZS (YF0m's ts_zsh); B twin of zz_HZS *)
Hypothesis HGOBJ : forall a, inG G_fr_obj a -> inG G_fr a.
(* discharged by lib/B/W_LLVMFuzzerTestOneInput_G.v obj_c at G_fr := G_fr_c B *)
Hypothesis HRO : rom_out segs B G_fr.
(* discharged by lib/B/W_LLVMFuzzerTestOneInput_G.v c_rom_out at G_fr := G_fr_c B and SK := YE2k.tfib_sink_head
   (it is lib/A's HROM_G = c_rom_apart and ROM_PIN = c_rom_pinned, with errno and AOFL_HEAD outside rom) *)
Hypothesis GSHV : forall ly S (W : world segs) mem md a n, AR segs B ly S W mem md -> 0 < n ->
  (forall x, a <= x < a + n -> inG pro_G x) -> shadow_hull_vis (aview segs (w_H W) mem) a n.
(* discharged by lib/B/W_source_reset.v's GSHV at ARM_add's ad_G, which is pro_G (4 * ASRC = 384);
   B twin of zz_GSHV (A: w8-integ 825c723c13f addI.v:187) *)

(* ---- the entry's surviving blocks (the relay's table g_src and the controller's buffer g_out): apart from the
   input block and inside the entry's footprint fr_FP over their REQUEST size, as the cut's ablocks_sep (req_size,
   a Theorem Labs lane's ruling 12:2xZ) and op_add's journal take them; lib/A's text at 5c8023c8afd.  Conjuncts 2-3 follow
   from the instance's fr_FP (ACfn_cf.fr_FP reads g_src / g_out's ranges from entry memory).  Conjunct 1 (the entry
   split) needs the input block, g_src's table and g_out's buffer to be DISTINCT blocks, which the cut's pre does
   not state yet (a Theorem Labs lane's review 21:5xZ, reported to the cut's owner): it is not a consequence of fr_live_pre. ---- *)
Hypothesis HFP_pro : forall cx T c O mx cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ra_rel B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) T [] ->
  aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c O mx (Z.of_nat (length O)) cap out ->
  (exists rest, Permutation (ablocks B (c_ly cx) (c_S cx))
     (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest)) /\
  (T <> 0 -> forall a, T <= a < T + req_size ATABLE -> inFP (lf_FP fr_FP cx) a) /\
  (forall b, In b (aout_blks cap out) -> forall a, fst b <= a < fst b + req_size (snd b) -> inFP (lf_FP fr_FP cx) a).
(* ---- the allocator-state invariant's facts op_add takes, at the state after the fake frame (LS_pro_oa), and the
   cut's two Variables at the first cut point (LS_pro, RI_pro): the model after op_add, k = 0 ---- *)
Hypothesis LS_pro_oa : forall cx (S2 : astate) pos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  blocks_bytes S2 + APARTIAL + ATABLE <= LIVE_MAX /\ mo_ok MT S2 (oa_cost MT).
Definition pro_m (q T' : Z) (pj : list byte) (c : ctl) (O : list byte) (cap out : Z) : lmod :=
  LM 0 [Some (oa_new_src 100 q pj); None; None; None] T' [ra_new 100] c O 0 cap out 0 1.
Hypothesis RI_pro : forall cx q T' pj c O cap out,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  RINV cx 0 (pro_m q T' pj c O cap out).
(* LS_pro at the PROPOSED text (W8Add's fr_LS_pro, a working branch f57b3e2d0ca lib/A/ReplyLS.v:571; the
   lib/A form at 6018cdef2fd): the blocks after op_add with the entry's split at its table T0 and relay_add's two
   cases (T0 = 0: a new table T'; T0 <> 0: T' = T0). *)
Hypothesis LS_pro : forall cx q T' pj c O cap out (S2 : astate) pos ly S,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  (exists c0 mx0, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c0 O mx0 (Z.of_nat (length O)) cap out) ->
  ct_cl c = 3 -> ct_br c = 0 -> ct_dd c = 0 -> ct_ei c = 0 ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, pos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) -> mo_le MT S2 S (oa_cost MT) ->
  (exists T0 rest0, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest0) /\
     ((T0 = 0 /\ Permutation (ablocks B ly S) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly S) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))))) ->
  LS cx 0 (pro_m q T' pj c O cap out) ly S.

(* the coverage facts the prologue's global stores take, from HGOBJ *)
Lemma pro_cov : forall lo n, rng_inb lo n G_fr_obj = true -> forall a, lo <= a < lo + n -> inG G_fr a.
Proof. intros lo n H a Ha. exact (HGOBJ a (rng_cover lo n G_fr_obj H a Ha)). Qed.
Let HG_client := pro_cov (rg_client fr_RG) 4 ltac:(vm_compute; reflexivity).
Let HG_cbroken := pro_cov (rg_client_broken fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_nfd := pro_cov AG_NFD 4 ltac:(vm_compute; reflexivity).
Let HG_smax := pro_cov (rg_send_max fr_RG) 8 ltac:(vm_compute; reflexivity).
Let HG_gone := pro_cov (rg_gone fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_sdead := pro_cov (rg_send_dead fr_RG) 1 ltac:(vm_compute; reflexivity).
Let HG_seintr := pro_cov (rg_send_eintr fr_RG) 1 ltac:(vm_compute; reflexivity).

(* ------------------------------------------------------------------ the image's read-only bytes *)
Definition rom_inb (a : Z) : bool :=
  existsb (fun sg => negb (seg_writable sg) && (Z.of_N (seg_base sg) <=? a) &&
    (a <? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) segs.
Lemma rom_inb_ok : forall a, rom_inb a = true -> in_rom segs a.
Proof.
  intros a H. unfold rom_inb in H. apply existsb_exists in H as (sg & Hs & Hb).
  apply andb_prop in Hb as [Hb H2]. apply andb_prop in Hb as [H0 H1].
  apply negb_true_iff in H0. apply Z.leb_le in H1. apply Z.ltb_lt in H2.
  exists sg. split; [exact Hs|]. split; [exact H0|]. lia.
Qed.
(* a read-only byte reads as the image's, in a memory with the ROM view *)
Lemma pro_rom_mbyte : forall (W : world segs) mem a, rom_view segs W mem -> in_rom segs a ->
  mbyte segs (arm W mem) a = seg_rom segs (Z_to_bv 64 a).
Proof.
  intros W mem a HR Ha. pose proof (HR a Ha) as E. unfold aview in E. unfold arm.
  destruct (mbyte segs (mrestrict (w_H W) mem) a) as [b1|]; destruct (seg_rom segs (Z_to_bv 64 a)) as [b2|];
    cbn in E; try discriminate; [|reflexivity].
  injection E as E. f_equal. apply bv_eq. exact E.
Qed.
Definition rom_vmb (a : Z) (n : nat) (v : Z) : bool :=
  forallb (fun k => rom_inb (a + Z.of_nat k) &&
    match seg_rom segs (Z_to_bv 64 (a + Z.of_nat k)) with
    | Some b => Z.eqb (bv_unsigned b) (le_byte v n k) | None => false end) (seq 0 n).
Lemma rom_vmb_ok : forall (W : world segs) mem a n v, rom_view segs W mem -> rom_vmb a n v = true ->
  val_mem segs (arm W mem) a n v.
Proof.
  intros W mem a n v HR H k Hk. unfold rom_vmb in H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_seq; lia)). apply andb_prop in H as [H1 H2].
  rewrite (pro_rom_mbyte W mem _ HR (rom_inb_ok _ H1)).
  destruct (seg_rom segs (Z_to_bv 64 (a + Z.of_nat k))) as [b|]; [|discriminate H2].
  apply Z.eqb_eq in H2. f_equal. apply bv_eq. rewrite H2. symmetry. rewrite Z_to_bv_unsigned. apply bv_wrap_small.
  unfold le_byte. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.
(* the jump table's words, from the ROM view *)
Lemma pro_jt : forall (W : world segs) mem, rom_view segs W mem -> jt_rom W mem.
Proof.
  intros W mem HR i Hi.
  assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3 \/ i = 4 \/ i = 5 \/ i = 6 \/ i = 7 \/ i = 8) as Hc by lia.
  destruct Hc as [->|[->|[->|[->|[->|[->|[->|[->| ->]]]]]]]];
    apply (rom_vmb_ok W mem _ _ _ HR); vm_compute; reflexivity.
Qed.

(* ------------------------------------------------------------------ bytes a run or a call keeps *)
Lemma pro_kept_frame : forall E rs (W : world segs) m m' a,
  frame_of E rs (mrestrict (w_H W) m) (mrestrict (w_H W) m') -> 0 <= a < 2 ^ 64 -> ~ in_wrange E rs a ->
  abyte_kept W m W m' a.
Proof.
  intros E rs W m m' a HF Ha Hn. split.
  - exact (aview_kept_out E rs (w_H W) m m' HF a Ha Hn).
  - intros Hw. unfold writable_at, arm in *.
    assert (Ex : mrestrict (w_H W) m' (Z_to_bv 64 a) = mrestrict (w_H W) m (Z_to_bv 64 a))
      by (apply HF; rewrite unsigned_lit_small by lia; exact Hn).
    unfold wview in *. rewrite Ex. exact Hw.
Qed.
(* A fake frame is apart from the IMAGE OBJECT, at image B's top.  lib/B/W_frame.v frm_off_imgP proves exactly this
   but states it as the SHARED `off_img`, which cites IMG_TOP_A = 0x5fb000 (Reusable/YImgTop.v); image B's own top
   is IMG_TOP_B = 0x5fc000, and lib/B's kit bounds its objects by that (W_kit.v pa_obj_img, W_frame.v palf_uar_img).
   So the shared statement leaves a 4 KiB gap between a frame and an object, and this walk's region disjointness
   needs the B number.  Same proof as frm_off_imgP, with its own 0x5fc000 kept in the conclusion. *)
Lemma pro_frm_img_hi : forall ly S (W : world segs) mem md cid pos,
  AR segs B ly S W mem md -> In (cid, pos) (frames S) ->
  frame_addr ly cid pos + fs_frame_bytes cid <= 0x10000 \/ 0x5fc000 <= frame_addr ly cid pos.
Proof.
  intros ly S W mem md cid pos (M & LG & _) Hin. pose proof (pa_img_cover ly S md LG) as [C1 C2].
  pose proof (frame_facts B ly S _ cid pos M Hin) as (Fc & Fp & _ & _ & _ & _ & _ & _ & F64 & _).
  destruct (Z.le_gt_cases (frame_addr ly cid pos + fs_frame_bytes cid) 0x10000) as [|H1]; [left; lia|].
  destruct (Z.le_gt_cases 0x5fc000 (frame_addr ly cid pos)) as [|H2]; [right; lia|]. exfalso.
  apply (client_byte_not_img B ly S _ (Z.max (frame_addr ly cid pos) 0x10000) M).
  - right. exists (cid, pos). split; [exact Hin|]. left. unfold in_zr. cbn [fst snd]. lia.
  - unfold in_zr. lia.
Qed.
(* a byte the loaded image holds writable is writable in every memory (_G.v wr_of_seg, for any memory) *)
Lemma pro_wr_any : forall (m : word -> option byte) a,
  wview segs (fun _ => None) (Z_to_bv 64 a) <> None -> writable_at segs m a.
Proof.
  intros m a Hw. unfold writable_at, wview in *. destruct (m (Z_to_bv 64 a)); [cbv iota; discriminate | exact Hw].
Qed.
Lemma G_obj_wr : forall a, inG G_fr_obj a -> forall m, writable_at segs m a.
Proof.
  intros a Ha m. apply pro_wr_any. apply (segwb_ok segs).
  exact (rng_all_in (segwb segs) G_fr_obj a ltac:(vm_compute; reflexivity) Ha).
Qed.
Lemma G_obj_err : forall a, inG G_fr_obj a -> ~ (as_errno B <= a < as_errno B + 4).
Proof.
  intros a Ha. rewrite HEV.
  exact (pro_apart_ok TFIB_ERRNO_B 4 G_fr_obj ltac:(vm_compute; reflexivity) a Ha).
Qed.
(* a byte of a live block is none of the seven globals the prologue stores (the blocks are off the image) *)
Lemma pro_blk_gst : forall ly S (W : world segs) mem md p n a, AR segs B ly S W mem md ->
  In (p, n) (ablocks B ly S) -> p <= a < p + req_size n -> pro_gst_out a.
Proof.
  intros ly S W mem md p n a HAR Hin Ha. pose proof (blk_img segs B LAWS ly S W mem md p n a HAR Hin Ha) as Hni.
  assert (HI : forall lo w, rng_inb lo w G_fr_obj = true -> ~ (lo <= a < lo + w))
    by (intros lo w Hr Hx; apply Hni; exact (proj1 (HG a (HGOBJ a (rng_cover lo w G_fr_obj Hr a Hx))))).
  split; [intros Hx; refine (HI 0xa2560 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8d60 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8da0 4 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8dc0 8 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8de0 1 _ _); [vm_compute; reflexivity | lia]|].
  split; [intros Hx; refine (HI 0x5d8e00 1 _ _); [vm_compute; reflexivity | lia]|].
  intros Hx; refine (HI 0x5d8e20 1 _ _); [vm_compute; reflexivity | lia].
Qed.
(* rom_out at a sub-G of G_fr, from HRO (its other conjuncts do not depend on G) *)
Lemma pro_rom_out : forall G, (forall a, inG G a -> inG G_fr a) -> rom_out segs B G.
Proof.
  intros G HsG a Ha. destruct (HRO a Ha) as (H1 & H2 & H3 & H4).
  split; [intros HGa; exact (H1 (HsG a HGa))|]. exact (conj H2 (conj H3 H4)).
Qed.
Lemma pro_rom_out_fr : rom_out segs B G_fr.
Proof. exact HRO. Qed.

(* ------------------------------------------------------------------ op_add's G *)
Lemma G_oa_fr : forall a, inG pro_G a -> inG G_fr a.
Proof. intros a Ha. exact (HGOBJ a (pro_G_obj a Ha)). Qed.
Lemma G_oa_rt : gx_rt B pro_G.
Proof.
  intros a Ha. rewrite HEV.
  split; [exact (pro_apart_ok TFIB_ERRNO_B 4 pro_G ltac:(vm_compute; reflexivity) a Ha)|].
  split; [exact (pro_apart_ok (VAL (A_OBJ 0)) 8 pro_G ltac:(vm_compute; reflexivity) a Ha)|].
  exact (pro_apart_ok (VAL (A_OBJ 30)) 8 pro_G ltac:(vm_compute; reflexivity) a Ha).
Qed.
Lemma G_oa_prog : gx_prog (PI := PB_fr) B pro_G.
Proof.
  split; [exact (gx_ok_sub segs B pro_G G_fr G_oa_fr HG)|].
  split; [exact G_oa_rt|].
  split; [exact (pro_rom_out pro_G G_oa_fr)|].
  split.
  { intros a Ha.
    pose proof (rng_all_in (fun x => match seg_rom segs (Z_to_bv 64 x) with Some _ => true | None => false end)
      pro_G a ltac:(vm_compute; reflexivity) Ha) as H.
    cbv beta in H. destruct (seg_rom segs (Z_to_bv 64 a)); [discriminate | discriminate H]. }
  split; [intros a Ha m; apply pro_wr_any; apply (segwb_ok segs);
          exact (rng_all_in (segwb segs) pro_G a ltac:(vm_compute; reflexivity) Ha)|].
  exact GSHV.
Qed.
Let HBgot := pal_got_shadow B TL. Let HBcell := pal_cell B TL.
Let RUN := paj_run (PL := PL_fr) (PI := PB_fr) B LAWS.
Let RUNP := SRr_run_pi_AJ (PL := PL_fr) (PI := PB_fr) B LAWS.
Let RUNX := paj_run_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let RUNTOX := paj_run_to_x (PL := PL_fr) (PI := PB_fr) B LAWS G_fr HG 0 [].
Let BR := paj_branch (PI := PB_fr).

(* ------------------------------------------------------------------ the entry state *)
Definition Bx : sv := SOff 33 0.
Definition Bspan : Z * Z := (SB, SB + 2 ^ 44 - 1).
(* the frame's bytes the prologue writes: the slot sp0 - 320 (`sd zero,0(sp)`) and the saved registers
   [sp0 - 104, sp0), both through sp0 (atom 2); the slots [F + 32, F + 192), through F (atom 34) *)
Definition pr_zero : YP09.region := YP09.mkRegion (Some 2%nat) (-320) (-312) (-320) (-312) [].
Definition pr_save : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0 [].
Definition pr_F : YP09.region := YP09.mkRegion (Some 34%nat) 32 192 32 192 [].
Definition pro_regions0 : smem :=
  [ pr_zero; pr_save; pr_F; got_regionP; bcell_regionP 33; uar_got_regionP 32; uar_cell_regionP 32 ].
(* `andi sp, sp, -32` lands on F (atom 34), by the alias *)
Definition pro_alias : sv * sv := (SAlu ALU_AND (SOff 2 (-320)) (SLit (-32)), SOff 34 0).
Definition pro_facts0 : facts :=
  mkFacts [ (2%nat, mkAF (2^46) (2^47) 4); (11%nat, mkAF 0 (2 ^ 26 - 1) 0); (32%nat, mkAF 0x10000 0x5fc000 2);
            (33%nat, mkAF SB SB 0); (34%nat, mkAF (2^46) (2^47) 5) ] [] [pro_alias].
Definition ss_pro0 : sstate := mkSS A_pro sr_atoms pro_regions0 None pro_facts0.
Definition pro_extra (regs : bvmap 5 word) : list word := map (Z_to_bv 64) [as_uar_cell B; SB; pro_F regs].
(* the globals the prologue resets, each stored through the auipc register of its hi slot j (0x84554-0x8458c) *)
Definition pr_g (j : nat) (off w : Z) : YP09.region := YP09.mkRegion (Some (A_HI j)) off (off + w) off (off + w) [].
(* the image values the prologue names, at the pinned placement (B's listing; vm_compute at PB_fr) *)
Lemma pro_vals :
  VAL (A_HI 60) = 0xa2540 /\ VAL (A_HI 61) = 0x5d9548 /\ VAL (A_HI 62) = 0x5d954c /\ VAL (A_HI 63) = 0x5d9550 /\
  VAL (A_HI 64) = 0x5d955c /\ VAL (A_HI 65) = 0x5d9564 /\ VAL (A_HI 66) = 0x5d956c /\
  VAL (A_HI 69) = HI_G_NOUT /\ VAL (A_HI 70) = HI_G_SRC /\
  VAL (A_OBJ 19) = rg_s fr_RG /\ VAL (A_OBJ 22) = 0x1239d /\ VAL (A_OBJ 23) = 0x10320 /\
  VAL (A_OBJ 0) = 0x9df50 /\ VAL (A_OBJ 6) = 0x9dfa8 /\ VAL (A_OBJ 30) = 0xa6638 /\
  BASE + AF_fr_LLVMFuzzerTestOneInput = YCfn.A_LLVMF.
Proof. vm_compute. repeat split; reflexivity. Qed.
(* a sign-extended byte store leaves its low byte (the fake frame's shadow poison) *)
Lemma pro_chunk1 : forall E m n b cs lo hi wlo whi od z,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  In (YP09.mkChunk od (CVal 1 (SLit z))) cs ->
  mbyte segs m (b + od) = Some (byte_of_word (Z_to_bv 64 z) 0).
Proof.
  intros E m n b cs lo hi wlo whi od z (_ & _ & _ & Hcs) Hn Hin.
  pose proof (proj1 (Forall_forall _ _) Hcs _ Hin) as Hck. specialize (Hck 0 ltac:(cbn; lia)).
  destruct Hck as (bb & Hc & Hm). cbn [YP09.r_base base_val YP09.c_off YP09.c_val cbyte sv_denot] in Hc, Hm.
  rewrite Hn, Z.add_0_r in Hm. injection Hc as <-. exact Hm.
Qed.
(* the fake frame's shadow poison, read off its region (16 sign-extended byte stores: 0xf1 x4, 0xf8 x6, 0xf3 x6) *)
Definition fs_z (j : nat) : Z :=
  if (j <? 4)%nat then 18446744073709551601 else if (j <? 10)%nat then 18446744073709551608
  else 18446744073709551603.
Lemma pro_shadow_garr8 : forall E m n b cs lo hi wlo whi,
  region_ok segs E m (YP09.mkRegion (Some n) lo hi wlo whi cs) -> bv_unsigned (ew E n) = b ->
  (forall j, (j < 16)%nat -> In (YP09.mkChunk (Z.of_nat j) (CVal 1 (SLit (fs_z j)))) cs) ->
  garr8 segs m b fake_shadow.
Proof.
  intros E m n b cs lo hi wlo whi HR Hb HF j Hj. cbn [length fake_shadow] in Hj.
  assert (Hz : forall j, (j < 16)%nat ->
    byte_of_word (Z_to_bv 64 (fs_z j)) 0 = Z_to_bv 8 (le_byte (nth j fake_shadow 0) 1 0) /\
    0 <= nth j fake_shadow 0 < 256).
  { clear. intros j Hj. do 16 (destruct j as [|j]; [split; [apply bv_eq; vm_compute; reflexivity | cbn; lia]|]). lia. }
  destruct (Hz j Hj) as [Hz1 Hz2]. split; [|exact Hz2].
  intros k Hk. assert (k = 0)%nat as -> by lia. rewrite Z.add_0_r.
  rewrite (pro_chunk1 E m n b cs lo hi wlo whi (Z.of_nat j) (fs_z j) HR Hb (HF j Hj)). rewrite Hz1. reflexivity.
Qed.
(* the saved registers, read off the stack region through sp0 (W_op_add.v oa_saved_of_region) *)
Lemma pro_saved_of_region : forall E m spv cs lo hi wlo whi (regs : bvmap 5 word),
  region_ok segs E m (YP09.mkRegion (Some 2%nat) lo hi wlo whi cs) -> bv_unsigned (ew E 2) = spv ->
  (forall r, (r < 32)%nat -> ew E r = getr regs (Z_to_bv 5 (Z.of_nat r))) ->
  Forall (fun p => In (YP09.mkChunk (- fst p) (CVal 8 (SOff (Z.to_nat (snd p)) 0))) cs) saved_regs ->
  forall o r, In (o, r) saved_regs -> val_mem segs m (spv - o) 8 (bv_unsigned (getr regs (Z_to_bv 5 r))).
Proof.
  intros E m spv cs lo hi wlo whi regs HR Hsp EA HIn o r Hp.
  rewrite Forall_forall in HIn. pose proof (HIn _ Hp) as Hin. cbn [fst snd] in Hin.
  assert (Hr : 0 <= r < 32)
    by (unfold saved_regs in Hp; cbn [In] in Hp;
        repeat (destruct Hp as [Hp | Hp]; [injection Hp as <- <-; lia|]); destruct Hp).
  replace (spv - o) with (spv + (- o)) by lia. change 8%nat with (N.to_nat 8).
  apply (field_of_region E m 2 spv cs lo hi wlo whi (- o) 8 (SOff (Z.to_nat r) 0) _ HR Hsp Hin).
  - cbn [sv_denot]. rewrite EA by lia. rewrite Z2Nat.id by lia. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. reflexivity.
  - pose proof (bv_unsigned_in_range 64 (getr regs (Z_to_bv 5 r))) as HB. change (bv_modulus 64) with (2 ^ 64) in HB.
    change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64). lia.
  - lia.
Qed.

Lemma pro_F_facts : forall sp0, sp0 mod 16 = 0 ->
  (sp0 - 320) - (sp0 - 320) mod 32 = sp0 - 320 \/ (sp0 - 320) - (sp0 - 320) mod 32 = sp0 - 336.
Proof.
  intros sp0 H. pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hb.
  pose proof (Z.div_mod (sp0 - 320) 32 ltac:(lia)) as D1. pose proof (Z.div_mod sp0 16 ltac:(lia)) as D2.
  rewrite H in D2. lia.
Qed.
Lemma pro_F_al : forall x, (x - x mod 32) mod 32 = 0.
Proof. intros x. rewrite Zminus_mod, Z.mod_mod, Z.sub_diag by lia. reflexivity. Qed.

Lemma pro_entry : forall W ly S regs mem md ch n,
  afn_pre segs B LLVMF_STK ly S W regs mem md ch -> getr regs 11 = w64 n -> 0 <= n < 2 ^ 26 ->
  st_ok_pi segs VAL (Eimg (Ereg regs (pro_extra regs))) ss_pro0
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro)) mem (seg_rom segs)))
  /\ sh_ok segs Bx [] (Eimg (Ereg regs (pro_extra regs))) (mrestrict (w_H W) mem).
Proof.
  intros W ly S regs mem md ch n HPRE H11 Rn.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity.
  destruct (al_const _ _ LAWS ly S W mem md HAR) as (Kcell & Kuar & Kgot & Kguar).
  rewrite HBgot, HBcell in Kgot. rewrite HBcell in Kcell. rewrite (palf_got_uar B TLF) in Kguar.
  pose proof (palf_uar_img B TLF) as HuR. pose proof (palf_uar_al B TLF) as HuA. pose proof (palf_sep B TLF) as HSEP.
  cbn [zseps zseps_from fst snd] in HSEP.
  set (F := pro_F regs).
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  rewrite restrict_mkst_fx.
  set (E := Eimg (Ereg regs (pro_extra regs))). pose proof pa_B_ok as HBASE.
  assert (E2 : ew E 2 = getr regs 2) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 2 2%bv eq_refl)).
  assert (E11 : ew E 11 = getr regs 11) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_nat regs _ 11 11%bv eq_refl)).
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (E241 : ew E (A_OBJ 0) = Z_to_bv 64 (VAL (A_OBJ 0))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E247 : ew E (A_OBJ 6) = Z_to_bv 64 (VAL (A_OBJ 6))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  assert (E271 : ew E (A_OBJ 30) = Z_to_bv 64 (VAL (A_OBJ 30))) by (subst E; apply Eimg_img; unfold A_OBJ, A_TEXT, A_LIM; lia).
  pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite E2; reflexivity).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  assert (VB : forall m w, ew E m = Z_to_bv 64 w -> 0 <= w < 2 ^ 64 -> base_val E (Some m) = w).
  { intros m w Hm Hw. cbn [base_val]. rewrite Hm. apply unsigned_lit_small. exact Hw. }
  split.
  - unfold ss_pro0, A_pro. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite Usp. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * cbn [base_val]. rewrite UF. split; [lia|]. split; [lia|]. split; [|constructor].
        intros o Ho. apply (apresent_writable segs). apply Hpres. lia.
      * rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 0)) 0 8 (SOff (A_OBJ 30) 0) (VAL (A_OBJ 30)));
          [cbn [sv_denot]; rewrite E271, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | pose proof (pa_val_range (A_OBJ 30)); zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kgot).
      * rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 30)) 0 8 (SOff 33 0) SB);
          [cbn [sv_denot]; rewrite E33, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | unfold SB; zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kcell).
      * rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
        split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (VAL (A_OBJ 6)) 0 8 (SOff 32 0) (as_uar_cell B));
          [cbn [sv_denot]; rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rdword segs (w_H W) mem _ _ Kguar).
      * rewrite (VB 32%nat (as_uar_cell B) E32) by lia. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ (as_uar_cell B) 0 4 (SLit 1) 1); [reflexivity | zside | zside |].
        rewrite Z.add_0_r. exact (val_mem_of_rd32 segs (w_H W) mem _ _ Kuar).
    + apply pairwise_disjoint_of_extents.
      unfold pro_regions0, pr_zero, pr_save, pr_F, got_regionP, bcell_regionP, uar_got_regionP, uar_cell_regionP, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi].
      rewrite (VB (A_OBJ 0) (VAL (A_OBJ 0)) E241) by (pose proof (pa_val_range (A_OBJ 0)); lia).
      rewrite (VB (A_OBJ 6) (VAL (A_OBJ 6)) E247) by (pose proof (pa_val_range (A_OBJ 6)); lia).
      rewrite (VB (A_OBJ 30) (VAL (A_OBJ 30)) E271) by (pose proof (pa_val_range (A_OBJ 30)); lia).
      rewrite (VB 32%nat (as_uar_cell B) E32) by lia. cbn [base_val]. rewrite Usp, UF.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
      revert HFv HspR Hslo Hshi H47 Hceil C1 C3 WS Hstk0 HcellR HgotR HguR HuR HSEP. clear.
      unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. repeat split; lia.
    + split; [|split; [exact I|]].
      * cbn [pro_facts0 f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
        rewrite Usp, UF, E11, H11, E32, E33, !unsigned_lit_small by (unfold SB; lia).
        change (2 ^ 5) with 32. change (2 ^ 4) with 16. change (2 ^ 2) with 4. rewrite !Z.pow_0_r, !Z.mod_1_r.
        revert HFv HFal HspR Hal16 Rn HuR HuA. clear. unfold SB. intros.
        repeat match goal with |- _ /\ _ => split end; lia.
      * cbn [pro_facts0 f_alias alias_ok pro_alias]. split; [|exact I].
        assert (E2' : ew E 2 = Z_to_bv 64 (spZ regs)) by (rewrite E2; unfold spZ; symmetry; apply Z_to_bv_bv_unsigned).
        apply U_inj. rewrite U_SAlu, (U_atom_off E 2 (spZ regs) (-320) E2'), (U_atom E 34 F E34) by lia.
        rewrite U_SLit. cbn [zalu_raw].
        assert (Hlo : 0 <= spZ regs + -320 < 2 ^ 64) by (destruct HspR as [HspR1 HspR2]; destruct HFv as [HFv | HFv]; rewrite HFv in HspR1; lia).
        change (zcanon (-32)) with (2 ^ 64 - 2 ^ 5). rewrite (land_neg_pow2_u64 (spZ regs + -320) 5 Hlo ltac:(lia)).
        assert (EF : spZ regs + -320 - (spZ regs + -320) mod 2 ^ 5 = F) by reflexivity.
        rewrite EF. apply zcanon_id. unfold M64. destruct HspR as [HspR1 HspR2]. destruct HFv as [HFv | HFv]; lia.
  - unfold sh_ok. constructor.
Qed.


(* ------------------------------------------------------------------ state tactics (lib/A's pro file's) *)
(* keep the regions idxs of HS's state *)
Ltac pro_keep HS idxs :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let rs := eval vm_compute in (YP03.pick (ss_mem ssx) idxs) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_submem (PI := PB_fr) Ex ssx msx rs HS ltac:(submem_tac) ltac:(vm_compute; reflexivity)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* make region i read-only *)
Ltac pro_ro HS i :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
  let HSk := fresh "HSk" in
  pose proof (ast_ok_pi_set_region (PI := PB_fr) Ex ssx msx i r (set_window r 0 0) HS eq_refl eq_refl
    ltac:(vm_compute; reflexivity)
    (region_ok_rewindow sg Ex _ r 0 0 (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) ltac:(intros o Ho; lia)))
    as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* rewrite every image atom's value in the goal, then compute each named image value *)
Ltac pro_val :=
  repeat match goal with |- context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv; clear Hv end.
Ltac pro_img HEI :=
  repeat match goal with |- context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia))
    end end;
  pro_val.
Ltac pro_imgh HEI H :=
  repeat match type of H with context [bv_unsigned (ew ?E ?a)] =>
    let a' := eval vm_compute in a in
    lazymatch eval vm_compute in ((A_TEXT <=? a') && (a' <? A_LIM))%nat with
    | true => rewrite (HEI a ltac:(unfold A_HI, A_OBJ, A_TEXT, A_LIM; lia)) in H
    end end;
  repeat match type of H with context [VAL ?a] =>
    let a' := eval vm_compute in a in
    let v := eval vm_compute in (VAL a') in
    let Hv := fresh "Hval" in
    assert (Hv : VAL a = v) by (vm_compute; reflexivity); rewrite Hv in H; clear Hv end.
(* add the store region of global hi slot j, offset off, width w, whose bytes HGx puts in G_fr *)
Ltac pro_addg HS HEI j off w HGx :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_region Ex ssx msx (pr_g j off w) HS eq_refl
    ltac:(unfold region_ok, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val];
          pro_img HEI; split; [lia|]; split; [lia|]; split; [|constructor];
          intros o Ho; cbn [ms_mem restrict mkst]; apply GWL; apply HGx; lia)
    ltac:(lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end;
          cbn [all_disjoint]; unfold extent_disjoint, pr_g; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
          repeat match goal with H : bv_unsigned (ew ?E ?a) = _ |- context [bv_unsigned (ew ?E ?a)] => rewrite H end;
          pro_img HEI;
          unfold SB, off_img in *; repeat split; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* pin image atom n to its value in HS's facts (the token run's static check reads a store region's base off them) *)
Ltac pro_addf HS HEI n :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
  let v := eval vm_compute in (VAL n) in
  let HSk := fresh "HSk" in
  pose proof (st_ok_pi_add_fact Ex ssx msx n (mkAF v v 0) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2];
          rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia)); pro_val;
          rewrite Z.pow_0_r, Z.mod_1_r; lia)) as HSk;
  clear HS; rename HSk into HS; norm_ss HS end.
(* region i of HS's state, as region_ok *)
Ltac pro_rgn HS i HR :=
  lazymatch type of HS with st_ok_pi ?sg ?vl ?Ex ?ssx ?msx =>
    let r := eval vm_compute in (nth i (ss_mem ssx) (YP09.mkRegion None 0 0 0 0 [])) in
    pose proof (st_ok_pi_region_nth (PI := PB_fr) Ex ssx msx i r HS eq_refl) as HR end.
(* a register op_add's post keeps *)
Ltac pro_cs := unfold acallee_saved;
  match goal with |- context [bv_unsigned ?r] => let v := eval vm_compute in (bv_unsigned r) in
    change (bv_unsigned r) with v end; lia.

(* ------------------------------------------------------------------ the frame's numbers *)
Lemma pro_Fb : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  CEIL8 + 32000 <= lf_F cx /\ lf_F cx + 320 <= spZ (c_regs cx) /\ spZ (c_regs cx) - 352 <= lf_F cx /\
  spZ (c_regs cx) <= 2 ^ 47 /\ lf_F cx mod 32 = 0 /\ spZ (c_regs cx) mod 16 = 0.
Proof.
  intros cx (_ & HPRE0).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE0; tauto).
  pose proof HPREE as (_ & _ & _ & _ & _ & Hstk0 & _ & _ & _).
  pose proof Hstk0 as (Hal16 & _ & Hceil0 & Hslo & Hshi & H47 & _ & _ & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (HF32 : lf_F cx = spZ (c_regs cx) - 320 - (spZ (c_regs cx) - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (spZ (c_regs cx) - 320) 32 ltac:(lia)) as Hmb.
  pose proof (pro_F_al (spZ (c_regs cx) - 320)) as Hal32. rewrite <- HF32 in Hal32.
  assert (HFlo : CEIL8 + 32000 <= lf_F cx) by (unfold CEIL8, YCfn.LLVMF_STK in *; lia).
  split; [exact HFlo|]. split; [lia|]. split; [lia|]. split; [unfold YCfn.LLVMF_STK in *; lia|].
  split; [exact Hal32 | exact Hal16].
Qed.
Lemma abyte_kept_trans : forall (W1 W2 W3 : world segs) m1 m2 m3 a,
  abyte_kept W1 m1 W2 m2 a -> abyte_kept W2 m2 W3 m3 a -> abyte_kept W1 m1 W3 m3 a.
Proof. intros W1 W2 W3 m1 m2 m3 a [H1 H2] [H3 H4]. split; [rewrite H3; exact H1 | intros Hw; exact (H4 (H2 Hw))]. Qed.
(* the frame's bytes are present wherever the journal from the entry holds *)
Lemma pro_frame_wr : forall cx own ly3 S3 k (W : world segs) mem md,
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) own ly3 S3 W mem md k ->
  forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a.
Proof.
  intros cx own ly3 S3 k W mem md (_ & _ & (memS & HJi & _) & _) a Ha. rewrite !Z.add_0_r in HJi.
  pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hpres & _).
  apply (apresent_writable segs). apply Hpres. lia.
Qed.
(* The frame and the fake frame before the loop's set-up: aframe_at but for the six slots 0x845b0-0x845d8 store
   (F+48, F+96, F+120, F+128, F+136, F+152).  FL is the fake frame's flag word, which __asan_stack_malloc_1 left
   at FF + 120 and which the cut carries beside aframe_at. *)
Definition pro_fr (cx : lfcx) (FF FL : Z) (W : world segs) (mem : word -> option byte) : Prop :=
  let sp0 := spZ (c_regs cx) in let F := lf_F cx in
  (forall o r, In (o, r) saved_regs -> sv8 W mem (sp0 - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) /\
  sv8 W mem (F + 32) HI_G_CLIENT /\ sv8 W mem (F + 40) HI_G_SDEAD /\ sv8 W mem (F + 56) HI_G_SEINTR /\
  sv8 W mem (F + 64) HI_G_GONE /\ sv8 W mem (F + 72) HI_G_SMAX /\ sv8 W mem (F + 80) FF /\
  sv8 W mem (F + 104) FF /\ sv8 W mem (F + 184) FF /\
  sv8 W mem FF 0x41b58ab3 /\ sv8 W mem (FF + 8) 0x1239d /\ sv8 W mem (FF + 16) YCfn.A_LLVMF /\
  sv8 W mem (FF + 120) FL /\ awr W mem FF 128 /\
  garr8 segs (arm W mem) (SB + FF / 8) fake_shadow /\ awr W mem (SB + FF / 8) 16.
(* the registers op_add returns with (callee-saved, as the prologue left them) *)
Definition pro_regs (cx : lfcx) (FF : Z) (regs : bvmap 5 word) : Prop :=
  getr regs 2 = w64 (lf_F cx) /\ getr regs 8 = getr (c_regs cx) 2 /\ getr regs 9 = w64 (lf_F cx) /\
  getr regs 19 = w64 (FF + 32) /\ getr regs 21 = w64 (c_n cx) /\ getr regs 22 = w64 (c_p cx) /\
  getr regs 24 = w64 (SB + FF / 8) /\ getr regs 27 = w64 SB /\
  getr regs 3 = w64 (as_gp B) /\ getr regs 4 = w64 (as_tp B).

(* ------------------------------------------------------------------ 0x84594, back from op_add *)
(* the loop's set-up writes F+48 (g_s), F+96 (the fake frame's shadow), F+120, F+128, F+136, F+152 through s1
   (atom 9) and reads the /10 multiplier at 0x10320 (.rodata, the listing's object 23).  Three narrow windows, so
   that the slots the prologue already stored (F+56 .. F+104, F+184) keep their bytes across the run. *)
Definition pr2_48 : YP09.region := YP09.mkRegion (Some 9%nat) 48 56 48 56 [].
Definition pr2_96 : YP09.region := YP09.mkRegion (Some 9%nat) 96 104 96 104 [].
Definition pr2_120 : YP09.region := YP09.mkRegion (Some 9%nat) 120 160 120 160 [].
Definition pr2_div : YP09.region :=
  YP09.mkRegion (Some (A_OBJ 23)) 0 8 0 0 [YP09.mkChunk 0 (CVal 8 (SLit DIV10))].
Definition pro2_regions : smem := [pr2_48; pr2_96; pr2_120; pr2_div].
Definition pro2_facts : facts :=
  mkFacts [ (9%nat, mkAF (2 ^ 46) (2 ^ 47) 5); (27%nat, mkAF SB SB 0); (32%nat, mkAF SB SB 0) ] [] [].
Definition ss_pro2 : sstate := mkSS A_pro_ret sr_atoms pro2_regions None pro2_facts.
Definition Bx2 : sv := SOff 32 0.
Definition pro2_extra : list word := map (Z_to_bv 64) [SB].
Lemma pro_entry2 : forall (W : world segs) regs mem F,
  getr regs 9 = w64 F -> getr regs 27 = w64 SB -> 2 ^ 46 <= F -> F + 192 <= 2 ^ 47 -> F mod 32 = 0 ->
  val_mem segs (arm W mem) 0x10320 8 DIV10 ->
  (forall a, F + 48 <= a < F + 160 -> writable_at segs (arm W mem) a) ->
  st_ok_pi segs VAL (Eimg (Ereg regs pro2_extra)) ss_pro2
    (restrict (w_H W) (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)))
  /\ sh_ok segs Bx2 [] (Eimg (Ereg regs pro2_extra)) (mrestrict (w_H W) mem).
Proof.
  intros W regs mem F H9 H27 HF0 HF1 HFal HVD HWR. rewrite restrict_mkst_fx.
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  set (E := Eimg (Ereg regs pro2_extra)).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact H9).
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact H27).
  assert (E32 : ew E 32 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E23 : ew E (A_OBJ 23) = Z_to_bv 64 0x10320).
  { subst E. rewrite Eimg_img by (unfold A_OBJ, A_TEXT, A_LIM; lia).
    pose proof pro_vals as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & PV23 & _). rewrite PV23. reflexivity. }
  assert (VB9 : base_val E (Some 9%nat) = F) by (cbn [base_val]; rewrite E9; apply unsigned_lit_small; lia).
  assert (VB23 : base_val E (Some (A_OBJ 23)) = 0x10320)
    by (cbn [base_val]; rewrite E23; apply unsigned_lit_small; lia).
  split.
  - unfold ss_pro2. apply pa_entry_st_ok_full.
    + apply regs_ok_Eimg_Ereg.
    + vm_compute. reflexivity.
    + unfold pro2_regions, pr2_48, pr2_96, pr2_120, pr2_div.
      repeat apply Forall_cons; try apply Forall_nil; unfold region_ok;
      cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks].
      * rewrite VB9. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply HWR. lia.
      * rewrite VB9. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply HWR. lia.
      * rewrite VB9. split; [lia|]. split; [lia|]. split; [|constructor]. intros o Ho. apply HWR. lia.
      * rewrite VB23. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
        constructor; [|constructor].
        apply (chunk_ok_val segs E _ 0x10320 0 8 (SLit DIV10) DIV10); [reflexivity | unfold DIV10; zside | zside |].
        rewrite Z.add_0_r. exact HVD.
    + apply pairwise_disjoint_of_extents.
      unfold pro2_regions, pr2_48, pr2_96, pr2_120, pr2_div, extent_of_region.
      cbn [map YP09.r_base YP09.r_lo YP09.r_hi]. rewrite VB9, VB23.
      cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd]. repeat split; lia.
    + split; [|split; [exact I | exact I]].
      cbn [pro2_facts f_atoms atoms_ok]. unfold afact_ok. cbn [af_lo af_hi af_al2].
      rewrite E9, E27, E32, !unsigned_lit_small by (unfold SB; lia).
      change (2 ^ 5) with 32. rewrite !Z.pow_0_r, !Z.mod_1_r. unfold SB.
      repeat match goal with |- _ /\ _ => split end; lia.
  - unfold sh_ok. constructor.
Qed.
(* aframe_at, from the facts before the set-up and the six slots it stores *)
Lemma pro_aframe : forall cx FF FL (W : world segs) mem,
  pro_fr cx FF FL W mem ->
  sv8 W mem (lf_F cx + 48) (rg_s fr_RG) -> sv8 W mem (lf_F cx + 96) (SB + FF / 8) ->
  sv8 W mem (lf_F cx + 120) (SB + rg_s fr_RG / 8) -> sv8 W mem (lf_F cx + 128) (rg_s fr_RG + 4) ->
  sv8 W mem (lf_F cx + 136) DIV10 -> sv8 W mem (lf_F cx + 152) (SB + (rg_s fr_RG + 4) / 8) ->
  (forall a, spZ (c_regs cx) - LLVMF_STK <= a < spZ (c_regs cx) -> writable_at segs (arm W mem) a) ->
  lf_F cx + 320 <= spZ (c_regs cx) -> spZ (c_regs cx) - 352 <= lf_F cx ->
  aframe_at cx FF W mem.
Proof.
  intros cx FF FL W mem (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFL & HFW & HSH & HSW)
    H48 H96 H120 H128 H136 H152 HWR HF1 HF2.
  unfold aframe_at. cbv zeta.
  split; [exact HSV|]. split; [intros i Hi; apply HWR; unfold YCfn.LLVMF_STK; lia|].
  split; [exact H32|]. split; [exact H40|]. split; [exact H48|]. split; [exact H56|]. split; [exact H64|].
  split; [exact H72|]. split; [exact H80|]. split; [exact H96|]. split; [exact H104|]. split; [exact H120|].
  split; [exact H128|]. split; [exact H136|]. split; [exact H152|]. split; [exact H184|].
  split; [exact HH0|]. split; [exact HH8|]. split; [exact HH16|]. split; [exact HFW|].
  split; [exact HSH | exact HSW].
Qed.
(* a symbolic value read as a number, and the shadow address of a + c in the shadow matcher's form (W2's oa_sv_lit /
   oa_sh_den, lib/A/W_op_add.v:532-546, which this file does not Require) *)
Lemma pro_sv_lit : forall E e v, U E e = zcanon v -> sv_denot E e = Z_to_bv 64 v.
Proof. intros E e v H. apply bv_eq. unfold U in H. rewrite H, Z_to_bv_unsigned. apply zcanon_wrap. Qed.
Lemma pro_sh_den : forall E (bx g : nat) sb a c,
  ew E bx = Z_to_bv 64 sb -> ew E g = Z_to_bv 64 a -> 0 <= sb < 2 ^ 62 -> 0 <= a < 2 ^ 62 -> 0 <= a + c < 2 ^ 62 ->
  sv_denot E (SAlu ALU_ADD (SOff bx 0) (SAlu ALU_SRL (SOff g c) (SLit 3))) = Z_to_bv 64 (sb + (a + c) / 8).
Proof.
  intros E bx g sb a c Hb Hg Hsb Ha Hac. apply pro_sv_lit. rewrite !U_SAlu. cbn [zalu_raw].
  rewrite (U_atom E bx sb Hb) by lia. rewrite (U_atom_off E g a c Hg) by lia. rewrite U_SLit.
  change (Z.land (zcanon 3) 63) with 3. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
  assert (Hd : 0 <= (a + c) / 8 <= a + c) by (split; [apply Z.div_pos | apply Z.div_le_upper_bound]; lia).
  rewrite (zcanon_id ((a + c) / 8)) by (unfold M64; lia). reflexivity.
Qed.
(* the registers the loop's set-up keeps *)
Definition pro_kept : list (bv 5) := [2; 3; 4; 8; 9; 19; 21; 22; 24; 27]%bv.

(* ------------------------------------------------------------------ 0x84594-0x845dc: the loop's set-up *)
(* B has NO empty-input branch here: the `in.n != 0` test IS the head (0x845e0), so this run lands on INV_H alone
   (the cut's difference (2)); A's pro_fin had to split and could land on INV_X. *)
Lemma pro_fin : forall cx (W : world segs) regs mem md ly3 S3 k m fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  pro_fr cx (frame_addr ly3 1 fpos) (flag_addr ly3 1 fpos) W mem ->
  pro_regs cx (frame_addr ly3 1 fpos) regs ->
  amodel_at B ly3 S3 W mem m -> lm_k m = 0 -> ainput_at B cx ly3 S3 W mem -> rom_view segs W mem ->
  ablocks_sep B fr_FP cx m ly3 S3 -> LS cx 0 m ly3 S3 -> RINV cx 0 m ->
  SRr segs W (mkCfg (mkst regs (Z_to_bv 64 (BASE + A_pro_ret)) mem (seg_rom segs)) md)
    (INV_H B G_fr fr_FP LS RINV cx 0).
Proof.
  intros cx W regs mem md ly3 S3 k m fpos HB HJ HFR HRG HMOD Hk0 HIN HRV HSEP HLS HRI.
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (WS : YCfn.LLVMF_STK = 32768) by reflexivity.
  pose proof HB as (HAI0 & HPRE0).
  assert (HlenP : c_n cx = Z.of_nat (length (c_pl cx))) by (unfold fr_lib_pre_cf in HPRE0; tauto).
  assert (Hn26 : 0 <= c_n cx < 2 ^ 26)
    by (unfold fr_lib_pre_cf in HPRE0; destruct HPRE0 as (_ & _ & _ & _ & [(H0 & _) | (H0 & _)] & _); lia).
  set (FF := frame_addr ly3 1 fpos) in *. set (F := lf_F cx) in *. set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S3)).
  { pose proof HJ as (_ & _ & (memS & HJi & _) & _). pose proof HJi as (_ & _ & _ & _ & _ & Hfrs & _).
    rewrite Hfrs. left. reflexivity. }
  destruct (frames_bounds segs B LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  destruct (al_frames _ _ LAWS ly3 S3 W mem md 1 fpos HAR Hin1) as (HFFal & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1, HFFal.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFL & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (HDIV : val_mem segs (arm W mem) 0x10320 8 DIV10)
    by (apply (rom_vmb_ok W mem _ _ _ HRV); vm_compute; reflexivity).
  assert (HWRF : forall a, sp0 - YCfn.LLVMF_STK <= a < sp0 -> writable_at segs (arm W mem) a)
    by (exact (pro_frame_wr cx _ _ _ _ W mem md HJ)).
  assert (HWR : forall a, F + 48 <= a < F + 160 -> writable_at segs (arm W mem) a)
    by (intros a Ha; apply HWRF; unfold sp0 in *; lia).
  destruct (pro_entry2 W regs mem F R9 R27 ltac:(unfold CEIL8 in *; lia) ltac:(unfold sp0 in *; lia) HFal HDIV HWR)
    as [HS SHOK].
  remember (Eimg (Ereg regs pro2_extra)) as E eqn:HE.
  assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (HAE : env_agree 32 (Ereg regs pro2_extra) E)
    by (rewrite HE; split; [intros q Hq; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  assert (E9 : ew E 9 = Z_to_bv 64 F)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 9 9%bv eq_refl); exact R9).
  assert (U9 : bv_unsigned (ew E 9) = F) by (rewrite E9; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  assert (E24 : ew E 24 = Z_to_bv 64 (SB + FF / 8))
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 24 24%bv eq_refl); exact R24).
  assert (E27 : ew E 27 = Z_to_bv 64 SB)
    by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); rewrite (ew_Ereg_nat regs _ 27 27%bv eq_refl); exact R27).
  clear HE.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (VI : forall j v, VAL (A_HI j) = v -> (A_HI j < A_LIM)%nat -> 0 <= v < 2 ^ 64 -> ew E (A_HI j) = Z_to_bv 64 v).
  { intros j v Hv Hj Hr. apply bv_eq. rewrite (HEI (A_HI j) ltac:(unfold A_HI, A_TEXT in *; lia)).
    rewrite unsigned_lit_small by exact Hr. exact Hv. }
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (E260 : ew E (A_OBJ 19) = Z_to_bv 64 (rg_s fr_RG))
    by (apply bv_eq; rewrite (HEI (A_OBJ 19) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia));
        rewrite unsigned_lit_small by (rewrite Hgs; lia); rewrite PVO19; reflexivity).
  change (A_OBJ 19) with 260%nat in E260.
  (* every fact of the cut but the slots the set-up stores, for any memory that keeps the bytes outside them *)
  assert (Herr : 0 <= as_errno B /\ as_errno B + 4 <= CEIL8)
    by (rewrite HEV; unfold TFIB_ERRNO_B, CEIL8; pose proof lt_ceil_lo; lia).
  assert (KEEPF : forall mf, (forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W mem W mf a) ->
    amodel_at B ly3 S3 W mf m /\ ainput_at B cx ly3 S3 W mf /\ rom_view segs W mf /\ jt_rom W mf /\
    pro_fr cx FF (flag_addr ly3 1 fpos) W mf).
  { intros mf KO.
    assert (KL : forall a, 0 <= a < CEIL8 -> abyte_kept W mem W mf a)
      by (intros a Ha; apply KO; unfold CEIL8 in *; lia).
    assert (HRVf : rom_view segs W mf) by exact (lt_rom_kept W W mem mf HRV KL).
    split; [exact (lt_amodel_kept B LAWS ly3 S3 W mem md W mf m HAR HMOD (proj1 Herr) (proj2 Herr) KL)|].
    split; [exact (lt_ainput_kept B LAWS cx ly3 S3 W mem md W mf HAR HIN (eq_sym HlenP) KL)|].
    split; [exact HRVf|]. split; [exact (lt_jt_kept W W mem mf (pro_jt W mem HRV) KL)|].
    assert (KH : forall a v, (forall x, a <= x < a + 8 -> abyte_kept W mem W mf x) -> sv8 W mem a v -> sv8 W mf a v)
      by (intros a v Hk Hv; exact (lt_sv8_kept W W mem mf a v Hk Hv)).
    split; [intros o r Hor; apply KH; [|exact (HSV o r Hor)]; intros x Hx;
            unfold saved_regs in Hor; cbn [In] in Hor;
            repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; apply KO; unfold sp0 in *; lia|]);
            destruct Hor|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H32]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H40]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H56]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H64]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H72]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H80]|].
    split; [apply KH; [intros x Hx; apply KO; lia | exact H104]|].
    split; [apply KH; [intros x Hx; apply KO; unfold sp0 in *; lia | exact H184]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH0]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH8]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HH16]|].
    split; [apply KH; [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFL]|].
    split; [apply (akept_awr W mem W mf); [intros x Hx; apply KL; unfold CEIL8 in *; lia | exact HFW]|].
    split; [apply (akept_garr8 W mem W mf); [intros x Hx; apply KL; cbn [length fake_shadow] in Hx;
            pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia
            | exact HSH]|].
    apply (akept_awr W mem W mf); [intros x Hx; apply KL;
      pose proof (Z.div_le_upper_bound FF 8 (2 ^ 44) ltac:(lia) ltac:(lia)); unfold SB, CEIL8 in *; lia | exact HSW]. }
  paj_run_to_tok RUNTOX HS HJ SHOK Bspan AF_LLVM_head.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr;
        first [ lia | left; split; [left; unfold sp0 in *; lia | lia] ] | ]).
    destruct Hin'. }
  clear HF.
  lazymatch type of HFr with frame_of _ _ (mrestrict _ ?m1) (mrestrict _ ?m2) =>
    assert (KO1 : forall a, 0 <= a < 2 ^ 64 -> ~ (F + 48 <= a < F + 56) -> ~ (F + 96 <= a < F + 104) ->
      ~ (F + 120 <= a < F + 160) -> abyte_kept W m1 W m2 a) end.
  { intros a Ha H1 H2 H3. apply (pro_kept_frame E _ W _ _ a HFr Ha). intros (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?U9 in Hr; lia | ]).
    destruct Hin'. }
  clear HFr.
  pose proof (regs_kept_of_st_ok_pi (PI := PB_fr) _ _ _ regs pro2_extra pro_kept HS HAE
    ltac:(vm_compute; reflexivity)) as KR.
  cbn [ms_regs restrict] in KR.
  prreg HS (18%bv : bv 5) Q18. prreg HS (23%bv : bv 5) Q23. prreg HS (25%bv : bv 5) Q25. prreg HS (26%bv : bv 5) Q26.
  pro_rgn HS 0%nat HR48. pro_rgn HS 1%nat HR96. pro_rgn HS 2%nat HR120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 0 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D120.
  pose proof (pro_sh_den E 27 260 SB (rg_s fr_RG) 4 E27 E260 ltac:(unfold SB; lia) ltac:(rewrite Hgs; lia)
    ltac:(rewrite Hgs; lia)) as D152.
  rewrite Z.add_0_r in D120.
  pmkst HS.
  lazymatch goal with |- SRr _ _ {| cfg_ms := mkst ?rf _ ?mf _; cfg_model := ?df |} _ =>
    apply SRr_ret; exists rf, mf, df end.
  split; [reflexivity|].
  lazymatch type of KO1 with forall a, _ -> _ -> _ -> _ -> abyte_kept _ _ _ ?m2 _ =>
    destruct (KEEPF m2 KO1) as (HMODf & HINf & HRVf & HJTf & HFRf) end.
  pose proof HFRf as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HFLf & _).
  split; [exact HJTf|].
  exists [(1, fpos)], ly3, S3, k, m, fpos.
  split; [exact HJ|]. split; [reflexivity|].
  split.
  { apply (pro_aframe cx FF (flag_addr ly3 1 fpos) W _ HFRf).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 48 56 48 56 48 8 (SOff 260 0) (rg_s fr_RG) HR48 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 96 104 96 104 96 8 (SOff 24 0) (SB + FF / 8) HR96 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E24, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity)
        ltac:(unfold SB in *; cbn [Z.of_N Z.mul]; lia) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 120 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 0) (SLit 3))) (SB + rg_s fr_RG / 8) HR120 U9
        ltac:(cbn [In]; tauto) D120
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 128 8 (SOff 260 4) (rg_s fr_RG + 4) HR120 U9
        ltac:(cbn [In]; tauto) ltac:(cbn [sv_denot]; rewrite E260, unsigned_lit_small by (rewrite Hgs; lia); reflexivity)
        ltac:(rewrite Hgs; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 136 8 (SLit DIV10) DIV10 HR120 U9
        ltac:(cbn [In]; tauto) eq_refl
        ltac:(unfold DIV10; split; [vm_compute; discriminate | vm_compute; reflexivity]) ltac:(zside)).
    - exact (field_of_region (PI := PB_fr) E _ 9 F _ 120 160 120 160 152 8
        (SAlu ALU_ADD (SOff 27 0) (SAlu ALU_SRL (SOff 260 4) (SLit 3))) (SB + (rg_s fr_RG + 4) / 8) HR120 U9
        ltac:(cbn [In]; tauto) D152
        ltac:(rewrite Hgs; unfold SB; split; [vm_compute; discriminate | vm_compute; reflexivity])
        ltac:(zside)).
    - exact (pro_frame_wr cx _ _ _ _ W _ _ HJ).
    - lia.
    - lia. }
  split; [exact HFLf|].
  split; [exact HMODf|]. split; [exact HINf|]. split; [exact HRVf|].
  split; [exact HSEP|]. split; [exact HLS|]. split; [exact HRI|].
  unfold lregs_H, lregs_common.
  split.
  { split; [rewrite (KR 2%bv ltac:(cbv; tauto)); exact R2|].
    split; [rewrite (KR 8%bv ltac:(cbv; tauto)); exact R8|].
    split; [rewrite (KR 9%bv ltac:(cbv; tauto)); exact R9|].
    split; [rewrite Q18; change 350%nat with (A_HI 70); apply VI; [exact PV70 | cbv; lia | unfold HI_G_SRC; lia]|].
    split; [rewrite (KR 19%bv ltac:(cbv; tauto)); exact R19|].
    split; [rewrite Q23; reflexivity|].
    split; [rewrite (KR 24%bv ltac:(cbv; tauto)); exact R24|].
    split; [rewrite Q26; change 349%nat with (A_HI 69); apply VI; [exact PV69 | cbv; lia | unfold HI_G_NOUT; lia]|].
    split; [rewrite (KR 27%bv ltac:(cbv; tauto)); exact R27|].
    split; [rewrite (KR 3%bv ltac:(cbv; tauto)); exact R3|].
    rewrite (KR 4%bv ltac:(cbv; tauto)); exact R4. }
  split; [rewrite Q25; reflexivity|].
  split; [rewrite (KR 21%bv ltac:(cbv; tauto)), Hk0, Z.sub_0_r; exact R21|].
  split; [rewrite (KR 22%bv ltac:(cbv; tauto)), Hk0, Z.add_0_r; exact R22|].
  split; [unfold OPS_MAX; lia|].
  rewrite Hk0. lia.
Qed.


(* ------------------------------------------------------------------ op_add's call: what the callee keeps *)
(* values and arrays read through a kept view *)
Lemma pro_garr8_view : forall (W W' : world segs) mem mem' a l,
  (forall x, a <= x < a + Z.of_nat (length l) -> aview segs (w_H W') mem' x = aview segs (w_H W) mem x) ->
  garr8 segs (arm W mem) a l -> garr8 segs (arm W' mem') a l.
Proof.
  intros W W' mem mem' a l HV Hg j Hj. destruct (Hg j Hj) as [Hv Hr]. split; [|exact Hr].
  apply (ad_vm_view W W' mem mem'); [|exact Hv]. intros x Hx. apply HV. lia.
Qed.
(* the fake frame keeps its place across a journal (frame_addr / flag_addr read only ly_F, which layout_le keeps) *)
Lemma pro_ff_eq : forall G XO OUT STK sp0 FP ly S (W : world segs) mem md own ly' S' W' mem' md' k cid pos,
  ajournal_gx segs B G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k ->
  frame_addr ly' cid pos = frame_addr ly cid pos /\ flag_addr ly' cid pos = flag_addr ly cid pos.
Proof.
  intros G XO OUT STK sp0 FP ly S W mem md own ly' S' W' mem' md' k cid pos (_ & _ & (memS & HJi & _) & _).
  pose proof HJi as (_ & Hly & _). destruct Hly as (_ & _ & _ & _ & _ & EF & _).
  unfold frame_addr, flag_addr. rewrite EF. split; reflexivity.
Qed.
(* the blocks after op_add, as ablocks_sep lists them *)
Lemma pro_sep_perm : forall (al al0 inp aob rest : list (Z * Z)) T T' q,
  Permutation al0 (inp ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aob ++ rest) ->
  ((T = 0 /\ Permutation al ((T', ATABLE) :: (q, APARTIAL) :: al0)) \/
   (T <> 0 /\ T' = T /\ Permutation al ((q, APARTIAL) :: al0))) ->
  Permutation al (inp ++ ((T', ATABLE) :: (q, APARTIAL) :: aob) ++ rest).
Proof.
  intros al al0 inp aob rest T T' q H0 [(HT & HP) | (HT & -> & HP)].
  - rewrite HT in H0. cbn [Z.eqb] in H0. rewrite HP, H0.
    exact (Permutation_app_swap_app [(T', ATABLE); (q, APARTIAL)] inp (aob ++ rest)).
  - rewrite (proj2 (Z.eqb_neq T 0) HT) in H0. rewrite HP, H0.
    eapply perm_trans; [exact (Permutation_app_swap_app [(q, APARTIAL)] inp ([(T, ATABLE)] ++ aob ++ rest))|].
    apply Permutation_app_head. apply perm_swap.
Qed.
(* op_add's afn_pre at sp = F: the donor's afn_pre_at, whose achain is the entry's chain with this frame pushed
   (the prologue saved ra at sp0-8 and s0 at sp0-16: achain_push) -- or, when sp0 is within 16 bytes of the stack
   top, the empty chain (lib/B/W_LLVMFuzzerTestOneInput_add.v lt_afn_pre_at, from the saved registers alone) *)
Lemma pro_afn_pre_at : forall cx ly3 S3 fpos k (W : world segs) mem md regs STK1,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k ->
  (forall o r, In (o, r) saved_regs -> sv8 W mem (spZ (c_regs cx) - o) (bv_unsigned (getr (c_regs cx) (Z_to_bv 5 r)))) ->
  spZ regs = lf_F cx -> YK0s.ret_ok (getr regs 1) -> 4096 <= raZ regs ->
  getr regs 3 = w64 (as_gp B) -> getr regs 4 = w64 (as_tp B) -> getr regs 8 = getr (c_regs cx) 2 ->
  0 <= STK1 -> STK1 + 352 <= LLVMF_STK ->
  exists ch, afn_pre segs B STK1 ly3 S3 W regs mem md ch.
Proof.
  intros cx ly3 S3 fpos k W mem md regs STK1 HB HJ HSV Hsp Hret Hra4 Hgp Htp Hs0 HSTK0 HSTKb.
  destruct HB as (_ & HPRE).
  assert (HPREE : afn_pre segs B LLVMF_STK (c_ly cx) (c_S cx) (c_W cx) (c_regs cx) (c_mem cx) (c_md cx) [])
    by (unfold fr_lib_pre_cf in HPRE; tauto).
  pose proof HPREE as (HAR0 & Hra0 & Hra40 & Hgp0 & Htp0 & Hstk0 & Hpres0 & Hch0 & HQT0).
  pose proof Hstk0 as (Hal16 & Hslo0 & Hceil0 & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  destruct (ajournal_gx_inner segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ) as (memS & HJ0 & Hmg).
  rewrite !Z.add_0_r in HJ0.
  set (sp0 := spZ (c_regs cx)) in *.
  assert (HF32 : lf_F cx = sp0 - 320 - (sp0 - 320) mod 32) by reflexivity.
  pose proof (Z.mod_pos_bound (sp0 - 320) 32 ltac:(lia)) as Hmb.
  assert (Ho16 : (lf_F cx - sp0) mod 16 = 0).
  { rewrite HF32.
    replace (sp0 - 320 - (sp0 - 320) mod 32 - sp0) with (- (320 + (sp0 - 320) mod 32)) by lia.
    assert (H32 : (sp0 - 320) mod 32 = 0 \/ (sp0 - 320) mod 32 = 16).
    { assert (E16 : (sp0 - 320) mod 16 = 0)
        by (replace (sp0 - 320) with (sp0 + (-20) * 16) by lia; rewrite Z.mod_add by lia; exact Hal16).
      pose proof (Z.div_mod ((sp0 - 320) mod 32) 16 ltac:(lia)) as D.
      assert (E2 : ((sp0 - 320) mod 32) mod 16 = 0)
        by (rewrite <- Znumtheory.Zmod_div_mod by (try lia; exists 2; reflexivity); exact E16).
      rewrite E2, Z.add_0_r in D.
      assert (Hq : (sp0 - 320) mod 32 / 16 = 0 \/ (sp0 - 320) mod 32 / 16 = 1) by lia.
      destruct Hq as [Hq | Hq]; rewrite Hq in D; lia. }
    destruct H32 as [H32 | H32]; rewrite H32; reflexivity. }
  assert (HoNeg : lf_F cx - sp0 <= 0) by (rewrite HF32; lia).
  assert (HoBud : STK1 - (lf_F cx - sp0) <= LLVMF_STK) by (rewrite HF32; lia).
  assert (HTOPeq : ly_top ly3 = ly_top (c_ly cx)).
  { pose proof HJ0 as (_ & Hly & _). pose proof Hly as (_ & _ & _ & _ & _ & _ & _ & _ & Etop & _). exact Etop. }
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (Hs0Z : s0Z regs = sp0) by (unfold s0Z, sp0, spZ; rewrite Hs0; reflexivity).
  destruct (Z_lt_le_dec sp0 (ly_top (c_ly cx) - 16)) as [Hlt | Hge].
  - pose proof (aview_above_of_journal (PI := PB_fr) B LLVMF_STK sp0 (lf_FP fr_FP cx)
      (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx) [(1, fpos)] ly3 S3 W mem md k HJ0) as HAB.
    assert (Hra8 : rdword (aview segs (w_H W) mem) (sp0 - 8) = Some (bv_unsigned (getr (c_regs cx) 1))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 8 1 ltac:(left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 1)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    assert (Hs016 : rdword (aview segs (w_H W) mem) (sp0 - 16) = Some (bv_unsigned (getr (c_regs cx) 8))).
    { apply (rdword_of_val_mem segs (w_H W) mem); [exact (HSV 16 8 ltac:(right; left; reflexivity)) |].
      pose proof (bv_unsigned_in_range 64 (getr (c_regs cx) 8)) as Hr.
      change (bv_modulus 64) with (2 ^ 64) in Hr. lia. }
    exists ((sp0, bv_unsigned (getr (c_regs cx) 1), bv_unsigned (getr (c_regs cx) 8)) :: []).
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hsp, Hs0Z.
    apply (achain_ly_top (c_ly cx) ly3 _ _ _ _ ltac:(exact HTOPeq)).
    eapply (achain_push (c_ly cx) (aview segs (w_H (c_W cx)) (c_mem cx)) (aview segs (w_H W) mem)
      sp0 (bv_unsigned (getr (c_regs cx) 8)) (bv_unsigned (getr (c_regs cx) 1)) [] (lf_F cx));
      [ exact Hch0 | lia
      | intros a Ha; rewrite (HAB a ltac:(lia)); apply Hmg; rewrite unsigned_lit_small by lia; intros HGa;
        pose proof (pa_segs_low a (proj1 (HG a HGa))); lia
      | exact Hra8 | exact Hs016
      | unfold raZ in Hra40; lia | lia
      | rewrite (Znumtheory.Zmod_div_mod 8 16 sp0) by (try lia; exists 2; reflexivity); rewrite Hal16; reflexivity
      | lia | rewrite HF32; lia ].
  - exists [].
    eapply (afn_pre_at segs B LLVMF_STK sp0 (lf_FP fr_FP cx) (c_ly cx) (c_S cx) (c_W cx) memS (c_md cx)
      [(1, fpos)] ly3 S3 W mem md k regs STK1 (lf_F cx - sp0) _ HJ0);
      [ rewrite Hsp; lia | exact Ho16 | exact HoNeg | exact HSTK0 | exact HoBud | exact Hret | exact Hra4
      | exact Hgp | exact Htp | ].
    rewrite Hs0Z. left. split; [right; left; rewrite HTOPeq; exact Hge | reflexivity].
Qed.
(* a callee-saved register across the call *)
Lemma pro_pres : forall regs regs' (r : bv 5), aregs_preserved regs regs' -> acallee_saved (bv_unsigned r) ->
  getr regs' r = getr regs r.
Proof. intros regs regs' r HP Hr. pose proof (HP _ Hr) as H. rewrite !Z_to_bv_bv_unsigned in H. exact H. Qed.
(* lib/B/W_op_add.v states oa_spec over lib/B's copy of YCbq (its afn_pre is that module's constant); the cut, the
   journal and this file use lib/Reusable's.  The two afn_pre bodies are the same text over the same AR, so the one
   is the other by conversion. *)
Lemma pro_afn_pre_B : forall STK ly S (W : world segs) regs mem md ch,
  afn_pre segs B STK ly S W regs mem md ch ->
  OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.YCbq.afn_pre segs B STK ly S W regs mem md ch.
Proof. intros STK ly S W regs mem md ch H. exact H. Qed.

(* the prologue's global stores, as the call sees them *)
Definition pro_glob (W : world segs) (mem : word -> option byte) : Prop :=
  val_mem segs (arm W mem) (rg_client fr_RG) 4 3 /\ val_mem segs (arm W mem) (rg_client_broken fr_RG) 1 0 /\
  val_mem segs (arm W mem) AG_NFD 4 0 /\ val_mem segs (arm W mem) (rg_send_max fr_RG) 8 0 /\
  val_mem segs (arm W mem) (rg_gone fr_RG) 1 0 /\ val_mem segs (arm W mem) (rg_send_dead fr_RG) 1 0 /\
  val_mem segs (arm W mem) (rg_send_eintr fr_RG) 1 0.
(* the bytes the prologue keeps from the entry to the call *)
Definition pro_ks (cx : lfcx) (a : Z) : Prop :=
  inG G_keep a \/ exists p n, In (p, n) (ablocks B (c_ly cx) (c_S cx)) /\ p <= a < p + req_size n.
(* relay_add's four globals are apart from g_s's 384 bytes (lib/A/W_op_add.v oa_ra_g, at B's addresses) *)
Lemma pro_ra_g : forall a, inG (RA_G fr_globals) a -> ~ (rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC).
Proof.
  intros a Ha.
  exact (pro_apart_ok (rg_s fr_globals) (4 * ASRC) (RA_G fr_globals) ltac:(vm_compute; reflexivity) a Ha).
Qed.

(* W_op_add.v's AR oa_call_keep / _blk / _hi (this base's lib/B/W_op_add.v, Section c), restated here: W2's
   W_op_add.v of record (a working branch 11fb7104fb5) states those three names over ARx, so this AR walk keeps
   their AR texts and proofs under pro_ names *)
Lemma pro_oa_call_keep : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k -> ~ YI16.sink_open_fp FP ->
forall a, in_img segs a -> ~ inG G' a -> ~ Exists (in_zr a) (as_owned_static B) ->
~ (as_errno B <= a < as_errno B + 4) ->
aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HJx Hsk a Him HnG Hno He.
pose proof (pa_segs_low a Him) as Hlo. unfold kLowMemEnd in Hlo.
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & F3 & _).
rewrite (F3 a Him Hno He ltac:(apply fp_spares_closed; exact Hsk)).
apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. exact HnG.
Qed.
Lemma pro_oa_call_keep_blk : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
gx_ok segs B G' ->
ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
forall p n j, In (p, n) (ablocks B ly0 S0) -> In (p, n) (ablocks B ly1 S1) -> 0 <= j < req_size n ->
~ inFP FP (p + j) -> aview segs (w_H W1) m1 (p + j) = aview segs (w_H W0) m0 (p + j).
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx p n j H0 H1 Hj Hfp.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _). rewrite !Z.add_0_r in HJi.
pose proof HJi as (HAR1 & _ & _ & _ & _ & _ & _ & _ & _ & F2 & _).
rewrite (F2 p n j H0 H1 Hj Hfp).
destruct (al_blocks _ _ LAWS ly1 S1 W1 m1 md1 p n HAR1 H1) as (_ & H4096 & Hbc & _).
apply (aview_gagree segs G' (w_H W0) m0 memS (p + j) HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
exact (blk_img segs B LAWS ly1 S1 W1 m1 md1 p n (p + j) HAR1 H1 ltac:(lia) (proj1 (HGok _ Hin))).
Qed.
Lemma pro_oa_call_keep_hi : forall G' STK sp0 FP ly0 S0 (W0 : world segs) m0 md0 ly1 S1 (W1 : world segs) m1 md1 k,
gx_ok segs B G' ->
ajournal_gx segs B G' 0 [] STK sp0 FP ly0 S0 W0 m0 md0 [] ly1 S1 W1 m1 md1 k ->
forall a, alloc_ceiling <= a < 2 ^ 64 -> ~ (sp0 - STK <= a < sp0) ->
aview segs (w_H W1) m1 a = aview segs (w_H W0) m0 a.
Proof.
intros G' STK sp0 FP ly0 S0 W0 m0 md0 ly1 S1 W1 m1 md1 k HGok HJx a Ha Hno.
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
destruct HJx as (_ & _ & (memS & HJi & HAG) & _).
rewrite !Z.add_0_r in HJi.
pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & F1 & _).
rewrite (F1 a Ha Hno).
apply (aview_gagree segs G' (w_H W0) m0 memS a HAG).
apply inGb_false. rewrite unsigned_lit_small by lia. intros Hin.
pose proof (pa_segs_low a (proj1 (HGok a Hin))). unfold kLowMemEnd in *. lia.
Qed.
(* ------------------------------------------------------------------ 0x84590 `jal op_add` *)
Lemma pro_mid : forall cx regs mem md S2 k fpos,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) mem md k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  pro_fr cx (frame_addr (c_ly cx) 1 fpos) (flag_addr (c_ly cx) 1 fpos) (c_W cx) mem ->
  getr regs 1 = w64 (BASE + A_pro_ret) -> pro_regs cx (frame_addr (c_ly cx) 1 fpos) regs ->
  pro_glob (c_W cx) mem ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) mem a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (cfg_at segs (BASE + AF_fr_op_add) regs mem md) (INV_H B G_fr fr_FP LS RINV cx 0).
Proof.
  intros cx regs mem md S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HFR Hra HRG HGL KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hgi & Hrom & _).
  destruct Hgi as (HGP0 & HCL & (T & HRR) & (c0 & O & mx0 & cap & out & HAO) & (gn0 & HGN) & HLK & HWK & HTU &
    (lst & HLS0) & HLW).
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  pose proof (HFP_pro cx T c0 O mx0 cap out HB HRR HAO) as ((rest0 & HPERM0) & HFPT & HFPO).
  set (W := c_W cx) in *. set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  set (sp0 := spZ (c_regs cx)) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR2.
  assert (Hgs : rg_s fr_RG = 0x5d8e60) by (vm_compute; reflexivity).
  assert (Hgs' : rg_s fr_globals = 0x5d8e60) by (vm_compute; reflexivity).
  (* ---- kept from the entry to the call ---- *)
  assert (KG : forall a, inG G_keep a -> aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros a Ha; apply KEEP; left; exact Ha).
  assert (KBk : forall p n a, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> p <= a < p + req_size n ->
      aview segs (w_H W) mem a = aview segs (w_H W) (c_mem cx) a)
    by (intros p0 n0 a Hp Ha; apply KEEP; right; exists p0, n0; split; [exact Hp | exact Ha]).
  assert (KGv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W mem) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W (c_mem cx) mem); [|exact Hv].
    intros x Hx. exact (KG x (rng_cover a (Z.of_nat n0) G_keep Hr x Hx)). }
  assert (AW : forall a n, rng_inb a n G_fr_obj = true -> forall (W' : world segs) m', awr W' m' a n).
  { intros a n0 Hr W' m' i Hi. apply (G_obj_wr (a + i) (rng_cover a n0 G_fr_obj Hr (a + i) ltac:(lia))). }
  (* ---- the call's facts ---- *)
  assert (HCLc : forall i, (i < 4)%nat -> asrc_closed W mem (oa_HA i)).
  { intros i Hi. destruct (HCL i Hi) as [HZ _]. split.
    - apply (pro_garr8_view W W (c_mem cx) mem); [|exact HZ].
      intros x Hx. apply KG. rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply (rng_cover (rg_s fr_globals) (4 * ASRC) G_keep ltac:(vm_compute; reflexivity)).
      unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 0 \/ i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[->|[->| ->]]]; vm_compute; reflexivity. }
  assert (Hos : forall i, nth i [0; 0; 0; 0] 0 = 0) by (intros i; destruct i as [|[|[|[|[|i]]]]]; reflexivity).
  assert (HRRc : ra_rel B fr_RG (c_ly cx) S2 W mem T []).
  { destruct HRR as [(HT0 & _ & (E1 & E2 & E3 & E4 & E5 & E6)) | HAT].
    - left. split; [exact HT0|]. split; [reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E1]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E3]|]. split; [apply AW; vm_compute; reflexivity|].
      split; [apply KGv; [vm_compute; reflexivity | exact E5] | apply AW; vm_compute; reflexivity].
    - right. pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _).
      apply (arelay_at_kept B fr_RG (c_ly cx) (c_S cx) W (c_mem cx) (c_ly cx) S2 W mem T [] HAT).
      + intros r Hr a Ha. split.
        * unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- apply KG. refine (rng_cover (rg_src fr_RG) 8 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_nsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply KG. refine (rng_cover (rg_capsrc fr_RG) 4 G_keep _ a ltac:(lia)). vm_compute. reflexivity.
          -- apply (KBk T ATABLE a HTin). change (req_size ATABLE) with 896. unfold ATABLE in Ha. lia.
        * intros _. unfold arelay_fp in Hr. cbn [map concat app] in Hr.
          destruct Hr as [<- | [<- | [<- | [<- | []]]]]; cbn [fst snd] in Ha.
          -- refine (G_obj_wr a (rng_cover (rg_src fr_RG) 8 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_nsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- refine (G_obj_wr a (rng_cover (rg_capsrc fr_RG) 4 G_fr_obj _ a ltac:(lia)) _). vm_compute. reflexivity.
          -- rewrite <- Eab2 in HTin.
             destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & _ & Hpr & _).
             apply (apresent_writable segs). apply (proj1 (Hpr a ltac:(change (req_size ATABLE) with 896;
               unfold ATABLE in Ha; lia))).
      + intros b Hb. rewrite Eab2. cbn [arelay_blks map concat app] in Hb. destruct Hb as [<- | []]. exact HTin. }
  assert (HLKc : alock_at fr_RG W mem false).
  { destruct HLK as (L1 & L2 & L3 & L4).
    split; [apply KGv; [vm_compute; reflexivity | exact L1]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L2]|].
    split; [apply KGv; [vm_compute; reflexivity | exact L3] | apply AW; vm_compute; reflexivity]. }
  assert (HWKc : awake_at fr_RG W mem) by (apply KGv; [vm_compute; reflexivity | exact HWK]).
  assert (HRVc : rom_view segs W mem)
    by (eapply ajournal_gx_rom_view; first [exact Hsegs | exact LAWS | exact HJ | exact pro_rom_out_fr | exact Hrom]).
  (* ---- op_add's afn_pre, its room and its meter ---- *)
  pose proof HFR as (HSV & H32 & H40 & H56 & H64 & H72 & H80 & H104 & H184 & HH0 & HH8 & HH16 & HFLw & HFW & HSH & HSW).
  pose proof HRG as (R2 & R8 & R9 & R19 & R21 & R22 & R24 & R27 & R3 & R4).
  assert (Hsp : spZ regs = F) by (unfold spZ; rewrite R2; apply unsigned_lit_small; unfold CEIL8 in *; lia).
  destruct (pro_afn_pre_at cx (c_ly cx) S2 fpos k W mem md regs OA_STK HB HJ HSV Hsp) as (ch & HPREc).
  { rewrite Hra. apply ret_ok_codeptr_v; [unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia | reflexivity]. }
  { unfold raZ. rewrite Hra, unsigned_lit_small by (unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput; lia).
    unfold A_pro_ret, AF_fr_LLVMFuzzerTestOneInput. lia. }
  { exact R3. } { exact R4. } { exact R8. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK. lia. }
  { unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK. lia. }
  destruct (LS_pro_oa cx S2 fpos HB Eab2 Hfrs2 Hnev2 Hbb2) as (Hroom & Hmok).
  (* the entry's T: when the table exists it is a live block of the entry, above 4096 *)
  assert (HT4096 : T <> 0 -> 4096 <= T /\ In (T, ATABLE) (ablocks B (c_ly cx) (c_S cx))).
  { intros HT0. destruct HRR as [(HT0' & _) | HAT]; [contradiction|].
    pose proof HAT as (_ & _ & _ & _ & _ & _ & _ & HTin & _). split; [|exact HTin]. rewrite <- Eab2 in HTin.
    destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & H4096 & _). exact H4096. }
  (* ---- op_add, at its own G ---- *)
  assert (HGcov1 : forall a, rg_s fr_globals <= a < rg_s fr_globals + 4 * ASRC -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G (rg_s fr_globals) (4 * ASRC) a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov2 : forall a, A_NFD <= a < A_NFD + 4 -> inG pro_G a)
    by (intros a Ha; exact (pro_inG_rng pro_G A_NFD 4 a ltac:(cbn [In pro_G app RA_G];
          repeat (first [left; reflexivity | right])) Ha)).
  assert (HGcov3 : forall a, inG (RA_G fr_globals) a -> inG pro_G a)
    by (intros a Ha; unfold pro_G; apply inG_app; right; exact Ha).
  destruct HGL as (G1 & G2 & G3 & G4 & G5 & G6 & G7).
  eapply SRr_bind.
  { exact (OA pro_G G_oa_prog W (c_ly cx) S2 regs mem md ch [0; 0; 0; 0] 0 T []
      (pro_afn_pre_B _ _ _ _ _ _ _ _ HPREc)
      ltac:(rewrite Hsp; exact HFal) ltac:(rewrite Hfrs2; vm_compute; reflexivity) eq_refl
      ltac:(intros i _; rewrite Hos; lia)
      ltac:(intros i Hi; rewrite Hos; exact (oa_zero_vm _ _ _ 4 4 (proj1 (HCLc i Hi)) ltac:(lia)
              ltac:(unfold ASRC; cbn; lia)))
      ltac:(intros i Hi _; exact (HCLc i Hi))
      G3 ltac:(lia) HZS HGcov1 HGcov2 HGcov3 HRRc HLKc HWKc HRVc
      ltac:(intros _; split; [cbn; lia | intros []]) Hroom Hmok). }
  cbv beta. intros W3 c3 Hwle3 (ly4 & S4 & regs4 & mem4 & md4 & kk & -> & HJo & HP4 & HAPK & HOK & Hfrs4 & HSome).
  assert (Hof : oa_first [0; 0; 0; 0] = Some 0%nat) by reflexivity.
  rewrite Hof in HSome. cbv beta iota in HSome.
  destruct HSome as (q & T' & pj & HSRC & HNFD & HREL & HLK4 & HPERM & HMLE).
  cbn [app] in HREL. change (100 + 0) with 100 in HSRC, HREL. change (0 + 1) with 1 in HNFD.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJo) as HAR4.
  pose proof (proj1 G_oa_prog) as HGoa.
  assert (Hsk : ~ YI16.sink_open_fp (oa_FP [0; 0; 0; 0] T [])).
  { unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
    intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & _). lia. }
  (* the journal from the entry, through op_add (lifted from pro_G to G_fr) *)
  pose proof (ajournal_gx_G_mono segs B pro_G G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ G_oa_fr HJo) as HJo'.
  assert (HFP1 : forall a, inFP (oa_FP [0; 0; 0; 0] T []) a ->
      (inFP (lf_FP fr_FP cx) a /\ exists b n, In (b, n) (ablocks B (c_ly cx) S2) /\ b <= a < b + req_size n) \/
      in_tmp_block (ablocks B (c_ly cx) (c_S cx)) (ablocks B (c_ly cx) S2) a).
  { intros a Ha. left. unfold oa_FP in Ha. rewrite Hof in Ha. unfold ra_FP in Ha.
    destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [destruct Ha as (r & [] & _)|].
    destruct Ha as (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
    destruct (HT4096 HT0) as (H4096 & HTin).
    split; [apply (HFPT HT0); change (req_size ATABLE) with 896; unfold ATABLE in *; lia|].
    exists T, ATABLE. split; [rewrite Eab2; exact HTin | change (req_size ATABLE) with 896; lia]. }
  pose proof (ajournal_gx_sub segs B LAWS pa_segs_low G_fr LLVMF_STK sp0 0 [] (lf_FP fr_FP cx)
     (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 W mem md k
     OA_STK (spZ regs) 0 [] (oa_FP [0; 0; 0; 0] T []) [] ly4 S4 W3 mem4 md4 kk HJ HJo'
     ltac:(rewrite Hsp; unfold OA_STK, SR_STK, LF_STK, OA_FRAME, ASTACK, YCfn.LLVMF_STK; lia)
     ltac:(lia) ltac:(lia) ltac:(intros a Ha; exfalso; exact (inFP_nil a Ha)) HG HFP1) as HJ4.
  cbn [app] in HJ4.
  destruct (pro_ff_eq _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ 1 fpos HJo) as [EFF EFL]. fold FF in EFF.
  (* ---- what op_add keeps ---- *)
  assert (KP : forall a, inG G_pst a -> aview segs (w_H W3) mem4 a = aview segs (w_H W) mem a).
  { intros a Ha. pose proof (G_pst_obj a Ha) as Ho. destruct (HG a (HGOBJ a Ho)) as (Him & Hno & _).
    exact (pro_oa_call_keep pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HJo Hsk a Him
      (G_pst_oa a Ha) Hno (G_obj_err a Ho)). }
  assert (KPv : forall a n v, rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W mem) a n v -> val_mem segs (arm W3 mem4) a n v).
  { intros a n0 v Hr Hv. apply (ad_vm_view W W3 mem mem4); [|exact Hv].
    intros x Hx. exact (KP x (rng_cover a (Z.of_nat n0) G_pst Hr x Hx)). }
  assert (KGPv : forall a n v, rng_inb a (Z.of_nat n) G_keep = true -> rng_inb a (Z.of_nat n) G_pst = true ->
      val_mem segs (arm W (c_mem cx)) a n v -> val_mem segs (arm W3 mem4) a n v)
    by (intros a n0 v H1 H2 Hv; exact (KPv a n0 v H2 (KGv a n0 v H1 Hv))).
  assert (KS3 : forall i, (1 <= i < 4)%nat -> asrc_closed W3 mem4 (oa_HA i)).
  { intros i Hi. destruct (HCLc i ltac:(lia)) as [HZ _]. split.
    - apply (pro_garr8_view W W3 mem mem4); [|exact HZ]. intros x Hx.
      rewrite repeat_length in Hx. change (Z.of_nat (Z.to_nat ASRC)) with 96 in Hx.
      apply HOK.
      + apply HGcov1. unfold oa_HA, ASRC in *. lia.
      + unfold oa_wr. rewrite Hof. intros [Hx1 | [Hx2 | Hx3]].
        * unfold oa_HA, ASRC in *. cbn [Z.of_nat] in Hx1. lia.
        * unfold oa_HA, ASRC, A_NFD in *. rewrite Hgs' in *. lia.
        * pose proof (pro_ra_g x Hx3). unfold oa_HA, ASRC in *. lia.
    - apply (AW (oa_HA i) ASRC). unfold oa_HA, ASRC.
      assert (i = 1 \/ i = 2 \/ i = 3)%nat as Hc by lia.
      destruct Hc as [->|[-> | ->]]; vm_compute; reflexivity. }
  (* the entry's blocks the call keeps: all but the relay's table, whose new entry relay_add writes *)
  assert (KBo : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) mem (p + j)).
  { intros p n j Hp Hne Hj. assert (Hp2 : In (p, n) (ablocks B (c_ly cx) S2)) by (rewrite Eab2; exact Hp).
    apply (pro_oa_call_keep_blk pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo p n j Hp2).
    - destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)).
      + right. right. exact Hp2.
      + right. exact Hp2.
    - exact Hj.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      pose proof (sep_blocks segs B LAWS (c_ly cx) S2 W mem md p n T ATABLE HAR2 Hp2 HTin (Hne HT0)) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
      unfold ATABLE in *. lia. }
  (* the input block and the controller's buffer are not the relay's table (the entry's blocks are distinct) *)
  assert (ND0 : List.NoDup (input_blks cx ++ (if T =? 0 then [] else [(T, ATABLE)]) ++ aout_blks cap out ++ rest0)).
  { pose proof HPREE as (HAR0 & _). exact (Permutation_NoDup HPERM0 (ad_nodup B LAWS _ _ _ _ _ HAR0)). }
  assert (HinpT : forall p n, In (p, n) (input_blks cx) -> T <> 0 -> (p, n) <> (T, ATABLE)).
  { intros p n Hp HT0 Heq. rewrite Heq in Hp. apply (pro_nd_app _ _ _ (T, ATABLE) ND0 Hp).
    rewrite (proj2 (Z.eqb_neq T 0) HT0). apply in_or_app. left. left. reflexivity. }
  assert (HoutT : forall b, In b (aout_blks cap out) -> T <> 0 -> b <> (T, ATABLE)).
  { intros b Hb HT0 Heq. rewrite Heq in Hb. pose proof (pro_nd_appr _ _ _ ND0) as ND1.
    rewrite (proj2 (Z.eqb_neq T 0) HT0) in ND1. cbn [app] in ND1. inversion ND1 as [|x l Hx _]; subst.
    apply Hx. apply in_or_app. left. exact Hb. }
  assert (KBt : forall p n j, In (p, n) (ablocks B (c_ly cx) (c_S cx)) -> (T <> 0 -> (p, n) <> (T, ATABLE)) ->
      0 <= j < req_size n -> aview segs (w_H W3) mem4 (p + j) = aview segs (w_H W) (c_mem cx) (p + j))
    by (intros p n j Hp Hne Hj; rewrite (KBo p n j Hp Hne Hj); exact (KBk p n (p + j) Hp ltac:(lia))).
  (* ---- the cut after op_add: the controller's stream ---- *)
  destruct (ERRL ly4 S4 W3 mem4 md4 HAR4) as ((v & Hv & Hvr) & Hvw).
  pose proof HAO as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12 & A13 & A14 & A15 & A16 & A17 &
    A18 & A19 & A20 & A21 & A22 & A23 & A24 & A25 & A26).
  assert (HAOp : aout_at B fr_RG ly4 S4 W3 mem4 (W_rep.CTL 3 0 0 0 v) O 0 (Z.of_nat (length O)) cap out).
  { split; [apply KPv; [vm_compute; reflexivity | exact G4]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A3]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A5]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact A7]|].
    split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G1]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G2]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G6]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [apply KPv; [vm_compute; reflexivity | exact G7]|]. split; [apply AW; vm_compute; reflexivity|].
    split; [exact Hv|]. split; [exact Hvw|]. split; [exact Hvr|].
    split; [left; reflexivity|]. split; [left; reflexivity|]. split; [left; reflexivity|].
    split; [left; reflexivity|]. split; [lia|]. split; [reflexivity|].
    destruct A26 as [A26 | (Hc & Hnc & Hio & junk & Hjl & Hjg)]; [left; exact A26|].
    right. split; [exact Hc|]. split; [exact Hnc|].
    assert (Hio2 : In (out, cap) (ablocks B ly4 S4)).
    { destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hio. }
    split; [exact Hio2|]. exists junk. split; [exact Hjl|].
    apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hjg].
    intros x Hx. unfold bzs in Hx. rewrite length_map, length_app in Hx.
    replace x with (out + (x - out)) by lia.
    apply (KBt out cap (x - out)); [exact Hio | intros HT0; apply (HoutT (out, cap));
      [unfold aout_blks; rewrite (proj2 (Z.eqb_neq cap 0) ltac:(lia)); left; reflexivity | exact HT0] |].
    pose proof (req_size_pos cap ltac:(lia)) as [_ Hrc]. lia. }
  (* the input *)
  assert (HINp : ainput_at B cx ly4 S4 W3 mem4).
  { split.
    - destruct Hin as [Hin | (Hn & Hpin)]; [left; exact Hin|]. right. split; [exact Hn|].
      destruct HPERM as [(_ & HP) | (_ & _ & HP)]; apply (Permutation_in _ (Permutation_sym HP)); rewrite Eab2;
        [right; right | right]; exact Hpin.
    - destruct Hin as [(Hn0 & _) | (Hn & Hpin)].
      + rewrite Hnl in Hn0. assert (Hpl : c_pl cx = []) by (apply length_zero_iff_nil; lia).
        rewrite Hpl. intros j Hj. cbn in Hj. lia.
      + apply (pro_garr8_view W W3 (c_mem cx) mem4); [|exact Hgarr].
        intros x Hx. rewrite length_map in Hx. rewrite <- Hnl in Hx. replace x with (c_p cx + (x - c_p cx)) by lia.
        apply (KBt (c_p cx) (c_n cx) (x - c_p cx)); [exact Hpin | intros HT0; apply (HinpT (c_p cx) (c_n cx));
          [unfold input_blks; rewrite (proj2 (Z.eqb_neq (c_n cx) 0) ltac:(lia)); left; reflexivity | exact HT0] |].
        pose proof (req_size_pos (c_n cx) ltac:(lia)) as [_ Hrc]. lia. }
  (* the model *)
  assert (HMOD4 : amodel_at B ly4 S4 W3 mem4 (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out)).
  { unfold amodel_at, pro_m. cbn [lm_hs lm_G lm_es lm_c lm_O lm_mx lm_cap lm_out lm_gn lm_nfd].
    split; [reflexivity|].
    split.
    { intros i Hi. destruct i as [|[|[|[|i]]]]; cbn [nth aslot].
      - exact HSRC.
      - exact (KS3 1%nat ltac:(lia)).
      - exact (KS3 2%nat ltac:(lia)).
      - exact (KS3 3%nat ltac:(lia)).
      - lia. }
    split; [exact HREL|]. split; [exact HAOp|].
    split; [split; [apply KPv; [vm_compute; reflexivity | exact G5]
                  | split; [apply AW; vm_compute; reflexivity | left; reflexivity]]|].
    split; [exact HLK4|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HWK]|].
    split; [exact HNFD|]. split; [apply AW; vm_compute; reflexivity|]. split; [unfold OPS_MAX; lia|].
    split; [apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HTU]|].
    split; [exists lst; apply KGPv; [vm_compute; reflexivity | vm_compute; reflexivity | exact HLS0]|].
    apply AW; vm_compute; reflexivity. }
  (* the frame and the fake frame *)
  assert (HIV : forall x, F <= x < 2 ^ 47 -> aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx. apply (pro_oa_call_keep_hi pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk HGoa HJo x);
      [unfold CEIL8 in *; lia | rewrite Hsp; lia]. }
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  pose proof (frm_off_imgP B _ _ _ _ _ 1 fpos HAR2 Hin1) as HFimg.
  change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg. unfold off_img in HFimg.
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HAR2 Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (FRV : forall x, (FF <= x < FF + 128) \/ (SB + FF / 8 <= x < SB + FF / 8 + 16) ->
      aview segs (w_H W3) mem4 x = aview segs (w_H W) mem x).
  { intros x Hx.
    assert (Hx64 : 0 <= x < 2 ^ 64) by (unfold SB in *; lia).
    assert (Hni : ~ in_img segs x).
    { intros Hi. destruct Hx as [Hx | Hx].
      - exact (frm_img segs B LAWS (c_ly cx) S2 W mem md 1 fpos x HAR2 Hin1
          ltac:(change (fs_frame_bytes 1) with 128; unfold FF in Hx; lia) Hi).
      - pose proof (pa_segs_low x Hi). unfold SB, kLowMemEnd in *. lia. }
    apply (ad_call_keep_frm B pro_G OA_STK (spZ regs) _ _ _ W mem md _ _ W3 mem4 md4 kk 1 fpos x HGoa HJo Hin1);
      [| | exact Hx64 | exact Hni].
    - unfold frame_rng, in_zr, shadow_addr. rewrite <- SB_SHADOW_OFF. cbn [fst snd].
      change (fs_frame_bytes 1) with 128. change (128 / 8) with 16. fold FF.
      destruct Hx as [Hx | Hx]; [left | right]; lia.
    - unfold oa_FP. rewrite Hof. unfold ra_FP. destruct (Z.eqb_spec T 0) as [HT0 | HT0]; [intros (r & [] & _)|].
      intros (r & [<- | []] & Hr). cbn [fst snd length Z.of_nat] in Hr. unfold AENT in Hr.
      destruct (HT4096 HT0) as (H4096 & HTin). rewrite <- Eab2 in HTin.
      destruct (al_blocks _ _ LAWS _ _ _ _ _ T ATABLE HAR2 HTin) as (_ & _ & _ & Happ & _).
      change (req_size ATABLE) with 896 in Happ.
      destruct Hx as [Hx | Hx].
      + pose proof (sep_block_frame segs B LAWS (c_ly cx) S2 W mem md T ATABLE 1 fpos HAR2 HTin Hin1) as Hd.
        unfold zdisjoint in Hd. cbn [fst snd] in Hd. change (req_size ATABLE) with 896 in Hd.
        change (fs_frame_bytes 1) with 128 in Hd. fold FF in Hd. unfold ATABLE in *. lia.
      + apply (fshadow_not_app FF 16 T 896 x ltac:(lia) ltac:(lia) Happ); [unfold SB in Hx; lia | unfold ATABLE in *; lia]. }
  assert (Hin4 : In (1, fpos) (frames S4)) by (rewrite Hfrs4, Hfrs2; left; reflexivity).
  destruct (al_frames _ _ LAWS ly4 S4 W3 mem4 md4 1 fpos HAR4 Hin4) as (_ & _ & HFp & HFs).
  rewrite EFF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFR4 : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) W3 mem4).
  { split.
    { intros o r Hor. apply (ad_vm_view W W3 mem mem4); [|exact (HSV o r Hor)].
      intros x Hx. apply HIV. unfold saved_regs in Hor. cbn [In] in Hor.
      repeat (destruct Hor as [Hor | Hor]; [injection Hor as <- <-; unfold sp0 in *; lia|]). destruct Hor. }
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H32]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H40]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H56]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H64]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H72]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H80]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H104]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply HIV; unfold sp0 in *; lia | exact H184]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH0]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH8]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HH16]|].
    split; [apply (ad_vm_view W W3 mem mem4); [intros x Hx; apply FRV; left; lia | exact HFLw]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split; [apply (pro_garr8_view W W3 mem mem4); [intros x Hx; apply FRV; right; cbn [length fake_shadow] in Hx; lia
            | exact HSH]|].
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers op_add keeps *)
  assert (HRG4 : pro_regs cx FF regs4).
  { split; [rewrite (pro_pres regs regs4 2%bv HP4 ltac:(pro_cs)); exact R2|].
    split; [rewrite (pro_pres regs regs4 8%bv HP4 ltac:(pro_cs)); exact R8|].
    split; [rewrite (pro_pres regs regs4 9%bv HP4 ltac:(pro_cs)); exact R9|].
    split; [rewrite (pro_pres regs regs4 19%bv HP4 ltac:(pro_cs)); exact R19|].
    split; [rewrite (pro_pres regs regs4 21%bv HP4 ltac:(pro_cs)); exact R21|].
    split; [rewrite (pro_pres regs regs4 22%bv HP4 ltac:(pro_cs)); exact R22|].
    split; [rewrite (pro_pres regs regs4 24%bv HP4 ltac:(pro_cs)); exact R24|].
    split; [rewrite (pro_pres regs regs4 27%bv HP4 ltac:(pro_cs)); exact R27|].
    split; [rewrite (pro_pres regs regs4 3%bv HP4 ltac:(pro_cs)); exact R3|].
    rewrite (pro_pres regs regs4 4%bv HP4 ltac:(pro_cs)); exact R4. }
  (* the blocks, as ablocks_sep lists them *)
  assert (Em : model_blks (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) =
    (T', ATABLE) :: (q, APARTIAL) :: aout_blks cap out) by reflexivity.
  assert (ND4 : List.NoDup (ablocks B ly4 S4)) by exact (ad_nodup B LAWS _ _ _ _ _ HAR4).
  assert (HSEP4 : ablocks_sep B fr_FP cx (pro_m q T' pj (W_rep.CTL 3 0 0 0 v) O cap out) ly4 S4).
  { split.
    - exists rest0. rewrite Em. rewrite Eab2 in HPERM. exact (pro_sep_perm _ _ _ _ _ T T' q HPERM0 HPERM).
    - intros b Hb. rewrite Em in Hb. destruct Hb as [<- | [<- | Hb]].
      + destruct HPERM as [(HT0 & HP) | (HT0 & -> & HP)].
        * left. intros Hb'. pose proof (Permutation_NoDup HP ND4) as ND. inversion ND as [|x l Hx ND']; subst.
          apply Hx. right. rewrite Eab2. exact Hb'.
        * right. intros a Ha. cbn [fst snd] in Ha. exact (HFPT HT0 a Ha).
      + left. intros Hb'. destruct HPERM as [(_ & HP) | (_ & _ & HP)]; pose proof (Permutation_NoDup HP ND4) as ND.
        * inversion ND as [|x l _ ND']; subst. inversion ND' as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
        * inversion ND as [|x l Hx _]; subst. apply Hx. rewrite Eab2. exact Hb'.
      + right. exact (HFPO b Hb). }
  (* the cut's two Variables, and the ROM view after op_add *)
  assert (Hc0ex : exists c1 mx1, aout_at B fr_RG (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) c1 O mx1
    (Z.of_nat (length O)) cap out) by (exists c0, mx0; exact HAO).
  assert (HPERM' : exists T0 rest, Permutation (ablocks B (c_ly cx) (c_S cx))
       (input_blks cx ++ (if T0 =? 0 then [] else [(T0, ATABLE)]) ++ aout_blks cap out ++ rest) /\
     ((T0 = 0 /\ Permutation (ablocks B ly4 S4) ((T', ATABLE) :: (q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx))) \/
      (T0 <> 0 /\ T' = T0 /\ Permutation (ablocks B ly4 S4) ((q, APARTIAL) :: ablocks B (c_ly cx) (c_S cx)))))
    by (exists T, rest0; split; [exact HPERM0 | rewrite <- Eab2; exact HPERM]).
  pose proof (LS_pro cx q T' pj (W_rep.CTL 3 0 0 0 v) O cap out S2 fpos ly4 S4 HB Hc0ex eq_refl eq_refl eq_refl
    eq_refl Eab2 Hfrs2 Hnev2 Hbb2 HMLE HPERM') as HLS4.
  pose proof (RI_pro cx q T' pj (W_rep.CTL 3 0 0 0 v) O cap out HB Hc0ex eq_refl eq_refl eq_refl eq_refl) as HRI4.
  assert (HRV4 : rom_view segs W3 mem4)
    by (eapply ajournal_gx_rom_view;
        first [exact Hsegs | exact LAWS | exact HJo | exact (proj1 (proj2 (proj2 G_oa_prog))) | exact HRVc]).
  (* the loop's set-up *)
  rewrite Hra. rewrite <- EFF in HFR4, HRG4. rewrite <- EFL in HFR4.
  exact (pro_fin cx W3 regs4 mem4 md4 ly4 S4 (k + kk) _ fpos HB HJ4 HFR4 HRG4 HMOD4 eq_refl HINp HRV4 HSEP4
    HLS4 HRI4).
Qed.


(* ------------------------------------------------------------------ the state at op_add's entry (0x85194) *)
(* the regions of the token run's state when it reaches op_add (as the run leaves them) *)
Definition pc_g (n : nat) (off w : Z) (sz : N) (v : Z) : YP09.region :=
  YP09.mkRegion (Some n) off (off + w) off (off + w) [YP09.mkChunk off (CVal sz (SLit v))].
(* the fake frame's shadow, in the order 0x844e8-0x8452c stores it (0xf1 x4, 0xf3 x4, 0xf8 x2, 0xf3 x2, 0xf8 x4) *)
Definition pc_sh : YP09.region := YP09.mkRegion (Some 513%nat) 0 16 0 0
  [YP09.mkChunk 7 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 6 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 5 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 4 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 11 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 10 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 9 (CVal 1 (SLit 18446744073709551608)); YP09.mkChunk 8 (CVal 1 (SLit 18446744073709551608));
   YP09.mkChunk 15 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 14 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 13 (CVal 1 (SLit 18446744073709551603)); YP09.mkChunk 12 (CVal 1 (SLit 18446744073709551603));
   YP09.mkChunk 3 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 2 (CVal 1 (SLit 18446744073709551601));
   YP09.mkChunk 1 (CVal 1 (SLit 18446744073709551601)); YP09.mkChunk 0 (CVal 1 (SLit 18446744073709551601))].
(* the fake frame: the header words 0x844d0-0x844dc and the flag pointer __asan_stack_malloc_1 left at FF + 120 *)
Definition pc_ff : YP09.region := YP09.mkRegion (Some 39%nat) 0 128 0 0
  [YP09.mkChunk 16 (CVal 8 (SOff 240 8388)); YP09.mkChunk 8 (CVal 8 (SOff 263 0));
   YP09.mkChunk 0 (CVal 8 (SLit 1102416563)); YP09.mkChunk 120 (CVal 8 (SOff 512 0))].
Definition pc_save : YP09.region := YP09.mkRegion (Some 2%nat) (-104) 0 (-104) 0
  [YP09.mkChunk (-104) (CVal 8 (SOff 27 0)); YP09.mkChunk (-96) (CVal 8 (SOff 26 0));
   YP09.mkChunk (-88) (CVal 8 (SOff 25 0)); YP09.mkChunk (-80) (CVal 8 (SOff 24 0));
   YP09.mkChunk (-72) (CVal 8 (SOff 23 0)); YP09.mkChunk (-64) (CVal 8 (SOff 22 0));
   YP09.mkChunk (-56) (CVal 8 (SOff 21 0)); YP09.mkChunk (-48) (CVal 8 (SOff 20 0));
   YP09.mkChunk (-40) (CVal 8 (SOff 19 0)); YP09.mkChunk (-32) (CVal 8 (SOff 18 0));
   YP09.mkChunk (-24) (CVal 8 (SOff 9 0)); YP09.mkChunk (-16) (CVal 8 (SOff 8 0));
   YP09.mkChunk (-8) (CVal 8 (SOff 1 0))].
Definition pc_F : YP09.region := YP09.mkRegion (Some 34%nat) 32 192 32 192
  [YP09.mkChunk 56 (CVal 8 (SOff 346 0)); YP09.mkChunk 40 (CVal 8 (SOff 345 0));
   YP09.mkChunk 64 (CVal 8 (SOff 344 0)); YP09.mkChunk 72 (CVal 8 (SOff 343 0));
   YP09.mkChunk 32 (CVal 8 (SOff 340 0)); YP09.mkChunk 80 (CVal 8 (SOff 39 0));
   YP09.mkChunk 104 (CVal 8 (SOff 39 0)); YP09.mkChunk 184 (CVal 8 (SOff 39 0))].
Lemma vm_at : forall m a a' (n n' : nat) v, val_mem segs m a n v -> a = a' -> n = n' -> val_mem segs m a' n' v.
Proof. intros m a a' n n' v H -> ->. exact H. Qed.
(* an image atom's value, by computation *)
Ltac pro_rwimg HEI n :=
  let v := eval vm_compute in (VAL n) in
  rewrite (HEI n ltac:(unfold A_TEXT, A_LIM; lia));
  replace (VAL n) with v by (vm_compute; reflexivity).
Lemma pro_at_call : forall cx S2 k fpos E regs4 m4 md4,
  lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  ajournal_gx segs B G_fr 0 [] LLVMF_STK (spZ (c_regs cx)) (lf_FP fr_FP cx)
    (c_ly cx) (c_S cx) (c_W cx) (c_mem cx) (c_md cx) [(1, fpos)] (c_ly cx) S2 (c_W cx) m4 md4 k ->
  ablocks B (c_ly cx) S2 = ablocks B (c_ly cx) (c_S cx) -> frames S2 = [(1, fpos)] ->
  st_nev S2 = st_nev (c_S cx) -> blocks_bytes S2 = blocks_bytes (c_S cx) ->
  img_env VAL A_LIM E ->
  bv_unsigned (ew E 2) = spZ (c_regs cx) -> bv_unsigned (ew E 34) = lf_F cx ->
  bv_unsigned (ew E 39) = frame_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 512) = flag_addr (c_ly cx) 1 fpos ->
  bv_unsigned (ew E 513) = SB + frame_addr (c_ly cx) 1 fpos / 8 -> ew E 33 = Z_to_bv 64 SB ->
  (forall r, (r < 32)%nat -> ew E r = getr (c_regs cx) (Z_to_bv 5 (Z.of_nat r))) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 346 (-1868) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 345 (-1892) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 344 (-1916) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 343 (-1936) 8 8 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 342 (-1964) 4 4 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 341 (-2024) 1 1 0) ->
  region_ok segs E (arm (c_W cx) m4) (pc_g 340 32 4 4 3) ->
  region_ok segs E (arm (c_W cx) m4) pc_sh -> region_ok segs E (arm (c_W cx) m4) pc_ff ->
  region_ok segs E (arm (c_W cx) m4) pc_save -> region_ok segs E (arm (c_W cx) m4) pc_F ->
  getr regs4 1 = Z_to_bv 64 (BASE + A_pro_ret) -> getr regs4 2 = ew E 34 -> getr regs4 3 = ew E 3 ->
  getr regs4 4 = ew E 4 -> getr regs4 8 = ew E 2 -> getr regs4 9 = ew E 34 ->
  getr regs4 19 = Z_to_bv 64 (bv_unsigned (ew E 39) + 32) ->
  getr regs4 21 = ew E 11 -> getr regs4 22 = ew E 10 -> getr regs4 24 = ew E 513 -> getr regs4 27 = ew E 33 ->
  (forall a, pro_ks cx a -> aview segs (w_H (c_W cx)) m4 a = aview segs (w_H (c_W cx)) (c_mem cx) a) ->
  SRr segs (c_W cx) (mkCfg (mkst regs4 (Z_to_bv 64 (BASE + AF_fr_op_add)) m4 (seg_rom segs)) md4)
    (INV_H B G_fr fr_FP LS RINV cx 0).
Proof.
  intros cx S2 k fpos E regs4 m4 md4 HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HEI U2 U34 U39 U512 U513 E33 EA
    RG7 RG6 RG5 RG4 RG3 RG2 RG1 RSH RFF RSV RF Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP.
  pose proof HB as (HAI0 & HPRE0).
  pose proof HPRE0 as (HPREE & Hra0 & H10 & H11 & _).
  pose proof HPREE as (_ & _ & _ & Hgp & Htp & _).
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  pose proof lt_ceil_lo as HCL8.
  pose proof (pro_Fb cx HB) as (HFlo & HFsp & HFsp2 & H47 & HFal & Hal16).
  set (FF := frame_addr (c_ly cx) 1 fpos) in *. set (F := lf_F cx) in *.
  pose proof (ajournal_gx_AR segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ HJ) as HAR.
  assert (Hin1 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HAR Hin1) as (HFF0 & HFF1 & _).
  change (fs_frame_bytes 1) with 128 in HFF1. fold FF in HFF0, HFF1.
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & HFp & HFs).
  fold FF in HFp, HFs. change (fs_frame_bytes 1) with 128 in HFp. change (fs_frame_bytes 1 / 8) with 16 in HFs.
  assert (HFF8 : 0 <= FF / 8 <= 2 ^ 44) by (split; [apply Z.div_pos; lia | apply Z.div_le_upper_bound; lia]).
  assert (ER : forall (r : nat) (b : bv 5), (r < 32)%nat -> Z.of_nat r = bv_unsigned b -> ew E r = getr (c_regs cx) b).
  { intros r b Hr Hb. rewrite (EA r Hr). f_equal. apply bv_eq. rewrite Z_to_bv_unsigned, <- Hb.
    apply bv_wrap_small. change (bv_modulus 5) with 32. lia. }
  (* the frame and the fake frame *)
  assert (HFR : pro_fr cx FF (flag_addr (c_ly cx) 1 fpos) (c_W cx) m4).
  { unfold pro_fr. cbv zeta. fold F.
    split.
    { apply (pro_saved_of_region E _ _ _ _ _ _ _ (c_regs cx) RSV U2 EA).
      unfold saved_regs.
      repeat (apply Forall_cons; [cbn [fst snd In]; repeat (first [left; reflexivity | right]) |]).
      apply Forall_nil. }
    assert (FS : forall off (nv : nat) v, In (YP09.mkChunk off (CVal 8 (SOff nv 0))) (YP09.r_chunks pc_F) ->
        bv_unsigned (ew E nv) = v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (F + off) v).
    { intros off nv v Hc Hv Hr. unfold sv8.
      refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 34 F _ 32 192 32 192 off 8 (SOff nv 0) v RF U34 Hc _ Hr
        ltac:(cbn; lia)) eq_refl eq_refl).
      cbn [sv_denot]. rewrite Hv, Z.add_0_r. reflexivity. }
    split; [apply (FS 32 340%nat); [cbn; tauto | pro_rwimg HEI 340%nat; reflexivity | unfold HI_G_CLIENT; lia]|].
    split; [apply (FS 40 345%nat); [cbn; tauto | pro_rwimg HEI 345%nat; reflexivity | unfold HI_G_SDEAD; lia]|].
    split; [apply (FS 56 346%nat); [cbn; tauto | pro_rwimg HEI 346%nat; reflexivity | unfold HI_G_SEINTR; lia]|].
    split; [apply (FS 64 344%nat); [cbn; tauto | pro_rwimg HEI 344%nat; reflexivity | unfold HI_G_GONE; lia]|].
    split; [apply (FS 72 343%nat); [cbn; tauto | pro_rwimg HEI 343%nat; reflexivity | unfold HI_G_SMAX; lia]|].
    split; [apply (FS 80 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 104 39%nat); [cbn; tauto | exact U39 | lia]|].
    split; [apply (FS 184 39%nat); [cbn; tauto | exact U39 | lia]|].
    assert (FH : forall off e v, In (YP09.mkChunk off (CVal 8 e)) (YP09.r_chunks pc_ff) ->
        sv_denot E e = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 -> sv8 (c_W cx) m4 (FF + off) v).
    { intros off e v Hc Hv Hr. unfold sv8.
      exact (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ 39 FF _ 0 128 0 0 off 8 e v RFF U39 Hc Hv Hr
        ltac:(cbn; lia)) eq_refl eq_refl). }
    split; [rewrite <- (Z.add_0_r FF); apply (FH 0 (SLit 1102416563)); [cbn; tauto | reflexivity | lia]|].
    split; [apply (FH 8 (SOff 263 0)); [cbn; tauto | | lia];
            cbn [sv_denot]; pro_rwimg HEI 263%nat; reflexivity|].
    split; [apply (FH 16 (SOff 240 8388)); [cbn; tauto | | unfold YCfn.A_LLVMF; lia];
            cbn [sv_denot]; pro_rwimg HEI 240%nat; reflexivity|].
    split; [apply (FH 120 (SOff 512 0)); [cbn; tauto | | ];
            [cbn [sv_denot]; rewrite U512, Z.add_0_r; reflexivity
            | destruct (FFL _ _ _ _ _ 1 fpos HAR Hin1) as (_ & _ & _ & (HFL4096 & _ & HFLc)); lia]|].
    split; [intros i Hi; apply (apresent_writable segs); exact (proj1 (HFp (FF + i) ltac:(lia)))|].
    split.
    { apply (pro_shadow_garr8 E _ 513 _ _ 0 16 0 0 RSH U513).
      intros j Hj. do 16 (destruct j as [|j]; [cbn; repeat (first [left; reflexivity | right]) |]). lia. }
    intros i Hi. apply (apresent_writable segs). pose proof (proj1 (HFs i Hi)) as H.
    unfold shadow_addr in H. rewrite <- SB_SHADOW_OFF in H. exact H. }
  (* the registers *)
  assert (HRG : pro_regs cx FF regs4).
  { unfold pro_regs, w64. fold F.
    split; [rewrite Q2, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q8, (ER 2%nat 2%bv ltac:(lia) eq_refl); reflexivity|].
    split; [rewrite Q9, <- U34, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q19, U39; reflexivity|].
    split; [rewrite Q21, (ER 11%nat 11%bv ltac:(lia) eq_refl), H11; reflexivity|].
    split; [rewrite Q22, (ER 10%nat 10%bv ltac:(lia) eq_refl), H10; reflexivity|].
    split; [rewrite Q24, <- U513, Z_to_bv_bv_unsigned; reflexivity|].
    split; [rewrite Q27; exact E33|].
    split; [rewrite Q3, (ER 3%nat 3%bv ltac:(lia) eq_refl), Hgp; reflexivity|].
    rewrite Q4, (ER 4%nat 4%bv ltac:(lia) eq_refl), Htp; reflexivity. }
  (* the globals *)
  assert (GV : forall n off w (sz : N) v a, region_ok segs E (arm (c_W cx) m4) (pc_g n off w sz v) ->
      (A_TEXT <= n < A_LIM)%nat -> VAL n + off = a -> N.to_nat sz = Z.to_nat w -> 0 <= v < 2 ^ (8 * Z.of_N sz) ->
      (Z.of_N sz <= 8) -> val_mem segs (arm (c_W cx) m4) a (Z.to_nat w) v).
  { intros n0 off w sz v a HR Hn Ha Hw Hv Hs.
    refine (vm_at _ _ _ _ _ _ (field_of_region (PI := PB_fr) E _ n0 (VAL n0) _ off (off + w) off (off + w) off sz
      (SLit v) v HR (HEI n0 Hn) ltac:(cbn; tauto) _ Hv Hs) Ha Hw).
    reflexivity. }
  assert (HGL : pro_glob (c_W cx) m4).
  { unfold pro_glob.
    split; [exact (GV 340%nat 32 4 4%N 3 (rg_client fr_RG) RG1 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 341%nat (-2024) 1 1%N 0 (rg_client_broken fr_RG) RG2 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 342%nat (-1964) 4 4%N 0 AG_NFD RG3 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 343%nat (-1936) 8 8%N 0 (rg_send_max fr_RG) RG4 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 344%nat (-1916) 1 1%N 0 (rg_gone fr_RG) RG5 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    split; [exact (GV 345%nat (-1892) 1 1%N 0 (rg_send_dead fr_RG) RG6 ltac:(unfold A_TEXT, A_LIM; lia)
              ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia))|].
    exact (GV 346%nat (-1868) 1 1%N 0 (rg_send_eintr fr_RG) RG7 ltac:(unfold A_TEXT, A_LIM; lia)
      ltac:(vm_compute; reflexivity) eq_refl ltac:(cbn; lia) ltac:(cbn; lia)). }
  (* the return address *)
  assert (Hra : getr regs4 1 = w64 (BASE + A_pro_ret)) by (rewrite Q1; reflexivity).
  exact (pro_mid cx regs4 m4 md4 S2 k fpos HB HJ Eab2 Hfrs2 Hnev2 Hbb2 HFR Hra HRG HGL KEEP).
Qed.

(* ------------------------------------------------------------------ the walk *)
(* ~ in_wrange E rs a, region by region: each window is read off (its base by the U facts in context, an image base
   by HEIx) and refuted by a lia over few facts: an empty window; a stack window above F (Ha, HFlo, HFsp); a window
   the one fact Hk about a misses *)
Ltac pro_nwr_k HEIx Ha HFlo HFsp :=
  let r := fresh "r" in let Hin' := fresh "Hin" in let Hr := fresh "Hr" in
  intros (r & Hin' & Hr);
  lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end;
  cbn [In] in Hin';
  repeat (destruct Hin' as [<- | Hin'];
    [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
      repeat match goal with Hu : bv_unsigned (ew ?E ?x) = _ |- _ =>
        match type of Hr with context [bv_unsigned (ew E x)] => rewrite Hu in Hr end end;
      pro_imgh HEIx Hr; unfold SB in Hr;
      first [ clear - Hr; lia
            | clear - Hr Ha HFlo HFsp; lia
            | match goal with Hk : ~ (_ <= _ < _) |- _ => clear - Hr Hk; lia end
            | match goal with Hk : (_ \/ _) |- _ => clear - Hr Hk; lia end ] | ]);
  destruct Hin'.
Theorem lf_seg_pro : forall cx, lf_base B MT XM_LIB RLO RHI fr_live_pre G_fr cx ->
  SRr segs (c_W cx) (lf_entry cx) (INV_H B G_fr fr_FP LS RINV cx 0).
Proof.
  intros [ly S W regs mem md p n pl M] HB.
  pose proof HB as (HAI & HPRE & Hra0 & H10 & H11 & Hin & Hnl & Hgarr & Hfrs & Hlive & Hgi & Hrom & Hrod & Hsink & Hfd & Hsrt & Hmeta & Hmo & Hstkr & Hhb & _).
  cbn [c_ly c_S c_W c_regs c_mem c_md c_p c_n c_pl c_M lf_entry] in *.
  pose proof pa_wx as Hwx. pose proof pa_segs_low as Hsegs. pose proof pa_B_ok as HBASE. pose proof pa_base_lo as HBLO.
  pose proof lt_ceil_lo as HCL8.
  assert (Rn : 0 <= n < 2 ^ 26) by (destruct Hin as [(-> & _) | (Hn & _)]; lia).
  destruct (pro_entry W ly S regs mem md [] n HPRE H11 Rn) as [HS SHOK].
  pose proof (ajournal_init segs B LLVMF_STK (lf_FP fr_FP (LFCX ly S W regs mem md p n pl M)) ly S W regs mem md [] HPRE) as HJ.
  pose proof HPRE as (HAR & Hra & Hra4 & Hgp & Htp & Hstk & Hpres & Hch & HQT).
  remember (Eimg (Ereg regs (pro_extra regs))) as E eqn:HE. assert (HEI : img_env VAL A_LIM E) by (subst E; apply Eimg_env).
  assert (EE : forall n (r : bv 5), Z.of_nat n = bv_unsigned r -> ew E n = getr regs r)
    by (intros n0 r Hn; subst E; pose proof (bv_unsigned_in_range 5 r) as Hr5; change (bv_modulus 5) with 32 in Hr5;
        rewrite Eimg_low by (unfold A_TEXT; lia); apply ew_Ereg_nat; exact Hn).
  set (F := pro_F regs) in *.
  assert (E32 : ew E 32 = Z_to_bv 64 (as_uar_cell B)) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 0)).
  assert (E33 : ew E 33 = Z_to_bv 64 SB) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 1)).
  assert (E34 : ew E 34 = Z_to_bv 64 F) by (subst E; rewrite Eimg_low by (unfold A_TEXT; lia); exact (ew_Ereg_extra regs _ 2)).
  assert (Usp : bv_unsigned (ew E 2) = spZ regs) by (rewrite (EE 2%nat 2%bv eq_refl); reflexivity).
  assert (HAE : env_agree 32 (Ereg regs (pro_extra regs)) E)
    by (rewrite HE; split; [intros m Hm; apply Eimg_low; unfold A_TEXT; lia | reflexivity]).
  clear HE.
  pose proof Hstk as (Hal16 & Hstk0 & Hceil & Hslo & Hshi & H47 & Hbot & Htop & Htop2).
  pose proof (asan_consts) as (C1 & C2 & C3 & C4 & C5).
  assert (WS : LLVMF_STK = 32768) by reflexivity. assert (Hes : ESTACK = 4096) by reflexivity.
  assert (HFv : F = spZ regs - 320 \/ F = spZ regs - 336) by exact (pro_F_facts (spZ regs) Hal16).
  assert (HFal : F mod 32 = 0) by exact (pro_F_al (spZ regs - 320)).
  assert (HspR : 2 ^ 46 <= F /\ spZ regs <= 2 ^ 47).
  { revert HFv Hslo Hshi H47 Hceil C1 C3 WS Hstk0. clear.
    unfold zone2, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL. intros. lia. }
  assert (UF : bv_unsigned (ew E 34) = F) by (rewrite E34; apply unsigned_lit_small; lia).
  unfold cfg_at. change (w64 YCfn.A_LLVMF) with (Z_to_bv 64 (BASE + A_pro)).
  (* run 1: the frame, the saved registers, the fake-stack test; stops at __asan_stack_malloc_1 (0x84478) *)
  paj_run_tok RUN HS HJ SHOK Bspan.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr; rewrite ?Usp, ?UF in Hr;
        first [ lia | left; lia ] | ]).
    destruct Hin'. }
  (* the call to __asan_stack_malloc_1 (128): the fake frame FF *)
  pmkst HS.
  prreg HS (1%bv : bv 5) R1. prreg HS (2%bv : bv 5) R2. prreg HS (3%bv : bv 5) R3. prreg HS (4%bv : bv 5) R4.
  rewrite (palf_sm1 B TLF).
  eapply SRr_bind.
  { lazymatch goal with |- SRr _ _ (mkCfg (mkst ?rg _ ?mm _) _) _ =>
      eapply (aj_stack_malloc_pres_at segs B LAWS Hsegs (pal_env B TL) ML SMP 1 ASM1 ltac:(lia) W rg mm LLVMF_STK (spZ regs)
        _ ly S W mem md [] ly S _ 0 (F - spZ regs) _ HJ) end.
    - unfold spZ at 1. rewrite R2, UF. lia.
    - destruct HFv as [HFe | HFe]; rewrite HFe;
        [replace (spZ regs - 320 - spZ regs) with ((-20) * 16) by lia | replace (spZ regs - 336 - spZ regs) with ((-21) * 16) by lia];
        apply Z_mod_mult.
    - lia.
    - rewrite WS, Hes. lia.
    - rewrite R3, (EE 3%nat 3%bv eq_refl). exact Hgp.
    - rewrite R4, (EE 4%nat 4%bv eq_refl). exact Htp.
    - exact R1.
    - apply ret_ok_codeptr_v; [lia | reflexivity].
    - rewrite Hfrs. vm_compute. reflexivity. }
  cbv beta. intros W2 c2 _ (-> & S2 & regs2 & mem2 & md2 & fpos & -> & HJ2 & HP2 & Ha0 & Eab & Hfrs2 & Hnin & Hnev2 & Hbb2 & Hz & Hflag & HK & HPg).
  set (FF := frame_addr ly 1 fpos) in *. set (FL := flag_addr ly 1 fpos) in *.
  pose proof (proj1 HJ) as HARa. pose proof (proj1 HJ2) as HARb.
  destruct (al_const _ _ LAWS _ _ _ _ _ HARa) as (Kc1 & Ku1 & Kg1 & Kgu1).
  destruct (al_const _ _ LAWS _ _ _ _ _ HARb) as (Kc2 & Ku2 & Kg2 & Kgu2).
  rewrite HBgot, HBcell in Kg1, Kg2. rewrite HBcell in Kc1, Kc2. rewrite (palf_got_uar B TLF) in Kgu1, Kgu2.
  pose proof (palf_uar_img B TLF) as HuR.
  jafter_call_keep_pi HS 35%nat regs2 (mrestrict (w_H W) mem2) HP2 [0; 1; 2; 3; 4; 5; 6]%nat HS2.
  match type of HS2 with ?ty -> _ => assert (HRK : ty); [|specialize (HS2 HRK); clear HRK] end.
  { cbn [ms_mem restrict]. repeat apply Forall_cons; [| | | | | | | apply Forall_nil].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact Usp | lia | lia | lia | cbn; lia | cbn; lia].
    - eapply (region_kept_stack_aj segs B); [exact HK | exact HJ2 | exact UF | lia | lia | lia | cbn; lia | cbn; lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 0) (VAL (A_OBJ 0)) 8 (VAL (A_OBJ 30)));
        [exact (HEI (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kg1) | exact (val_mem_of_rdword segs _ _ _ _ Kg2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 30) (VAL (A_OBJ 30)) 8 SHADOW_OFF);
        [exact (HEI (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kc1) | exact (val_mem_of_rdword segs _ _ _ _ Kc2) | lia].
    - apply (region_kept_val_at E _ _ (A_OBJ 6) (VAL (A_OBJ 6)) 8 (as_uar_cell B));
        [exact (HEI (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)) | exact (val_mem_of_rdword segs _ _ _ _ Kgu1) | exact (val_mem_of_rdword segs _ _ _ _ Kgu2) | lia].
    - apply (region_kept_val_at E _ _ 32 (as_uar_cell B) 4 1);
        [rewrite E32; apply unsigned_lit_small; lia | exact (val_mem_of_rd32 segs _ _ _ _ Ku1) | exact (val_mem_of_rd32 segs _ _ _ _ Ku2) | lia]. }
  clear HS. rewrite <- restrict_mkst_fx in HS2. rename HS2 into HS.
  remember (havoc E 35 (map (getr regs2) CLOB)) as Ea eqn:HEa in HS.
  assert (HEIa : img_env VAL A_LIM Ea) by (rewrite HEa; apply img_env_havoc; [exact HEI | cbv; lia]).
  assert (OLDa : forall m, (m < 35)%nat -> ew Ea m = ew E m) by (intros m Hm; rewrite HEa; apply YN3v.ew_havoc_old; exact Hm).
  assert (HAEa : env_agree 32 (Ereg regs (pro_extra regs)) Ea) by (rewrite HEa; apply env_agree_havoc_ge; [cbv; lia | exact HAE]).
  clear HEa.
  prreg HS (10%bv : bv 5) RF.
  (* seat the fake frame: FF in atom 39 (a0), its flag FL in 512, the frame's shadow SB + FF / 8 in 513 *)
  assert (Hfin2 : In (1, fpos) (frames S2)) by (rewrite Hfrs2; left; reflexivity).
  destruct (frames_bounds segs B LAWS _ _ _ _ _ 1 fpos HARb Hfin2) as (HF4096 & HFceil & HFhigh).
  destruct (al_frames _ _ LAWS _ _ _ _ _ 1 fpos HARb Hfin2) as (HFal2 & HFapp & HFpres & HFSpres).
  destruct (FFL _ _ _ _ _ 1 fpos HARb Hfin2) as (HFLp & HFLo & (HFLapp & HFLimg) & (HFL4096 & HFLz & HFLc)).
  change (fs_frame_bytes 1) with 128 in *. change (128 / 8) with 16 in *.
  fold FF FL in HFal2, HFapp, HFpres, HFSpres, HFLp, HFLo, HFLapp, HFLimg, HFL4096, HFLz, HFLc, HF4096, HFceil, HFhigh.
  assert (RF' : ew Ea 39 = Z_to_bv 64 FF) by (rewrite <- RF, Ha0; reflexivity).
  assert (E33a : ew Ea 33 = Z_to_bv 64 SB) by (rewrite OLDa by lia; exact E33).
  assert (U2a : bv_unsigned (ew Ea 2) = spZ regs) by (rewrite OLDa by lia; exact Usp).
  assert (U34a : bv_unsigned (ew Ea 34) = F) by (rewrite OLDa by lia; exact UF).
  assert (U32a : bv_unsigned (ew Ea 32) = as_uar_cell B) by (rewrite OLDa, E32 by lia; apply unsigned_lit_small; lia).
  assert (U241 : bv_unsigned (ew Ea 241) = VAL (A_OBJ 0)) by exact (HEIa (A_OBJ 0) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U247 : bv_unsigned (ew Ea 247) = VAL (A_OBJ 6)) by exact (HEIa (A_OBJ 6) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (U271 : bv_unsigned (ew Ea 271) = VAL (A_OBJ 30)) by exact (HEIa (A_OBJ 30) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)).
  assert (HFF8 : FF / 8 = 4 * (FF / 32)).
  { pose proof (Z.div_mod FF 32 ltac:(lia)) as D. rewrite HFal2, Z.add_0_r in D. rewrite D at 1.
    replace (32 * (FF / 32)) with (4 * (FF / 32) * 8) by lia. rewrite Z.div_mul by lia. reflexivity. }
  assert (HFF8lo : 512 <= FF / 8) by (apply Z.div_le_lower_bound; lia).
  assert (HFF8hi : FF / 8 < 17592186044416) by (apply Z.div_lt_upper_bound; lia).
  pose proof (pa_obj_img 30 ltac:(lia)) as HcellR. pose proof (pa_obj_img 0 ltac:(lia)) as HgotR. pose proof (pa_obj_img 6 ltac:(lia)) as HguR.
  pose proof (palf_sep B TLF) as HSEP. cbn [zseps zseps_from fst snd] in HSEP.
  pose proof (pa_val_range (A_OBJ 0)). pose proof (pa_val_range (A_OBJ 6)). pose proof (pa_val_range (A_OBJ 30)).
  pose proof (ff_seat_ok Ea _ _ (w_H W) mem2 39 33 512 1 FF FL HS eq_refl ltac:(vm_compute; reflexivity)
    RF' E33a ltac:(lia) ltac:(lia) ltac:(right; reflexivity) HFal2 ltac:(lia) ltac:(change (fs_frame_bytes 1) with 128; lia)
    ltac:(lia)
    ltac:(change (fs_frame_bytes 1) with 128; intros a Ha; exact (proj1 (HFpres a Ha)))
    ltac:(change (fs_frame_bytes 1 / 8) with 16; intros i Hi; exact (proj1 (HFSpres i Hi)))
    ltac:(change (fs_frame_bytes 1) with 128; exact Hflag) ltac:(change (fs_frame_bytes 1) with 128; exact Hz)) as HS3.
  pose proof (pro_frm_img_hi _ _ _ _ _ 1 fpos HARb Hfin2) as HFimg. change (fs_frame_bytes 1) with 128 in HFimg. fold FF in HFimg.
  set (Eb := havoc Ea 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)]) in HS3.
  assert (OLDb : forall m, (m < 512)%nat -> ew Eb m = ew Ea m) by (intros m Hm; subst Eb; apply YN3v.ew_havoc_old; exact Hm).
  assert (HEIb : img_env VAL A_LIM Eb) by (subst Eb; apply img_env_havoc_hi; [exact HEIa | cbv; lia]).
  assert (U512 : bv_unsigned (ew Eb 512) = FL).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 0 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. lia. }
  assert (U513 : bv_unsigned (ew Eb 513) = SB + FF / 8).
  { subst Eb. rewrite (ew_havoc_new _ 512 [Z_to_bv 64 FL; Z_to_bv 64 (SB + FF / 8)] 1 (Z_to_bv 64 0) ltac:(cbn; lia)).
    apply unsigned_lit_small. unfold SB. lia. }
  assert (U39b : bv_unsigned (ew Eb 39) = FF) by (rewrite OLDb, RF' by lia; apply unsigned_lit_small; lia).
  assert (U2b : bv_unsigned (ew Eb 2) = spZ regs) by (rewrite OLDb by lia; exact U2a).
  assert (U34b : bv_unsigned (ew Eb 34) = F) by (rewrite OLDb by lia; exact U34a).
  assert (U32b : bv_unsigned (ew Eb 32) = as_uar_cell B) by (rewrite OLDb by lia; exact U32a).
  assert (U241b : bv_unsigned (ew Eb 241) = VAL (A_OBJ 0)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U241).
  assert (U247b : bv_unsigned (ew Eb 247) = VAL (A_OBJ 6)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U247).
  assert (U271b : bv_unsigned (ew Eb 271) = VAL (A_OBJ 30)) by (rewrite OLDb by (unfold A_OBJ; lia); exact U271).
  match type of HS3 with ?A1 -> ?A2 -> _ => assert (HD1 : A1); [|assert (HD2 : A2); [|specialize (HS3 HD1 HD2)]] end.
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_fregion, fframe_region. cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1) with 128. rewrite U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    unfold off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  { lazymatch goal with |- all_disjoint ?Ey ?ry ?rsy => let rs2 := eval vm_compute in rsy in change (all_disjoint Ey ry rs2) end.
    cbn [all_disjoint]. unfold extent_disjoint, ff_sregion, ff_fregion, fshadow_region, fframe_region.
    cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val].
    change (fs_frame_bytes 1 / 8) with 16. change (fs_frame_bytes 1) with 128.
    rewrite U513, U39b, U2b, U34b, U241b, U247b, U271b, U32b.
    pose proof (Z.mul_div_le FF 8 ltac:(lia)) as Hd8a. pose proof (Z.mod_pos_bound FF 8 ltac:(lia)) as Hd8b.
    pose proof (Z.div_mod FF 8 ltac:(lia)) as Hd8c.
    unfold SB, off_img, in_app, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in *. repeat split; lia. }
  clear HS. rename HS3 into HS. norm_ss HS.
  (* run 2 (plain): the frame's slots F+184 and F+104, the fake frame's header and its shadow's poison *)
  paj_run_sh RUNP HS HJ2.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        first [ lia
        | left; lia
        | right; right; right; exists 1, fpos; split; [left; reflexivity|];
          change (frame_addr ly 1 fpos) with FF; change (fs_frame_bytes 1) with 128;
          first [ left; unfold in_zr; cbn [fst snd]; lia
          | right; unfold in_zr, shadow_addr; rewrite <- SB_SHADOW_OFF; cbn [fst snd]; change (128 / 8) with 16; lia ] ]
      | ]).
    destruct Hin'. }
  (* the size refusal: n >> 26 <> 0 goes to 0x85014; refuted by the contract's n < 2^26 *)
  assert (E11b : ew Eb 11 = Z_to_bv 64 n) by (rewrite OLDb, OLDa, (EE 11%nat 11%bv eq_refl), H11 by lia; reflexivity).
  psrr_branch_pi RUNP BR HS.
  { exfalso. rewrite branch_ne_U, U_SAlu, (U_atom Eb 11 n E11b), !U_SLit in Hc by lia. cbn [zalu_raw] in Hc.
    change (Z.land (zcanon 26) 63) with 26 in Hc. rewrite Z.shiftr_div_pow2, Z.div_small in Hc by lia.
    vm_compute in Hc. discriminate Hc. }
  (* the fake frame and its shadow become read-only (the token run keeps its windows off the shadow span);
     the runtime's GOT and uar regions are dropped *)
  pro_keep HS [0; 1; 2; 3; 4]%nat.
  pro_ro HS 0%nat. pro_ro HS 1%nat.
  pose proof pro_vals as (PV60 & PV61 & PV62 & PV63 & PV64 & PV65 & PV66 & PV69 & PV70 & PVO19 & PVO22 & PVO23 &
    PVO0 & PVO6 & PVO30 & PVLF).
  assert (RGv : rg_client fr_RG = 0xa2560 /\ rg_client_broken fr_RG = 0x5d8d60 /\ rg_send_max fr_RG = 0x5d8dc0 /\
    rg_gone fr_RG = 0x5d8de0 /\ rg_send_dead fr_RG = 0x5d8e00 /\ rg_send_eintr fr_RG = 0x5d8e20 /\
    rg_s fr_RG = 0x5d8e60 /\ rg_nout fr_RG = 0x5d8e40 /\ rg_nsrc fr_RG = 0x5d8d20 /\ rg_src fr_RG = 0x5d8d40)
    by (vm_compute; repeat split; reflexivity).
  destruct RGv as (RG1 & RG2 & RG3 & RG4 & RG5 & RG6 & RG7 & RG8 & RG9 & RG10).
  assert (HNFDv : AG_NFD = 0x5d8da0) by reflexivity.
  (* the seven global stores' regions (pr_g 60 .. 66), all in G_fr *)
  pro_addg HS HEIb 60%nat 32 4 HG_client.
  pro_addg HS HEIb 61%nat (-2024) 1 HG_cbroken.
  pro_addg HS HEIb 62%nat (-1964) 4 HG_nfd.
  pro_addg HS HEIb 63%nat (-1936) 8 HG_smax.
  pro_addg HS HEIb 64%nat (-1916) 1 HG_gone.
  pro_addg HS HEIb 65%nat (-1892) 1 HG_sdead.
  pro_addg HS HEIb 66%nat (-1868) 1 HG_seintr.
  pro_addf HS HEIb 340%nat. pro_addf HS HEIb 341%nat. pro_addf HS HEIb 342%nat. pro_addf HS HEIb 343%nat.
  pro_addf HS HEIb 344%nat. pro_addf HS HEIb 345%nat. pro_addf HS HEIb 346%nat.
  (* the journal, from here at G_fr (the donor's journal is ajournal_gx at G = [], lifted) *)
  pose proof (ajournal_gx_G_mono segs B [] G_fr _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (fun a Ha => False_ind _ (inG_nil a Ha)) (proj2 (ajournal_gx_nil segs B _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) HJ2)) as HJ3.
  lazymatch type of HS with st_ok_pi _ _ _ _ (restrict _ ?msx) =>
    assert (SHOKb : sh_ok segs Bx [] Eb (mrestrict (w_H W) (ms_mem msx))) by (unfold sh_ok; constructor) end.
  pose proof (pro_Fb (LFCX ly S W regs mem md p n pl M) HB) as (HFlo & HFsp & HFsp2 & _ & _ & _).
  change (lf_F (LFCX ly S W regs mem md p n pl M)) with F in HFlo, HFsp, HFsp2. unfold CEIL8 in HFlo.
  cbn [c_regs] in HFsp, HFsp2.
  (* run 3: the frame's slots and the seven globals, to `jal op_add` *)
  paj_run_to_tok RUNTOX HS HJ3 SHOKb Bspan AF_fr_op_add.
  { intros a (r & Hin' & Hr).
    lazymatch type of Hin' with In _ ?rs => let rs' := eval vm_compute in rs in change (In r rs') in Hin' end.
    cbn [In] in Hin'.
    repeat (destruct Hin' as [<- | Hin'];
      [ cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Hr;
        rewrite ?U2b, ?U34b, ?U39b, ?U512, ?U513, ?U241b, ?U247b, ?U271b, ?U32b in Hr;
        pro_imgh HEIb Hr;
        first [ clear - Hr; lia
        | left; split; [left; clear - Hr WS HFsp HFsp2; lia | clear - Hr; lia]
        | right; left; first [ apply HG_client; clear - Hr RG1; lia | apply HG_cbroken; clear - Hr RG2; lia
                             | apply HG_nfd; clear - Hr HNFDv; lia | apply HG_smax; clear - Hr RG3; lia
                             | apply HG_gone; clear - Hr RG4; lia | apply HG_sdead; clear - Hr RG5; lia
                             | apply HG_seintr; clear - Hr RG6; lia ]
        ]
      | ]).
    destruct Hin'. }
  (* ---- the bytes the prologue keeps from the entry to the call (pro_mid's KEEP) ---- *)
  pose proof HK as (HK1 & HK2 & HK3 & _ & _ & _).
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    rename Hx into HFr3;
    assert (K3 : forall a, 0 <= a < alloc_ceiling -> (a + 1 <= FF \/ FF + 128 <= a) ->
        (a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a) -> pro_gst_out a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem2 a) end.
  { clear - HFr3 HFr0 HEIb U2b U34b U39b U512 U513 U241b U247b U271b U32b HFlo HFsp.
    intros a Ha Hff Hsh Hgst. pose proof Hgst as (Hg1 & Hg2 & Hg3 & Hg4 & Hg5 & Hg6 & Hg7). clear Hgst.
    pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    rewrite (proj1 (pro_kept_frame _ _ W _ _ a HFr3 ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEIb Ha HFlo HFsp))).
    pose proof (proj1 (pro_kept_frame _ _ W _ _ a HFr0 ltac:(clear - Ha D1; lia)
      ltac:(pro_nwr_k HEIb Ha HFlo HFsp))) as K2.
    cbn [ms_mem mkst] in K2. exact K2. }
  assert (K1 : forall a, 0 <= a < alloc_ceiling -> aview segs (w_H W) (ms_mem ms) a = aview segs (w_H W) mem a).
  { clear - HFr HEI Usp UF HFlo HFsp.
    intros a Ha. pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    exact (proj1 (pro_kept_frame _ _ W _ _ a HFr ltac:(clear - Ha D1; lia) ltac:(pro_nwr_k HEI Ha HFlo HFsp))). }
  lazymatch goal with Hx : frame_of _ _ (mrestrict (w_H W) (ms_mem ms0)) (mrestrict (w_H W) ?m4) |- _ =>
    assert (KEEP : forall a, pro_ks (LFCX ly S W regs mem md p n pl M) a ->
        aview segs (w_H W) m4 a = aview segs (w_H W) mem a) end.
  { pose proof asan_consts as (D1 & D2 & D3 & D4 & D5).
    intros a [Ha | (p0 & n0 & Hp & Hpa)]; [|cbn [c_ly c_S] in Hp].
    - pose proof (G_obj_rng a (G_keep_obj a Ha)) as Hr. pose proof (G_keep_gst a Ha) as Hg.
      destruct (HG a (HGOBJ a (G_keep_obj a Ha))) as (Him & Hno & _).
      rewrite (K3 a ltac:(clear - Hr D1; lia) ltac:(clear - Hr HFimg; lia) ltac:(clear - Hr HF4096; lia) Hg),
        (HK3 a Him Hno (G_obj_err a (G_keep_obj a Ha))).
      exact (K1 a ltac:(clear - Hr D1; lia)).
    - destruct (al_blocks _ _ LAWS _ _ _ _ _ p0 n0 HARa Hp) as (_ & H4096 & Hbc & Happ & _).
      assert (Hp2 : In (p0, n0) (ablocks B ly S2)) by (rewrite Eab; exact Hp).
      pose proof (sep_block_frame segs B LAWS ly S2 W mem2 md2 p0 n0 1 fpos HARb Hp2 Hfin2) as Hd.
      unfold zdisjoint in Hd. cbn [fst snd] in Hd.
      change (frame_addr ly 1 fpos) with FF in Hd. change (fs_frame_bytes 1) with 128 in Hd.
      assert (Hsh : a < 2147450880 + FF / 8 \/ 2147450880 + FF / 8 + 16 <= a).
      { destruct (Z_lt_le_dec a (2147450880 + FF / 8)) as [Hl | Hl]; [left; exact Hl | right].
        destruct (Z_lt_le_dec a (2147450880 + FF / 8 + 16)) as [Hl2 | Hl2]; [|exact Hl2].
        exfalso. exact (fshadow_not_app FF 16 p0 (req_size n0) a ltac:(clear - HF4096; lia)
          ltac:(clear - HFceil D1; lia) Happ ltac:(clear - Hl Hl2; lia) Hpa). }
      rewrite (K3 a ltac:(clear - H4096 Hbc Hpa; lia) ltac:(clear - Hd Hpa; lia) Hsh
        (pro_blk_gst _ _ _ _ _ p0 n0 a HARa Hp Hpa)).
      replace a with (p0 + (a - p0)) by ring.
      rewrite (HK2 p0 n0 (a - p0) Hp ltac:(clear - Hpa; lia) (fun Hf => Hf)).
      exact (K1 (p0 + (a - p0)) ltac:(clear - H4096 Hbc Hpa D1; lia)). }
  (* ---- op_add's entry ---- *)
  pmkst HS.
  pro_rgn HS 0%nat RQ7. pro_rgn HS 1%nat RQ6. pro_rgn HS 2%nat RQ5. pro_rgn HS 3%nat RQ4.
  pro_rgn HS 4%nat RQ3. pro_rgn HS 5%nat RQ2. pro_rgn HS 6%nat RQ1. pro_rgn HS 7%nat RQS.
  pro_rgn HS 8%nat RQF. pro_rgn HS 10%nat RQV. pro_rgn HS 11%nat RQP.
  prreg HS (1%bv : bv 5) Q1. prreg HS (2%bv : bv 5) Q2. prreg HS (3%bv : bv 5) Q3. prreg HS (4%bv : bv 5) Q4.
  prreg HS (8%bv : bv 5) Q8. prreg HS (9%bv : bv 5) Q9. prreg HS (19%bv : bv 5) Q19.
  prreg HS (21%bv : bv 5) Q21. prreg HS (22%bv : bv 5) Q22. prreg HS (24%bv : bv 5) Q24.
  prreg HS (27%bv : bv 5) Q27.
  assert (EAb : forall r, (r < 32)%nat -> ew Eb r = getr regs (Z_to_bv 5 (Z.of_nat r))).
  { intros r Hr. rewrite OLDb, OLDa by (clear - Hr; lia). apply EE. rewrite Z_to_bv_unsigned. symmetry.
    apply bv_wrap_small. change (bv_modulus 5) with 32. clear - Hr; lia. }
  assert (Hfrs2' : frames S2 = [(1, fpos)]) by (rewrite Hfrs2, Hfrs; reflexivity).
  exact (pro_at_call (LFCX ly S W regs mem md p n pl M) S2 0 fpos Eb _ _ _ HB HJ3 Eab Hfrs2' Hnev2 Hbb2 HEIb
    U2b U34b U39b U512 U513 (eq_trans (OLDb 33%nat ltac:(apply Nat.ltb_lt; reflexivity)) E33a) EAb
    RQ7 RQ6 RQ5 RQ4 RQ3 RQ2 RQ1 RQS RQF RQV RQP Q1 Q2 Q3 Q4 Q8 Q9 Q19 Q21 Q22 Q24 Q27 KEEP).
Qed.
End pro.
