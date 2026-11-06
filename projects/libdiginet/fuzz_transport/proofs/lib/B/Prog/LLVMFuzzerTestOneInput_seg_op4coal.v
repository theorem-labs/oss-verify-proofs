(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 401 of its 453 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4s.v, with its module paths and module names changed; 717 of its 755 lines of code are new or changed and 415 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4coal: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk, image B).
   The segment OP4COAL of the image-B walk of fuzz_transport.asan-ubsan's LLVMFuzzerTestOneInput
   (lib/B/Prog/LLVMFuzzerTestOneInput_segs.v lc_op4coal_stmt): from the cut SYSJ (+0x1170) to the cut FIND (+0x11ec,
   turn 0 of the find loop) or the cut WANT (+0x1498, at = -1).

   The code (listing slots of lib/B/Prog/DgnTransportBList.v; offsets from transportb_text = 0x812a0):
     +0x1170 .. +0x118c  a2 = c.key (`lwu a2,28(s4)`, s4 = c = F + 32), a0 = ((a2 >> 16) | 8) & 0xff, s9 = 2^32 - 1
                         (+0x1184), a1 = 8, `bne a0,a1` to +0x11b4: falls through exactly when the key's kind is 0 or 8;
     +0x11b4 .. +0x11c0  a0 = a2 & 0xff0000, `beq a0,0x90000` to +0x1190: the kind is 9;
     +0x11c4 .. +0x11cc  a0 = the spill at 32(s1) (transportb_hi 14), a3 = g_nq (`lwu a3,-0x1a4(a0)`), `beqz a3` to
                         +0x1190;
     +0x11d0 .. +0x11e8  a4 = 0, a5 = 1, a6 = g_q (auipc / addi), a7 = 2^32 - 1, a0 = a6: the cut FIND at turn 0;
     +0x1190             `sd s5,0(s1)`: the word g_cmd + 40 serial into 0(s1), the one store of the segment;
     +0x1194 .. +0x1198  s5 = t2 (the sys flag), `beqz t2` to +0x11a4;
     +0x119c .. +0x11a0  s6 = SPEC_E_REFUSED, `j` to WANT;
     +0x11a4 .. +0x11a8  a0 = (s32) s9 = -1, `bltz` to +0x1480 (always taken; +0x11ac / +0x11b0 are not reached);
     +0x1480 .. +0x1494  a0 = (s32) g_nq, s6 = (g_nq == QUEUE_MAX) ? SPEC_E_SPACE : SPEC_OK, then WANT.
   At every arm that reaches +0x1190 the model's lc_at is Some (-1): the key is not coalescable (kind 0, 8 or 9;
   TCb.v h_coalescable_m), or g_nq = 0 (TOps.v submit_find_at's first test). The segment makes no call. The store at
   +0x1190 writes the 8 bytes [sp1, sp1 + 8) of the function's own stack window (the G journal's awr_byte, W_journalG.v
   ajournal_gx_exec); no byte lc_tag_common reads lies there (the spill slots start at sp1 + 8, the saved words at
   sp0 - 104, the frame, its shadow, the input and G below sp1), so the cut's facts move to the new memory (tc_kept,
   with LLVMFuzzerTestOneInput_st.v lc_core_kept_run). Every other step only materializes the model (W_journalG.v
   ajournal_gx_materialize) and writes a0 .. a7, s5, s6 or s9, none of which lc_tag_common reads.

   How it is proved: machine steps (YA0n.v SRr_step with YK11.v's step lemmas and YK14.v step_sd_val), each
   instruction word fetched from the code table of lib/B/Prog/DgnTransportBImg.v (transportbtbl_ok). The loads read:
   c.key from the garr8 of c that lc_tag_common states; the spill word at 32(s1) from lc_lcore's lc_spills
   (lf_spill_init's (32, transportb_hi 14)); g_nq from the world relation tw_at TMAP_B at the world tg_B2. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YA0o YP02 YN01 YN2e YI04 YO0f YK0h YK14 YK1b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v YE2k YCfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require AsanCells TransportGB YF0x.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBSyms DgnTransportBAddr DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts SubmitTag.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TOP := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TOps.
Module QF := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim.QueueFacts.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* The instruction words, from the code table                          *)
(* ------------------------------------------------------------------ *)

Ltac fw := apply transportbtbl_ok; vm_compute; reflexivity.
Lemma F_1170 : fetch_word tfibsegs (Z_to_bv 64 0x82410) = Some (Z_to_bv 32 30041603). Proof. fw. Qed.
Lemma F_1174 : fetch_word tfibsegs (Z_to_bv 64 0x82414) = Some (Z_to_bv 32 17192211). Proof. fw. Qed.
Lemma F_1178 : fetch_word tfibsegs (Z_to_bv 64 0x82418) = Some (Z_to_bv 32 8742163). Proof. fw. Qed.
Lemma F_117c : fetch_word tfibsegs (Z_to_bv 64 0x8241c) = Some (Z_to_bv 32 267744531). Proof. fw. Qed.
Lemma F_1180 : fetch_word tfibsegs (Z_to_bv 64 0x82420) = Some (Z_to_bv 32 4293920147). Proof. fw. Qed.
Lemma F_1184 : fetch_word tfibsegs (Z_to_bv 64 0x82424) = Some (Z_to_bv 32 33938579). Proof. fw. Qed.
Lemma F_1188 : fetch_word tfibsegs (Z_to_bv 64 0x82428) = Some (Z_to_bv 32 8390035). Proof. fw. Qed.
Lemma F_118c : fetch_word tfibsegs (Z_to_bv 64 0x8242c) = Some (Z_to_bv 32 45421667). Proof. fw. Qed.
Lemma F_1190 : fetch_word tfibsegs (Z_to_bv 64 0x82430) = Some (Z_to_bv 32 22327331). Proof. fw. Qed.
Lemma F_1194 : fetch_word tfibsegs (Z_to_bv 64 0x82434) = Some (Z_to_bv 32 232083). Proof. fw. Qed.
Lemma F_1198 : fetch_word tfibsegs (Z_to_bv 64 0x82438) = Some (Z_to_bv 32 231011). Proof. fw. Qed.
Lemma F_119c : fetch_word tfibsegs (Z_to_bv 64 0x8243c) = Some (Z_to_bv 32 4284484371). Proof. fw. Qed.
Lemma F_11a0 : fetch_word tfibsegs (Z_to_bv 64 0x82440) = Some (Z_to_bv 32 796917871). Proof. fw. Qed.
Lemma F_11a4 : fetch_word tfibsegs (Z_to_bv 64 0x82444) = Some (Z_to_bv 32 820507). Proof. fw. Qed.
Lemma F_11a8 : fetch_word tfibsegs (Z_to_bv 64 0x82448) = Some (Z_to_bv 32 738544739). Proof. fw. Qed.
Lemma F_11b4 : fetch_word tfibsegs (Z_to_bv 64 0x82454) = Some (Z_to_bv 32 16713015). Proof. fw. Qed.
Lemma F_11b8 : fetch_word tfibsegs (Z_to_bv 64 0x82458) = Some (Z_to_bv 32 10908979). Proof. fw. Qed.
Lemma F_11bc : fetch_word tfibsegs (Z_to_bv 64 0x8245c) = Some (Z_to_bv 32 591287). Proof. fw. Qed.
Lemma F_11c0 : fetch_word tfibsegs (Z_to_bv 64 0x82460) = Some (Z_to_bv 32 4239722723). Proof. fw. Qed.
Lemma F_11c4 : fetch_word tfibsegs (Z_to_bv 64 0x82464) = Some (Z_to_bv 32 33862915). Proof. fw. Qed.
Lemma F_11c8 : fetch_word tfibsegs (Z_to_bv 64 0x82468) = Some (Z_to_bv 32 3854919299). Proof. fw. Qed.
Lemma F_11cc : fetch_word tfibsegs (Z_to_bv 64 0x8246c) = Some (Z_to_bv 32 4228285155). Proof. fw. Qed.
Lemma F_11d0 : fetch_word tfibsegs (Z_to_bv 64 0x82470) = Some (Z_to_bv 32 1811). Proof. fw. Qed.
Lemma F_11d4 : fetch_word tfibsegs (Z_to_bv 64 0x82474) = Some (Z_to_bv 32 1050515). Proof. fw. Qed.
Lemma F_11d8 : fetch_word tfibsegs (Z_to_bv 64 0x82478) = Some (Z_to_bv 32 5698839). Proof. fw. Qed.
Lemma F_11dc : fetch_word tfibsegs (Z_to_bv 64 0x8247c) = Some (Z_to_bv 32 1082460179). Proof. fw. Qed.
Lemma F_11e0 : fetch_word tfibsegs (Z_to_bv 64 0x82480) = Some (Z_to_bv 32 4293920019). Proof. fw. Qed.
Lemma F_11e4 : fetch_word tfibsegs (Z_to_bv 64 0x82484) = Some (Z_to_bv 32 33904787). Proof. fw. Qed.
Lemma F_11e8 : fetch_word tfibsegs (Z_to_bv 64 0x82488) = Some (Z_to_bv 32 525587). Proof. fw. Qed.
Lemma F_1480 : fetch_word tfibsegs (Z_to_bv 64 0x82720) = Some (Z_to_bv 32 33862915). Proof. fw. Qed.
Lemma F_1484 : fetch_word tfibsegs (Z_to_bv 64 0x82724) = Some (Z_to_bv 32 3854902531). Proof. fw. Qed.
Lemma F_1488 : fetch_word tfibsegs (Z_to_bv 64 0x82728) = Some (Z_to_bv 32 3758425363). Proof. fw. Qed.
Lemma F_148c : fetch_word tfibsegs (Z_to_bv 64 0x8272c) = Some (Z_to_bv 32 10499379). Proof. fw. Qed.
Lemma F_1490 : fetch_word tfibsegs (Z_to_bv 64 0x82730) = Some (Z_to_bv 32 4294247699). Proof. fw. Qed.
Lemma F_1494 : fetch_word tfibsegs (Z_to_bv 64 0x82734) = Some (Z_to_bv 32 4290083603). Proof. fw. Qed.

(* ------------------------------------------------------------------ *)
(* Registers and words                                                 *)
(* ------------------------------------------------------------------ *)

Lemma ifx0f : forall (rd z : bv 5) (A B : bvmap 5 word), bv_eqb rd z = false -> (if bv_eqb rd z then A else B) = B.
Proof. intros rd z A B0 H. rewrite H. reflexivity. Qed.

Lemma gu_eq : forall R a v, 0 < a < 32 -> YK11.getr (YK11.regupd R (Z_to_bv 5 a) v) (Z_to_bv 5 a) = v.
Proof.
  intros R a v Ha. apply YK11.getr_same. intros E.
  assert (H : bv_unsigned (Z_to_bv 5 a) = 0) by (rewrite E; reflexivity).
  rewrite Z_to_bv_unsigned in H. unfold bv_wrap in H. change (bv_modulus 5) with 32 in H.
  rewrite Z.mod_small in H by lia. lia.
Qed.

Lemma gu_ne : forall R a b v, 0 <= a < 32 -> 0 <= b < 32 -> a <> b ->
  YK11.getr (YK11.regupd R (Z_to_bv 5 a) v) (Z_to_bv 5 b) = YK11.getr R (Z_to_bv 5 b).
Proof.
  intros R a b v Ha Hb Hab. apply YK11.getr_other. intros E. apply (f_equal bv_unsigned) in E.
  rewrite !Z_to_bv_unsigned in E. unfold bv_wrap in E. change (bv_modulus 5) with 32 in E.
  rewrite !Z.mod_small in E by lia. lia.
Qed.

Lemma g0 : forall R, YK11.getr R (Z_to_bv 5 0) = Z_to_bv 64 0.
Proof. intros R. reflexivity. Qed.

Lemma u64 : forall z, 0 <= z < 2 ^ 64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof.
  intros z Hz. rewrite Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  apply Z.mod_small. lia.
Qed.

Lemma vaddi : forall x i, v_addi (Z_to_bv 64 x) i = Z_to_bv 64 (x + i).
Proof.
  intros x i. unfold v_addi. apply bv_eq. rewrite !Z_to_bv_unsigned. unfold bv_wrap.
  rewrite Z.add_mod_idemp_l by (change (bv_modulus 64) with (2 ^ 64); lia). reflexivity.
Qed.

Lemma vsrli : forall x s, 0 <= x < 2 ^ 64 -> v_srli (Z_to_bv 64 x) s = Z_to_bv 64 (Z.shiftr x s).
Proof. intros x s Hx. unfold v_srli. rewrite u64 by lia. reflexivity. Qed.

Lemma vori : forall x i, 0 <= x < 2 ^ 64 -> 0 <= i < 2 ^ 11 -> v_ori (Z_to_bv 64 x) i = Z_to_bv 64 (Z.lor x i).
Proof.
  intros x i Hx Hi. unfold v_ori. rewrite u64 by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small i) by lia. reflexivity.
Qed.

Lemma vandi : forall x i, 0 <= x < 2 ^ 64 -> 0 <= i < 2 ^ 11 -> v_andi (Z_to_bv 64 x) i = Z_to_bv 64 (Z.land x i).
Proof.
  intros x i Hx Hi. unfold v_andi. rewrite u64 by lia. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small i) by lia. reflexivity.
Qed.

Lemma vand : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 ->
  v_and (Z_to_bv 64 x) (Z_to_bv 64 y) = Z_to_bv 64 (Z.land x y).
Proof. intros x y Hx Hy. unfold v_and. rewrite !u64 by lia. reflexivity. Qed.

Lemma ceq : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> c_eq (Z_to_bv 64 x) (Z_to_bv 64 y) = (x =? y).
Proof.
  intros x y Hx Hy. unfold c_eq. destruct (Z.eqb_spec x y) as [E|E].
  - subst y. apply bv_eqb_refl.
  - apply bv_eqb_neq. intros Ew. apply E. apply (f_equal bv_unsigned) in Ew. rewrite !u64 in Ew by lia. exact Ew.
Qed.

Lemma vlw : forall g, 0 <= g < 2 ^ 64 -> v_lw (Z_to_bv 64 g) = Z_to_bv 64 (bv_swrap 32 g).
Proof. intros g Hg. unfold v_lw. rewrite u64 by lia. reflexivity. Qed.

Lemma cltu0 : forall y, - 2 ^ 64 < y < 2 ^ 64 -> c_ltu (Z_to_bv 64 0) (Z_to_bv 64 y) = negb (y =? 0).
Proof.
  intros y Hy. unfold c_ltu. destruct (Z.eqb_spec y 0) as [E|E].
  - subst y. reflexivity.
  - cbn [negb]. unfold bv_ltu. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
    apply Z.ltb_lt. rewrite Zmod_0_l.
    assert (y mod 2 ^ 64 <> 0).
    { intros Hm. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [q Hq].
      assert (q = 0) by nia. subst q. lia. }
    pose proof (Z.mod_pos_bound y (2 ^ 64) ltac:(lia)). lia.
Qed.

(* (s32) of a 32-bit value: its range, and 512 only for 512 (+0x1484 .. +0x148c). *)
Lemma oc_swrap : forall g, 0 <= g < 2 ^ 32 ->
  (- 2 ^ 31 <= bv_swrap 32 g < 2 ^ 31) /\ (bv_swrap 32 g = 512 -> g = 512).
Proof.
  intros g Hg. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The one store: 8 bytes at a                                          *)
(* ------------------------------------------------------------------ *)

(* The memory after `sd` of the word v at a, as the machine step leaves it outside the hidden bytes. *)
Definition oc_mem2 (H : word -> bool) (mem : word -> option byte) (a v : Z) : word -> option byte :=
  munrestrict H mem (YK0h.wbytes (mrestrict H mem) (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v))).

(* The store changes the visible bytes [a, a + 8) only, keeps every visible byte present and every hidden byte, and
   the word at a reads v. *)
Lemma oc_st8 : forall (H : word -> bool) (mem : word -> option byte) (a v : Z),
  0 <= a -> a + 8 <= 2 ^ 64 -> 0 <= v < 2 ^ 64 ->
  (forall x, a <= x < a + 8 -> apresent H mem x) ->
  (forall x : word, ~ (a <= bv_unsigned x < a + 8) -> mrestrict H (oc_mem2 H mem a v) x = mrestrict H mem x) /\
  YK1b.mem_grows (mrestrict H mem) (mrestrict H (oc_mem2 H mem a v)) /\
  (forall x, H x = true -> oc_mem2 H mem a v x = mem x) /\
  rdword (aview tfibsegs H (oc_mem2 H mem a v)) a = Some v.
Proof.
  intros H mem a v Ha0 Ha1 Hv HP.
  assert (HL : Z.of_nat (length (word_to_le_bytes 8 (Z_to_bv 64 v))) = 8)
    by (rewrite YK0h.length_N_to_le_bytes; reflexivity).
  assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64; lia).
  assert (P : forall x : word, H x = false ->
    mrestrict H (oc_mem2 H mem a v) x =
    YK0h.wbytes (mrestrict H mem) (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v)) x).
  { intros x Hx. change (mrestrict H (oc_mem2 H mem a v) x) with (if H x then None else oc_mem2 H mem a v x).
    rewrite Hx. unfold oc_mem2, munrestrict. rewrite Hx. reflexivity. }
  split; [|split; [|split]].
  - intros x Hx. destruct (H x) eqn:E.
    + unfold mrestrict. rewrite E. reflexivity.
    + rewrite (P x E). destruct (Z_lt_le_dec (bv_unsigned x) a) as [Hlt | Hge].
      * rewrite YK0h.wbytes_below by (rewrite ?Ua, ?HL; lia). reflexivity.
      * rewrite YK0h.wbytes_above by (rewrite ?Ua, ?HL; lia). reflexivity.
  - intros x Hx. destruct (H x) eqn:E.
    + exfalso. apply Hx. unfold mrestrict. rewrite E. reflexivity.
    + rewrite (P x E). apply (YK1b.wbytes_grows _ _ _ x). exact Hx.
  - intros x Hx. unfold oc_mem2, munrestrict. rewrite Hx. reflexivity.
  - apply YF0x.val_mem_rdword; [exact Hv|]. intros k Hk.
    destruct (HP (a + Z.of_nat k) ltac:(lia)) as [Hh _].
    transitivity (mbyte tfibsegs (YK0h.wbytes (mrestrict H mem) (Z_to_bv 64 a) (word_to_le_bytes 8 (Z_to_bv 64 v)))
      (a + Z.of_nat k)).
    { unfold mbyte. rewrite (P _ Hh). reflexivity. }
    rewrite (YN2e.wbytes_mbyte_in tfibsegs) by (rewrite ?HL; lia).
    replace (Z.to_nat (a + Z.of_nat k - a)) with k by lia.
    apply YN2e.word_to_le_bytes_nth; [exact Hk | exact Hv].
Qed.

(* The state after a step: the machine's view of the stepped memory, outside the hidden bytes. *)
Lemma oc_unr `{fx : YK11.FPState} : forall (H : word -> bool) (regs0 : bvmap 5 word) (pc0 : word)
    (full rom0 : word -> option byte) (regs : bvmap 5 word) (pc : word) (m rom : word -> option byte),
  unrestrict H (ms_mem (YK11.mkst regs0 pc0 full rom0)) (YK11.mkst regs pc m rom) =
  YK11.mkst regs pc (munrestrict H full m) rom.
Proof. intros. reflexivity. Qed.

(* ------------------------------------------------------------------ *)
(* The key's kind                                                      *)
(* ------------------------------------------------------------------ *)

(* Taken from lib/Prog/T/LLVMFuzzerTestOneInput_op4t2.v (the plain image's walk of the same code). *)
Lemma oc_mask16 : forall x m, 0 <= x -> 0 <= m ->
  Z.land x (Z.shiftl m 16) = Z.shiftl (Z.land (Z.shiftr x 16) m) 16.
Proof.
  intros x m Hx Hm. rewrite Z.shiftl_land.
  apply Z.bits_inj'. intros i Hi. rewrite !Z.land_spec.
  destruct (Z.lt_ge_cases i 16) as [H|H].
  - rewrite (Z.shiftl_spec_low m 16 i) by lia. rewrite !andb_false_r. reflexivity.
  - rewrite (Z.shiftl_spec (Z.shiftr x 16) 16 i) by lia. rewrite Z.shiftr_spec by lia.
    replace (i - 16 + 16) with i by lia. reflexivity.
Qed.

(* The kind byte of a key below 2^32: k = (key >> 16) mod 256. *)
Definition oc_kind (key : Z) : Z := Z.shiftr key 16 mod 256.

Lemma oc_kind_range : forall key, 0 <= key -> 0 <= oc_kind key < 256.
Proof. intros key Hk. unfold oc_kind. apply Z.mod_pos_bound. lia. Qed.

(* +0x1174 .. +0x117c: ((key >> 16) | 8) & 0xff = kind | 8. *)
Lemma oc_lor8 : forall key, 0 <= key -> Z.land (Z.lor (Z.shiftr key 16) 8) 255 = Z.lor (oc_kind key) 8.
Proof.
  intros key Hk. rewrite Z.land_lor_distr_l. change (Z.land 8 255) with 8. f_equal.
  unfold oc_kind. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma oc_lor8_cases_b : forallb (fun k => Bool.eqb (Z.lor k 8 =? 8) ((k =? 0) || (k =? 8)))
  (map Z.of_nat (seq 0 256)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma oc_lor8_cases : forall k, 0 <= k < 256 -> (Z.lor k 8 =? 8) = ((k =? 0) || (k =? 8)).
Proof.
  intros k Hk. pose proof oc_lor8_cases_b as H. rewrite forallb_forall in H.
  specialize (H k ltac:(apply in_map_iff; exists (Z.to_nat k); split; [lia | apply in_seq; lia])).
  apply Bool.eqb_prop in H. exact H.
Qed.

(* +0x11b4 .. +0x11b8: key & 0xff0000 = kind << 16. *)
Lemma oc_ff0000 : forall key, 0 <= key -> Z.land key 16711680 = oc_kind key * 65536.
Proof.
  intros key Hk. change 16711680 with (Z.shiftl 255 16). rewrite (oc_mask16 key 255) by lia.
  rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 16) with 65536. f_equal.
  unfold oc_kind. change 255 with (Z.ones 8). rewrite Z.land_ones by lia. reflexivity.
Qed.

Lemma oc_coal : forall key, TC.h_coalescable_m key =
  if (oc_kind key =? 0) || (oc_kind key =? 8) || (oc_kind key =? 9) then 0 else 1.
Proof.
  intros key. unfold TC.h_coalescable_m, TC.SPEC_KEY_INPUT, TC.SPEC_KEY_KEEPALIVE.
  change (Z.shiftr key 16 mod 2 ^ 8) with (oc_kind key).
  destruct (oc_kind key =? 0), (oc_kind key =? 8), (oc_kind key =? 9); reflexivity.
Qed.

(* ------------------------------------------------------------------ *)
(* The model's values at the cut                                       *)
(* ------------------------------------------------------------------ *)

(* The key is below 2 ^ 32 and the cursor after the key and display bytes is a cursor of D. *)
Lemma oc_kd : forall D c, QF.fuzz_in_ok D c ->
  0 <= sv_key (lc_sub_kd D (lc_oc D c)) < 2 ^ 32 /\ QF.fuzz_in_ok D (sv_c (lc_sub_kd D (lc_oc D c))).
Proof.
  intros D c Hc. unfold lc_oc, lc_sub_kd.
  destruct (QF.fuzz_u8_ok D c Hc) as (c1 & v1 & E1 & Hc1 & _). rewrite E1. cbn [fst].
  destruct (QF.fuzz_u8_ok D c1 Hc1) as (c2 & kb & E2 & Hc2 & Hkb). rewrite E2.
  destruct (QF.fuzz_u8_ok D c2 Hc2) as (c3 & ab & E3 & Hc3 & Hab). rewrite E3.
  destruct (QF.fuzz_u8_ok D c3 Hc3) as (c4 & db & E4 & Hc4 & _). rewrite E4.
  cbn [sv_key sv_c]. split; [apply SubmitTag.key_range; lia | exact Hc4].
Qed.

(* c's bytes are 24: the tag and serial bytes, the n taken bytes and 21 - n zeros. *)
Lemma oc_cbytes_len : forall D B1 c, QF.fuzz_in_ok D c -> length (tg_cbytes (lc_tag_vals D B1 c)) = 24%nat.
Proof.
  intros D B1 c Hc. unfold lc_tag_vals.
  destruct (QF.fuzz_u8_ok D c Hc) as (c4 & lb & E4 & Hc4 & Hlb). rewrite E4.
  pose proof (Z.mod_pos_bound lb 22 ltac:(lia)) as Hm.
  destruct (QF.fuzz_take_ok D c4 (lb mod 22 + 3 - 3) Hc4 ltac:(lia))
    as (c5 & off & n & E5 & _ & Hn & Hoff & Hsum & _).
  rewrite E5. cbn [tg_cbytes].
  rewrite !length_app, repeat_length, TWL.length_sub by lia. cbn [length]. lia.
Qed.

(* `j` as the decoder writes it: Jal x0 with x0 as a decoded register literal (YK11.v step_jal_x0 names the literal 0). *)
Lemma oc_step_jal0 `{fx : YK11.FPState} : forall segs regs pc mem rom w rd (imm : bv 21),
  fetch_word segs pc = Some w -> is_ecall w = false -> decode_any w = Some (Jal rd imm, 4%Z) -> bv_unsigned rd = 0 ->
  RiscvSemantics.step segs (YK11.mkst regs pc mem rom) = MachineOk (YK11.mkst regs (btgt pc (bv_signed imm)) mem rom).
Proof.
  intros segs regs pc mem rom w rd imm Hf He Hd Hr.
  apply (YK11.step_jal_x0 segs regs pc mem rom w imm Hf He).
  rewrite Hd. repeat f_equal. apply bv_eq. rewrite Hr. reflexivity.
Qed.

Section s. Context {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Variable XL : Z -> Z.
Variables RLO RHI : Z.
Local Abbreviation segs := tfibsegs.

(* Registers named by a literal of the decoder (BV 5 k p) or of the cut (BV 5 k I), written Z_to_bv 5 k. *)
Ltac nreg := repeat match goal with
  | |- context [@BV 5%N ?k ?p] =>
      replace (@BV 5%N k p) with (Z_to_bv 5 k) by (apply bv_eq; reflexivity)
  end.
Ltac nreg_in H := repeat match type of H with
  | context [@BV 5%N ?k ?p] =>
      replace (@BV 5%N k p) with (Z_to_bv 5 k) in H by (apply bv_eq; reflexivity)
  end.

(* The cut's common facts at a materialized model. *)
Lemma tc_mat : forall cx op B1 ly S (W : world segs) R mem md md2 e,
  AR_laws segs B ->
  lc_tag_common B MT cx op B1 ly S W R mem md e -> same_but_materialized md md2 ->
  lc_tag_common B MT cx op B1 ly S W R mem md2 e.
Proof.
  intros cx op B1 ly S W R mem md md2 e LAWS H Hs.
  rewrite (YA0o.same_but_materialized_wvb md md2 Hs).
  destruct H as (H1 & ((HJ & Hc) & Hl) & H3).
  refine (conj H1 (conj (conj (conj _ Hc) Hl) H3)).
  eapply ajournal_gx_materialize; first [exact LAWS | exact transportb_segs_low | exact HJ].
Qed.

(* The registers lc_tag_common reads: lc_core's sp, gp, tp, s0, s1; lc_fr's s2, s10; lc_lcore's s3; s4, s7, s8, s11.
   oc_kept2 adds t2 and s5, which the cuts SYSJ and FIND fix. *)
Definition oc_kept : list Z := [2; 3; 4; 8; 9; 18; 19; 20; 23; 24; 26; 27].
Definition oc_kept2 : list Z := 7 :: 21 :: oc_kept.

Lemma tc_regs : forall cx op B1 ly S (W : world segs) R R2 mem md e,
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  (forall k, In k oc_kept -> YK11.getr R2 (Z_to_bv 5 k) = YK11.getr R (Z_to_bv 5 k)) ->
  lc_tag_common B MT cx op B1 ly S W R2 mem md e.
Proof.
  intros cx op B1 ly S W R R2 mem md e H HA.
  unfold lc_tag_common, lc_lcore, lc_core, lc_fr in *. nreg_in H. nreg.
  rewrite (HA 2), (HA 3), (HA 4), (HA 8), (HA 9), (HA 18), (HA 19), (HA 20), (HA 23), (HA 24), (HA 26), (HA 27)
    by (cbn [oc_kept In]; tauto).
  exact H.
Qed.

(* Registers and bounds a cut fixes. *)
Lemma oc_r : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_base B MT XL RLO RHI cx -> lc_tag_common B MT cx op B1 ly S W R mem md e ->
  YK11.getr R (Z_to_bv 5 20) = Z_to_bv 64 (lc_F cx + 32) /\ YK11.getr R (Z_to_bv 5 9) = Z_to_bv 64 (lc_sp1 cx) /\
  4096 <= lc_F cx /\ lc_F cx + 256 <= 2 ^ 47 /\ 0 <= lc_sp1 cx /\ lc_sp1 cx + 192 <= 2 ^ 47.
Proof.
  intros cx op B1 ly S W R mem md e HB H.
  destruct H as (_ & (Hcore & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R20 & _).
  pose proof (lc_geom B MT XL RLO RHI cx ly S W R mem md e HB Hcore) as G.
  destruct G as [_ _ G2 G1 _ _ _ _ _].
  destruct Hcore as (_ & _ & _ & _ & _ & _ & R9 & _ & _ & Hsp & _ & _ & HF0 & _ & HF1 & _).
  nreg_in R20. nreg_in R9. unfold w64 in R20, R9.
  unfold LF_FBYTES, LF_FRAME in *.
  refine (conj R20 (conj R9 _)). lia.
Qed.

Lemma oc_nth_bu : forall (l : list byte) n, (n < length l)%nat ->
  nth n (map bv_unsigned l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  intros l n Hn. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply map_nth.
Qed.

(* +0x1170: c.key's four bytes at c + 28. *)
Lemma oc_key_rd : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_base B MT XL RLO RHI cx -> lc_tag_common B MT cx op B1 ly S W R mem md e ->
  let kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)) in
  rdn segs (mrestrict (w_H W) mem) (Z_to_bv 64 (lc_F cx + 32 + 28)) 4 = Some (Z_to_le_bytes 4 (sv_key kd)) /\
  0 <= sv_key kd < 2 ^ 32.
Proof.
  intros cx op B1 ly S W R mem md e HB H kd. subst kd.
  destruct (oc_r cx op B1 ly S W R mem md e HB H) as (_ & _ & HF0 & HF1 & _).
  destruct H as (_ & (_ & _ & _ & _ & (_ & _ & Hin & _) & _) & _ & _ & _ & _ & Hg & _).
  destruct (oc_kd (l_pl cx) (lo_c op) Hin) as (Hk & Hc3).
  set (kd := lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op))) in *.
  pose proof (oc_cbytes_len (l_pl cx) B1 (sv_c kd) Hc3) as HL.
  set (tv := lc_tag_vals (l_pl cx) B1 (sv_c kd)) in *.
  split; [|exact Hk].
  assert (Hm : forall j, (j < 4)%nat -> mbyte segs (mrestrict (w_H W) mem) (lc_F cx + 32 + 28 + Z.of_nat j) =
    Some (Z_to_bv 8 (YO0f.le_byte (sv_key kd) 4 j))).
  { intros j Hj.
    assert (Hlt : (28 + j < length (TW.zs (TOP.cmd_struct (tg_cbytes tv) (tg_len tv) (sv_display kd) (sv_key kd))))%nat)
      by (unfold TW.zs, TOP.cmd_struct; rewrite length_map, !length_app, TWL.length_put, HL; cbn [length]; lia).
    destruct (Hg (28 + j)%nat Hlt) as [Hv Hb].
    specialize (Hv 0%nat ltac:(lia)).
    replace (lc_F cx + 32 + 28 + Z.of_nat j) with (lc_F cx + 32 + Z.of_nat (28 + j) + Z.of_nat 0) by lia.
    rewrite Hv. f_equal. f_equal.
    rewrite (tw_le_byte1 _ Hb).
    unfold TW.zs, TOP.cmd_struct in *. rewrite oc_nth_bu by (rewrite length_map in Hlt; exact Hlt).
    rewrite app_nth2 by (rewrite HL; lia). rewrite HL.
    rewrite app_nth2 by (cbn [length]; lia). cbn [length].
    replace (28 + j - 24 - 4)%nat with j by lia.
    apply tw_le_byte_put. exact Hj. }
  destruct (YN01.bytes4_rdn segs (mrestrict (w_H W) mem) (lc_F cx + 32 + 28) (sv_key kd)
    ltac:(lia) ltac:(lia) Hm) as [Hr _].
  rewrite Z.mod_small in Hr by lia. exact Hr.
Qed.

(* +0x11c4 / +0x1480: the spill word at 32(s1), transportb_hi 14 (lf_spill_init). *)
Lemma oc_sp_rd : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_base B MT XL RLO RHI cx -> lc_tag_common B MT cx op B1 ly S W R mem md e ->
  rdn segs (mrestrict (w_H W) mem) (Z_to_bv 64 (lc_sp1 cx + 32)) 8 = Some (Z_to_le_bytes 8 (transportb_hi 14)).
Proof.
  intros cx op B1 ly S W R mem md e HB H.
  destruct (oc_r cx op B1 ly S W R mem md e HB H) as (_ & _ & _ & _ & Hs0 & Hs1).
  destruct H as (_ & (_ & _ & Hsp & _) & _).
  unfold lc_spills in Hsp. rewrite Forall_forall in Hsp.
  specialize (Hsp (32, transportb_hi 14) ltac:(unfold lf_spill_loop, lf_spill_init; apply in_or_app; left;
    apply in_or_app; right; cbn [In]; right; left; reflexivity)).
  cbn [fst snd] in Hsp.
  pose proof (val_mem_of_rdword _ _ _ _ _ Hsp) as Hv.
  pose proof (YN01.bytes_rdn segs (mrestrict (w_H W) mem) (lc_sp1 cx + 32) 8 (transportb_hi 14) ltac:(lia) ltac:(lia) Hv)
    as Hr.
  rewrite Z.mod_small in Hr by (vm_compute; split; congruence).
  exact Hr.
Qed.

(* +0x11c8 / +0x1484: g_nq's four bytes, from the world relation at tg_B2. *)
Lemma oc_nq_rd : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  let tv := lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) in
  rdn segs (mrestrict (w_H W) mem) (Z_to_bv 64 TB_g_nq) 4 = Some (Z_to_le_bytes 4 (TW.g_nq (tg_B2 tv))) /\
  0 <= TW.g_nq (tg_B2 tv) < 2 ^ 32.
Proof.
  intros cx op B1 ly S W R mem md e H tv.
  destruct H as (_ & _ & _ & _ & _ & Htw & _). fold tv in Htw. unfold lc_tw in Htw.
  pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_B (tg_B2 tv) TW.OFF_g_nq TB_g_nq TW.SZ_g_nq 0 4
    TMAP_B_ok Htw TMAP_B_g_nq ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)) as Hv.
  rewrite !Z.add_0_r in Hv.
  pose proof (TWL.u_at_range (tg_B2 tv) TW.OFF_g_nq 4) as Hg. change (8 * Z.of_nat 4) with 32 in Hg.
  destruct (YN01.bytes4_rdn segs (mrestrict (w_H W) mem) TB_g_nq (TW.u_at (tg_B2 tv) TW.OFF_g_nq 4)
    ltac:(unfold TB_g_nq; lia) ltac:(unfold TB_g_nq; lia) Hv) as [Hr _].
  rewrite Z.mod_small in Hr by lia.
  unfold TW.g_nq. split; [exact Hr | exact Hg].
Qed.

(* The cut's common facts move to a memory that differs from the cut's only in the 8 bytes [sp1, sp1 + 8) and keeps
   every present byte present, with the G journal at that memory: the spill slots start at sp1 + 8, the saved words
   at sp0 - 104; the frame (c, its last word), its shadow, the input and G lie below sp1. *)
Lemma tc_kept : forall cx op B1 ly S (W : world segs) R mem md e mem2 md2,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx ->
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
    (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S W mem2 md2 e ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx <= a < lc_sp1 cx + 8) ->
     aview segs (w_H W) mem2 a = aview segs (w_H W) mem a) ->
  (forall a, apresent (w_H W) mem a -> apresent (w_H W) mem2 a) ->
  lc_tag_common B MT cx op B1 ly S W R mem2 md2 e.
Proof.
  intros cx op B1 ly S W R mem md e mem2 md2 LAWS HB HT HJ2 KA GR.
  destruct HT as (Hopc & (Hcore & Hfr & Hsp & Hfsh & Hopok & He & Hmt & R19) & Hob & Hraw & Hser & Htw & Hc &
    H24 & H16 & H8 & H64 & R24 & R27 & R20 & R23).
  pose proof (lc_geom B MT XL RLO RHI cx ly S W R mem md e HB Hcore) as G.
  destruct G as [HARg Hsp0al Hstk Hsp1c HFaddr HFin Hn HINg HLIVEg].
  pose proof Hcore as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _ & _ & HF4096 & _ & HFceil & _).
  destruct Hstk as (Hceil & Hslo & Hshi & H47).
  pose proof asan_consts as ((CVlo & CVhi) & _).
  change (2 ^ 47) with 140737488355328 in H47.
  unfold LF_FRAME, LF_FBYTES in Hsp1, HFceil.
  assert (KB8 : forall a, 0 <= a < lc_sp1 cx -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KA; lia).
  assert (KA8 : forall a, lc_sp1 cx + 8 <= a < 2 ^ 47 -> aview segs (w_H W) mem2 a = aview segs (w_H W) mem a)
    by (intros a Ha; apply KA; lia).
  assert (KIN : forall i, 0 <= i < l_n cx ->
    aview segs (w_H W) mem2 (l_p cx + i) = aview segs (w_H W) mem (l_p cx + i)).
  { destruct (Z_lt_le_dec 0 (l_n cx)) as [Hn0 | Hn0].
    - pose proof (HINg Hn0) as InP.
      pose proof (req_size_pos (l_n cx) ltac:(lia)) as (Hq1 & Hq2).
      destruct (al_blocks _ _ LAWS ly S W mem md (l_p cx) (l_n cx) HARg InP) as (_ & H4096 & Hbc & _).
      intros i Hi. apply KB8. lia.
    - intros i Hi. lia. }
  pose proof Hopok as (_ & _ & Hin & _).
  destruct (oc_kd (l_pl cx) (lo_c op) Hin) as (_ & Hc3).
  pose proof (oc_cbytes_len (l_pl cx) B1 _ Hc3) as HL.
  split; [exact Hopc|].
  split.
  { split.
    { apply (lc_core_kept_run B MT XL RLO RHI cx ly S W R mem md e ly S W R mem2 md2 e HB Hcore HJ2 eq_refl
        (Permutation_refl _)).
      - intros r _. reflexivity.
      - intros a Ha. apply KA8. lia.
      - exact KIN.
      - intros a Ha. unfold LF_FBYTES in Ha. apply KB8. lia.
      - intros a _ Hp. exact (GR a Hp). }
    split; [exact Hfr|].
    split.
    { unfold lc_spills in *. rewrite Forall_forall in Hsp |- *. intros o Ho.
      pose proof (proj1 (Forall_forall _ _) (lf_spill_vals (lc_F cx) ltac:(lia) ltac:(unfold LF_FBYTES; lia)) o Ho)
        as (_ & _ & Ho8 & Ho192).
      rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp1 cx + fst o))
        by (intros k Hk; apply KA8; lia).
      exact (Hsp o Ho). }
    split.
    { apply (lc_fsh_kept cx (aview segs (w_H W) mem)); [|exact Hfsh].
      intros a Ha. unfold lc_SH, SHADOW_OFF in Ha. pose proof (Z.div_pos (lc_F cx) 8 ltac:(lia)).
      apply KB8. split; [lia|].
      assert (lc_F cx / 8 <= lc_F cx) by (apply Z.div_le_upper_bound; lia). lia. }
    split; [exact Hopok|]. split; [exact He|]. split; [exact Hmt | exact R19]. }
  split; [exact Hob|]. split; [exact Hraw|]. split; [exact Hser|].
  split.
  { unfold lc_tw in *. apply (tw_kept_GB (aview segs (w_H W) mem)); [exact Htw|].
    intros b n i Hin' Hi. pose proof (TG.G_HARNESS_B_in_hull (b, n) Hin') as Hh. cbn [fst snd] in Hh.
    unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. apply KB8. lia. }
  split.
  { apply (lc_garr8_kept (w_H W) (w_H W) mem mem2 (lc_F cx + 32) _); [|exact Hc].
    intros j Hj. unfold TW.zs, TOP.cmd_struct in Hj. rewrite length_map, !length_app, TWL.length_put, HL in Hj.
    cbn [length] in Hj. apply KB8. lia. }
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp1 cx + 24))
      by (intros k Hk; apply KA8; lia). exact H24. }
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp1 cx + 16))
      by (intros k Hk; apply KA8; lia). exact H16. }
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp1 cx + 8))
      by (intros k Hk; apply KA8; lia). exact H8. }
  split.
  { rewrite (rdword_ext (aview segs (w_H W) mem) (aview segs (w_H W) mem2) (lc_sp1 cx + 64))
      by (intros k Hk; apply KA8; lia). exact H64. }
  split; [exact R24|]. split; [exact R27|]. split; [exact R20 | exact R23].
Qed.

(* Normalize the machine's pc to a literal address. *)
Ltac npc := match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ _ ?pc _ _) _) _ =>
  let v := eval vm_compute in (bv_unsigned pc) in
  replace pc with (Z_to_bv 64 v) by (apply bv_eq; vm_compute; reflexivity) end.
(* Immediates of the decoded words, as integers. *)
Ltac nimm := repeat match goal with
  | |- context [bv_signed (@BV 12%N ?k ?p)] =>
      let v := eval vm_compute in (bv_signed (@BV 12%N k p)) in change (bv_signed (@BV 12%N k p)) with v
  | |- context [bv_signed (@BV 20%N ?k ?p)] =>
      let v := eval vm_compute in (bv_signed (@BV 20%N k p)) in change (bv_signed (@BV 20%N k p)) with v
  | |- context [bv_unsigned (@BV 6%N ?k ?p)] => change (bv_unsigned (@BV 6%N k p)) with k
  end.
(* The getr of an update chain. *)
Ltac gr := repeat first [ rewrite gu_eq by lia | rewrite gu_ne by lia | rewrite g0 ].
(* A closed word equality. *)
Ltac wcl := apply bv_eq; vm_compute; reflexivity.

(* The decoder's answer for a closed word, computed once, then matched against the step lemma's pattern. *)
Ltac dec := lazymatch goal with |- decode_any ?w = _ =>
  let d := eval vm_compute in (decode_any w) in
  transitivity d; [vm_compute; reflexivity | reflexivity] end.

(* One machine step: the step lemma L at the fetch lemma F; SIDE closes the load's read goals or the branch's
   condition. The cut's common facts (the hypothesis HT) follow the model the step materializes (tc_mat). *)
Ltac stp L F SIDE :=
  npc;
  eapply (SRr_step segs transportb_wx);
  [ reflexivity
  | rewrite YA0o.restrict_mkst_fx; etransitivity;
    [ eapply L; [exact F | reflexivity | dec | SIDE .. ]
    | rewrite ?ifx0f by reflexivity; reflexivity ]
  | let m := fresh "md" in let Hs := fresh "Hs" in intros m Hs; rewrite YA0o.unrestrict_mkst_mrestrict; nreg;
    match goal with
    | LW : AR_laws _ _, HT0 : lc_tag_common _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        let H' := fresh "HT" in pose proof (tc_mat _ _ _ _ _ _ _ _ _ m _ LW HT0 Hs) as H'; clear HT0 Hs; rename H' into HT
    end ].

(* +0x1190: `sd s5,0(s1)`, the word v (s5) into [sp1, sp1 + 8), a byte range of the function's own stack window; the
   cut's facts move to the stored memory (tc_kept) and the word at sp1 reads v. *)
Lemma oc_sd : forall cx op B1 ly S (W : world segs) R mem md e v (Q : world segs -> config -> Prop),
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS_B -> lc_base B MT XL RLO RHI cx ->
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  YK11.getr R (Z_to_bv 5 21) = Z_to_bv 64 v -> 0 <= v < 2 ^ 64 ->
  (forall mem2 md2, lc_tag_common B MT cx op B1 ly S W R mem2 md2 e ->
     rdword (aview segs (w_H W) mem2) (lc_sp1 cx) = Some v ->
     SRr segs W (mkCfg (@YK11.mkst (l_fx cx) R (Z_to_bv 64 0x82434) mem2 (YK11.seg_rom segs)) md2) Q) ->
  SRr segs W (mkCfg (@YK11.mkst (l_fx cx) R (Z_to_bv 64 0x82430) mem (YK11.seg_rom segs)) md) Q.
Proof.
  intros cx op B1 ly S W R mem md e v Q LAWS HGX HB HT R21 Hv HK.
  destruct (oc_r cx op B1 ly S W R mem md e HB HT) as (_ & R9 & _ & _ & Hs0 & Hs1).
  pose proof HT as (_ & ((HJ & _ & _ & _ & _ & _ & _ & _ & _ & Hsp1 & _) & _) & _).
  unfold LF_FRAME in Hsp1.
  assert (Hpres : forall x, lc_sp1 cx <= x < lc_sp1 cx + 8 -> apresent (w_H W) mem x).
  { intros x Hx. pose proof HJ as (_ & _ & (memS & HJi & _) & _). rewrite !Z.add_0_r in HJi.
    pose proof HJi as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hp & _). apply Hp.
    unfold LLVMF_STK. lia. }
  eapply (SRr_step segs transportb_wx).
  - reflexivity.
  - rewrite YA0o.restrict_mkst_fx.
    eapply YK14.step_sd_val; [exact F_1190 | reflexivity | dec |].
    nreg. rewrite R9. nimm. rewrite (vaddi (lc_sp1 cx) 0). replace (lc_sp1 cx + 0) with (lc_sp1 cx) by lia.
    apply (YN2e.store_ok_writable segs); [lia | change (Z.of_nat 8) with 8; lia |].
    intros x Hx. apply (apresent_writable segs). apply Hpres. exact Hx.
  - intros md2 Hs. rewrite (@oc_unr (l_fx cx)). nreg. rewrite R9, R21. nimm.
    rewrite (vaddi (lc_sp1 cx) 0). replace (lc_sp1 cx + 0) with (lc_sp1 cx) by lia.
    npc.
    destruct (oc_st8 (w_H W) mem (lc_sp1 cx) v ltac:(lia) ltac:(lia) Hv Hpres) as (M1 & M2 & M3 & M4).
    assert (KA : forall a, 0 <= a < 2 ^ 64 -> ~ (lc_sp1 cx <= a < lc_sp1 cx + 8) ->
      aview segs (w_H W) (oc_mem2 (w_H W) mem (lc_sp1 cx) v) a = aview segs (w_H W) mem a).
    { intros a Ha Hn. unfold aview, mbyte. rewrite (M1 (Z_to_bv 64 a)) by (rewrite u64 by lia; exact Hn).
      reflexivity. }
    assert (GR : forall a, apresent (w_H W) mem a -> apresent (w_H W) (oc_mem2 (w_H W) mem (lc_sp1 cx) v) a)
      by (intros a Ha; exact (apresent_grows _ _ _ a M2 Ha)).
    assert (HJ2 : @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
      (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S W
      (oc_mem2 (w_H W) mem (lc_sp1 cx) v) md2 e).
    { apply (ajournal_gx_exec segs B LAWS transportb_segs_low TG.G_HARNESS_B 0 [] LLVMF_STK (lc_sp0 cx) []
        (l_ly cx) (l_S cx) (l_W cx) (l_mem cx) (l_md cx) [(LF_CID, l_fpos cx)] ly S W mem md e
        (oc_mem2 (w_H W) mem (lc_sp1 cx) v) md2 (fun a => lc_sp1 cx <= a < lc_sp1 cx + 8) HGX HJ).
      - intros x Hx. exact (M1 x Hx).
      - exact M2.
      - exact M3.
      - exact Hs.
      - intros a Ha. cbv beta in Ha. left. split; [unfold awr_byte; left; unfold LLVMF_STK; lia | lia]. }
    exact (HK _ md2 (tc_kept cx op B1 ly S W R mem md e _ md2 LAWS HB HT HJ2 KA GR) M4).
Qed.

(* +0x1190 .. +0x11b0, +0x1480 .. +0x1494: the arms that reach the join +0x1190 (lc_at = Some (-1)) end at WANT. *)
Lemma oc_nc : forall cx op B1 ly S (W : world segs) R mem md e,
  AR_laws segs B -> W_journalG.gx_ok segs B TG.G_HARNESS_B -> lc_base B MT XL RLO RHI cx ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  YK11.getr R (Z_to_bv 5 7) = Z_to_bv 64 (if lc_sys tv then 1 else 0) ->
  YK11.getr R (Z_to_bv 5 21) = Z_to_bv 64 (TB_g_cmd + 40 * tg_serial tv) ->
  YK11.getr R (Z_to_bv 5 25) = Z_to_bv 64 (2 ^ 32 - 1) ->
  lc_at tv (sv_key kd) = Some (-1) ->
  SRr segs W (lc_cfg cx 0x1190 R mem md) (fun W2 c2 => lc_st_find B MT cx op 0 W2 c2 \/ lc_st_want B MT cx op W2 c2).
Proof.
  intros cx op B1 ly S W R mem md e LAWS HGX HB D kd tv HT R7 R21 R25 HAT.
  destruct (oc_r cx op B1 ly S W R mem md e HB HT) as (_ & R9 & _ & _ & Hs0 & Hs1).
  pose proof HT as (_ & _ & _ & _ & Hser & _). fold D kd tv in Hser.
  assert (Hv : 0 <= TB_g_cmd + 40 * tg_serial tv < 2 ^ 64) by (unfold TB_g_cmd, TC.CMDS_MAX in *; lia).
  unfold lc_cfg. set (FX := l_fx cx).
  npc.
  apply (oc_sd cx op B1 ly S W R mem md e _ _ LAWS HGX HB HT R21 Hv).
  intros mem2 md2 HT2 HW0. clear HT. rename HT2 into HT.
  pose proof (oc_sp_rd cx op B1 ly S W R mem2 md2 e HB HT) as RDS.
  destruct (oc_nq_rd cx op B1 ly S W R mem2 md2 e HT) as (RDQ & Hg). fold D kd tv in RDQ, Hg.
  set (g := TW.g_nq (tg_B2 tv)) in *.
  destruct (lc_sys tv) eqn:Esys.
  - (* +0x1194 s5 = t2; +0x1198 `beqz t2` falls through: s6 = SPEC_E_REFUSED, `j` WANT *)
    stp YK11.step_addi F_1194 ltac:(idtac).
    stp YK11.step_beq_ft F_1198 ltac:(nreg; gr; rewrite R7, ?Esys; reflexivity).
    stp YK11.step_addi F_119c ltac:(idtac).
    stp oc_step_jal0 F_11a0 ltac:(reflexivity).
    npc. apply SRr_ret. right.
    eexists ly, S, _, mem2, _, e, B1, (-1).
    split; [unfold lc_cfg; reflexivity|].
    fold D kd tv g.
    split.
    { apply (tc_regs cx op B1 ly S W R _ mem2 _ e HT).
      intros k Hk. cbn [oc_kept In] in Hk. repeat (destruct Hk as [<-|Hk]; [gr; reflexivity|]). destruct Hk. }
    split; [exact HW0|].
    split; [exact HAT|].
    nreg. unfold w64. gr. nimm.
    split; [unfold lc_want; rewrite Esys; wcl|].
    split; [rewrite R25; wcl|].
    rewrite R7, ?Esys. wcl.
  - (* +0x1198 `beqz t2` taken; +0x11a4 a0 = -1, `bltz` taken; +0x1480 .. +0x1494 the g_nq test *)
    stp YK11.step_addi F_1194 ltac:(idtac).
    stp YK11.step_beq_tk F_1198 ltac:(nreg; gr; rewrite R7, ?Esys; reflexivity).
    stp YK11.step_addiw F_11a4 ltac:(idtac).
    stp YK11.step_blt_tk F_11a8 ltac:(nreg; gr; nimm; rewrite R25; vm_compute; reflexivity).
    stp YK11.step_ld F_1480 ltac:(first
      [ nreg; gr; nimm; rewrite R9, vaddi; exact RDS
      | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by (vm_compute; split; congruence);
        symmetry; apply u64; vm_compute; split; congruence ]).
    stp YK11.step_lw F_1484 ltac:(first
      [ nreg; gr; nimm; rewrite vaddi; exact RDQ
      | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
    stp YK11.step_addi F_1488 ltac:(idtac).
    stp YK11.step_sltu F_148c ltac:(idtac).
    stp YK11.step_addi F_1490 ltac:(idtac).
    stp YK11.step_andi F_1494 ltac:(idtac).
    npc. apply SRr_ret. right.
    eexists ly, S, _, mem2, _, e, B1, (-1).
    split; [unfold lc_cfg; reflexivity|].
    fold D kd tv g.
    split.
    { apply (tc_regs cx op B1 ly S W R _ mem2 _ e HT).
      intros k Hk. cbn [oc_kept In] in Hk. repeat (destruct Hk as [<-|Hk]; [gr; reflexivity|]). destruct Hk. }
    split; [exact HW0|].
    split; [exact HAT|].
    nreg. unfold w64. gr. nimm.
    split.
    { unfold lc_want. fold g. rewrite Esys. cbn [negb andb]. rewrite vlw by lia. rewrite !vaddi.
      destruct (oc_swrap g Hg) as [Hw1 Hw2].
      unfold v_sltu. rewrite cltu0 by lia.
      destruct (Z.eqb_spec g 512) as [E|E].
      - rewrite E. wcl.
      - replace (bv_swrap 32 g + -512 =? 0) with false by (symmetry; apply Z.eqb_neq; intros Hx; apply E; apply Hw2; lia).
        replace (g =? TC.QUEUE_MAX) with false by (symmetry; apply Z.eqb_neq; unfold TC.QUEUE_MAX; lia).
        wcl. }
    split; [rewrite R25; wcl|].
    rewrite R7, ?Esys. wcl.
Qed.

Lemma lc_op4coal_ok : lc_op4coal_stmt B MT XL RLO RHI.
Proof.
  unfold lc_op4coal_stmt. intros HP cx op W' c' HB HJ.
  destruct HJ as (ly' & S' & regs' & mem' & md' & e & B1 & Hc' & HT & R7 & R21). subst c'.
  pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
  pose proof (G_HARNESS_gx_ok B (lp_g_unowned _ _ _ _ _ HP)) as HGX.
  set (D := l_pl cx) in *.
  set (kd := lc_sub_kd D (lc_oc D (lo_c op))) in *.
  set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
  nreg_in R7. nreg_in R21. unfold w64 in R7, R21.
  destruct (oc_r cx op B1 ly' S' W' regs' mem' md' e HB HT) as (R20 & R9 & HF0 & HF1 & Hs0 & Hs1).
  destruct (oc_key_rd cx op B1 ly' S' W' regs' mem' md' e HB HT) as (RDK & Hkey). fold D kd in RDK, Hkey.
  pose proof (oc_sp_rd cx op B1 ly' S' W' regs' mem' md' e HB HT) as RDS.
  destruct (oc_nq_rd cx op B1 ly' S' W' regs' mem' md' e HT) as (RDQ & Hg). fold D kd tv in RDQ, Hg.
  set (key := sv_key kd) in *.
  set (g := TW.g_nq (tg_B2 tv)) in *.
  pose proof (oc_kind_range key ltac:(lia)) as Hk.
  assert (Hsh : 0 <= Z.shiftr key 16 < 2 ^ 64)
    by (rewrite Z.shiftr_div_pow2 by lia; split; [apply Z.div_pos | apply Z.div_lt_upper_bound]; lia).
  assert (Hor : 0 <= Z.lor (Z.shiftr key 16) 8 < 2 ^ 64)
    by (apply YN2e.lor_range64; lia).
  assert (Hk8 : 0 <= Z.lor (oc_kind key) 8 < 2 ^ 64)
    by (apply YN2e.lor_range64; lia).
  unfold lc_cfg. set (FX := l_fx cx).
  (* +0x1170 .. +0x1188: a2 = key, a0 = kind | 8, a1 = -1, s9 = 2^32 - 1, a1 = 8 *)
  stp YK11.step_lwu F_1170 ltac:(first
    [ nreg; rewrite R20; nimm; rewrite vaddi; exact RDK
    | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
  stp YK11.step_srli F_1174 ltac:(idtac).
  stp YK11.step_ori F_1178 ltac:(idtac).
  stp YK11.step_andi F_117c ltac:(idtac).
  stp YK11.step_addi F_1180 ltac:(idtac).
  stp YK11.step_srli F_1184 ltac:(idtac).
  stp YK11.step_addi F_1188 ltac:(idtac).
  npc.
  match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R1 := R) end.
  assert (A10 : YK11.getr R1 (Z_to_bv 5 10) = Z_to_bv 64 (Z.lor (oc_kind key) 8)).
  { unfold R1. gr. nimm. rewrite vsrli, vori, vandi by lia. rewrite oc_lor8 by lia. reflexivity. }
  assert (A11 : YK11.getr R1 (Z_to_bv 5 11) = Z_to_bv 64 8) by (unfold R1; gr; nimm; wcl).
  assert (A12 : YK11.getr R1 (Z_to_bv 5 12) = Z_to_bv 64 key) by (unfold R1; gr; reflexivity).
  assert (A25 : YK11.getr R1 (Z_to_bv 5 25) = Z_to_bv 64 (2 ^ 32 - 1)) by (unfold R1; gr; nimm; wcl).
  assert (K1 : forall k, In k oc_kept2 -> YK11.getr R1 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
  { intros k Hk'. cbn [oc_kept2 oc_kept In] in Hk'.
    repeat (destruct Hk' as [<-|Hk']; [unfold R1; gr; reflexivity|]). destruct Hk'. }
  destruct (Z.lor (oc_kind key) 8 =? 8) eqn:E8.
  - (* +0x118c `bne` falls through: the kind is 0 or 8, not coalescable *)
    stp YK11.step_bne_ft F_118c ltac:(nreg; rewrite A10, A11, ceq by lia; exact E8).
    assert (HC0 : TC.h_coalescable_m key = 0).
    { rewrite oc_coal. rewrite oc_lor8_cases in E8 by lia. rewrite E8. reflexivity. }
    npc. refine (oc_nc cx op B1 ly' S' W' R1 mem' _ e LAWS HGX HB
      (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT (fun k Hk => K1 k (or_intror (or_intror Hk)))) _ _ A25 _).
    + rewrite (K1 7) by (cbn; tauto). exact R7.
    + rewrite (K1 21) by (cbn; tauto). exact R21.
    + unfold lc_at. fold D kd tv key. rewrite HC0. reflexivity.
  - (* +0x118c `bne` taken; +0x11b4 .. +0x11bc: a0 = key & 0xff0000, a1 = 0x90000 *)
    stp YK11.step_bne_tk F_118c ltac:(nreg; rewrite A10, A11, ceq by lia; exact E8).
    stp YK11.step_lui F_11b4 ltac:(idtac).
    stp YK11.step_and F_11b8 ltac:(idtac).
    stp YK11.step_lui F_11bc ltac:(idtac).
    npc.
    match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R2 := R) end.
    assert (B10 : YK11.getr R2 (Z_to_bv 5 10) = Z_to_bv 64 (oc_kind key * 65536)).
    { unfold R2. gr. nimm. rewrite A12. unfold v_lui. change (Z.shiftl 4080 12) with 16711680.
      rewrite vand by lia. rewrite oc_ff0000 by lia. reflexivity. }
    assert (B11 : YK11.getr R2 (Z_to_bv 5 11) = Z_to_bv 64 589824) by (unfold R2; gr; nimm; wcl).
    assert (K2 : forall k, In k oc_kept2 -> YK11.getr R2 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
    { intros k Hk'. rewrite <- (K1 k Hk'). cbn [oc_kept2 oc_kept In] in Hk'.
      repeat (destruct Hk' as [<-|Hk']; [unfold R2; gr; reflexivity|]). destruct Hk'. }
    destruct (oc_kind key =? 9) eqn:E9.
    + (* +0x11c0 `beq` taken: the kind is 9, not coalescable *)
      stp YK11.step_beq_tk F_11c0 ltac:(nreg; rewrite B10, B11, ceq by lia;
        apply Z.eqb_eq; apply Z.eqb_eq in E9; lia).
      assert (HC0 : TC.h_coalescable_m key = 0).
      { rewrite oc_coal. rewrite E9. rewrite !orb_true_r. reflexivity. }
      npc. refine (oc_nc cx op B1 ly' S' W' R2 mem' _ e LAWS HGX HB
        (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT (fun k Hk => K2 k (or_intror (or_intror Hk)))) _ _ _ _).
      * rewrite (K2 7) by (cbn; tauto). exact R7.
      * rewrite (K2 21) by (cbn; tauto). exact R21.
      * unfold R2. gr. exact A25.
      * unfold lc_at. fold D kd tv key. rewrite HC0. reflexivity.
    + (* +0x11c0 `beq` falls through: coalescable; +0x11c4 a0 = the spill, +0x11c8 a3 = g_nq *)
      stp YK11.step_beq_ft F_11c0 ltac:(nreg; rewrite B10, B11, ceq by lia;
        apply Z.eqb_neq; apply Z.eqb_neq in E9; lia).
      assert (HC1 : TC.h_coalescable_m key = 1).
      { rewrite oc_coal. rewrite oc_lor8_cases in E8 by lia. rewrite E8, E9. reflexivity. }
      stp YK11.step_ld F_11c4 ltac:(first
        [ nreg; gr; nimm; rewrite (K2 9 ltac:(cbn; tauto)), R9, vaddi; exact RDS
        | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by (vm_compute; split; congruence);
          symmetry; apply u64; vm_compute; split; congruence ]).
      stp YK11.step_lwu F_11c8 ltac:(first
        [ nreg; gr; nimm; rewrite vaddi; exact RDQ
        | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
      npc.
      match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R3 := R) end.
      assert (C13 : YK11.getr R3 (Z_to_bv 5 13) = Z_to_bv 64 g) by (unfold R3; gr; reflexivity).
      assert (K3 : forall k, In k oc_kept2 -> YK11.getr R3 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
      { intros k Hk'. rewrite <- (K2 k Hk'). cbn [oc_kept2 oc_kept In] in Hk'.
        repeat (destruct Hk' as [<-|Hk']; [unfold R3; gr; reflexivity|]). destruct Hk'. }
      destruct (g =? 0) eqn:Eg.
      * (* +0x11cc `beqz a3` taken: g_nq = 0, the find answers -1 *)
        stp YK11.step_beq_tk F_11cc ltac:(nreg; rewrite C13, g0, ceq by lia; exact Eg).
        apply Z.eqb_eq in Eg.
        npc. refine (oc_nc cx op B1 ly' S' W' R3 mem' _ e LAWS HGX HB
          (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT (fun k Hk => K3 k (or_intror (or_intror Hk)))) _ _ _ _).
        -- rewrite (K3 7) by (cbn; tauto). exact R7.
        -- rewrite (K3 21) by (cbn; tauto). exact R21.
        -- unfold R3. gr. unfold R2. gr. exact A25.
        -- unfold lc_at. fold D kd tv key. rewrite HC1. cbn [negb Z.eqb]. cbn [TOP.submit_find_at].
           fold g. rewrite Eg. reflexivity.
      * (* +0x11cc `beqz a3` falls through; +0x11d0 .. +0x11e8 the find loop's entry *)
        stp YK11.step_beq_ft F_11cc ltac:(nreg; rewrite C13, g0, ceq by lia; exact Eg).
        apply Z.eqb_neq in Eg.
        stp YK11.step_addi F_11d0 ltac:(idtac).
        stp YK11.step_addi F_11d4 ltac:(idtac).
        stp YK11.step_auipc F_11d8 ltac:(idtac).
        stp YK11.step_addi F_11dc ltac:(idtac).
        stp YK11.step_addi F_11e0 ltac:(idtac).
        stp YK11.step_srli F_11e4 ltac:(idtac).
        stp YK11.step_addi F_11e8 ltac:(idtac).
        npc. apply SRr_ret. left.
        eexists ly', S', _, mem', _, e, B1.
        split; [unfold lc_cfg; reflexivity|].
        fold D kd tv key g.
        split.
        { apply (tc_regs cx op B1 ly' S' W' regs' _ mem' _ e HT).
          intros k Hk'. rewrite <- (K3 k (or_intror (or_intror Hk'))). cbn [oc_kept In] in Hk'.
          repeat (destruct Hk' as [<-|Hk']; [gr; reflexivity|]). destruct Hk'. }
        split; [fold key; rewrite HC1; discriminate|].
        split; [fold g; lia|].
        split; [unfold TC.CMDS_MAX; lia|].
        split; [rewrite Nat.sub_0_r; reflexivity|].
        nreg. unfold w64. gr. nimm.
        fold R3. fold key g. rewrite C13.
        split; [wcl|]. split; [wcl|]. split; [wcl|]. split; [wcl|].
        split; [reflexivity|].
        split; [wcl|].
        split; [unfold R3; gr; unfold R2; gr; exact A12|].
        split; [rewrite (K3 7) by (cbn; tauto); exact R7|].
        rewrite (K3 21) by (cbn; tauto). exact R21.
Qed.

End s.
