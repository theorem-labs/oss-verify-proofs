(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/CanKit.v, with its module names changed; 492 of its 559 lines of code are new or changed and 457 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SrxDeskKit.v, with its module names changed; 401 of its 453 lines of code are new or changed and 507 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/LLVMFuzzerTestOneInput_seg_op4s.v, with its module paths and module names changed; 522 of its 556 lines of code are new or changed and 419 lines of the source are left out. *)
(* LLVMFuzzerTestOneInput_seg_op4coal: proves no function (kind: segment lemma of LLVMFuzzerTestOneInput's walk).
   The segment OP4COAL of the image-A walk of fuzz_transport.asan's LLVMFuzzerTestOneInput
   (lib/A/Prog/LLVMFuzzerTestOneInput_segs.v lc_op4coal_stmt): from the cut SYSJ (+0xe6c) to the cut FIND (+0xee0,
   turn 0 of the find loop) or the cut WANT (+0x1164, at = -1).

   The code (listing slots of lib/A/Prog/DgnTransportList.v; offsets from transport_text = 0x81264):
     +0xe6c .. +0xe88  a2 = c.key (`lwu a2,28(s7)`, s7 = c = F + 32), a0 = ((a2 >> 16) | 8) & 0xff, s3 = 2^32 - 1,
                       `bne a0,8` to +0xea8: falls through exactly when the key's kind is 0 or 8;
     +0xea8 .. +0xeb4  a0 = a2 & 0xff0000, `beq a0,0x90000` to +0xe8c: the kind is 9;
     +0xeb8 .. +0xec0  a0 = the spill at sp + 24 (transport_hi 14), a3 = g_nq (`lwu a3,944(a0)`), `beqz a3` to +0xe8c;
     +0xec4 .. +0xedc  a4 = 0, a5 = 1, a6 = g_q (auipc / addi), a7 = 2^32 - 1, a0 = a6: the cut FIND at turn 0;
     +0xe8c            `beqz s4` (the sys flag) to +0xe98;
     +0xe90 .. +0xe94  s6 = SPEC_E_REFUSED, `j` to WANT;
     +0xe98 .. +0xe9c  a0 = (s32) s3 = -1, `bltz` to +0x114c (always taken);
     +0x114c .. +0x1160 a0 = (s32) g_nq, s6 = (g_nq == QUEUE_MAX) ? SPEC_E_SPACE : SPEC_OK, then WANT.
   At every arm that reaches +0xe8c the model's lc_at is Some (-1): the key is not coalescable (kind 0, 8 or 9;
   TCb.v h_coalescable_m), or g_nq = 0 (TOps.v submit_find_at's first test). The segment makes no call and no store, so
   the memory and the world are the cut's; each step only materializes the model (W_journalG.v
   ajournal_gx_materialize) and writes a0 .. a7, s3 or s6, none of which lc_tag_common reads.

   How it is proved: machine steps (YA0n.v SRr_step with YK11.v's step lemmas), each instruction word fetched from the
   code table of lib/A/Prog/DgnTransportImg.v (transporttbl_ok). The loads read: c.key from the garr8 of c that
   lc_tag_common states; the spill word at sp + 24 from lc_lcore's lc_spills (lf_spill_init's (24, transport_hi 14));
   g_nq from the world relation tw_at TMAP_A at the world tg_B2. *)
From Stdlib Require Import ZArith NArith List Lia Permutation Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK11 YK0s YK0o YK15 YK18 YP09 YM05 YK04 YA0i YA0n.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YC5d YI00 YO09.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YI16 YE00 YE01.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YA0o YP02 YN01 YN2e YI04 YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import AB1v AE2k ACfn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require AF0x TransportG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaBase DgnTransportSyms DgnTransportAddr DgnTransportCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg TWorldG TWorldA TImgA.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import DgnTransportImg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_segs.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import LLVMFuzzerTestOneInput_st.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TWorldLemmas TCb TOps.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TSim Require QueueFacts SubmitTag.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
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

Ltac fw := apply transporttbl_ok; vm_compute; reflexivity.
Lemma F_e6c : fetch_word tfibsegs (Z_to_bv 64 0x820d0) = Some (Z_to_bv 32 30139907). Proof. fw. Qed.
Lemma F_e70 : fetch_word tfibsegs (Z_to_bv 64 0x820d4) = Some (Z_to_bv 32 17192211). Proof. fw. Qed.
Lemma F_e74 : fetch_word tfibsegs (Z_to_bv 64 0x820d8) = Some (Z_to_bv 32 8742163). Proof. fw. Qed.
Lemma F_e78 : fetch_word tfibsegs (Z_to_bv 64 0x820dc) = Some (Z_to_bv 32 267744531). Proof. fw. Qed.
Lemma F_e7c : fetch_word tfibsegs (Z_to_bv 64 0x820e0) = Some (Z_to_bv 32 4293920147). Proof. fw. Qed.
Lemma F_e80 : fetch_word tfibsegs (Z_to_bv 64 0x820e4) = Some (Z_to_bv 32 33937811). Proof. fw. Qed.
Lemma F_e84 : fetch_word tfibsegs (Z_to_bv 64 0x820e8) = Some (Z_to_bv 32 8390035). Proof. fw. Qed.
Lemma F_e88 : fetch_word tfibsegs (Z_to_bv 64 0x820ec) = Some (Z_to_bv 32 45420643). Proof. fw. Qed.
Lemma F_e8c : fetch_word tfibsegs (Z_to_bv 64 0x820f0) = Some (Z_to_bv 32 656995). Proof. fw. Qed.
Lemma F_e90 : fetch_word tfibsegs (Z_to_bv 64 0x820f4) = Some (Z_to_bv 32 4284484371). Proof. fw. Qed.
Lemma F_e94 : fetch_word tfibsegs (Z_to_bv 64 0x820f8) = Some (Z_to_bv 32 754974831). Proof. fw. Qed.
Lemma F_e98 : fetch_word tfibsegs (Z_to_bv 64 0x820fc) = Some (Z_to_bv 32 623899). Proof. fw. Qed.
Lemma F_e9c : fetch_word tfibsegs (Z_to_bv 64 0x82100) = Some (Z_to_bv 32 704989283). Proof. fw. Qed.
Lemma F_ea8 : fetch_word tfibsegs (Z_to_bv 64 0x8210c) = Some (Z_to_bv 32 16713015). Proof. fw. Qed.
Lemma F_eac : fetch_word tfibsegs (Z_to_bv 64 0x82110) = Some (Z_to_bv 32 10908979). Proof. fw. Qed.
Lemma F_eb0 : fetch_word tfibsegs (Z_to_bv 64 0x82114) = Some (Z_to_bv 32 591287). Proof. fw. Qed.
Lemma F_eb4 : fetch_word tfibsegs (Z_to_bv 64 0x82118) = Some (Z_to_bv 32 4239723747). Proof. fw. Qed.
Lemma F_eb8 : fetch_word tfibsegs (Z_to_bv 64 0x8211c) = Some (Z_to_bv 32 25474307). Proof. fw. Qed.
Lemma F_ebc : fetch_word tfibsegs (Z_to_bv 64 0x82120) = Some (Z_to_bv 32 990209667). Proof. fw. Qed.
Lemma F_ec0 : fetch_word tfibsegs (Z_to_bv 64 0x82124) = Some (Z_to_bv 32 4228286179). Proof. fw. Qed.
Lemma F_ec4 : fetch_word tfibsegs (Z_to_bv 64 0x82128) = Some (Z_to_bv 32 1811). Proof. fw. Qed.
Lemma F_ec8 : fetch_word tfibsegs (Z_to_bv 64 0x8212c) = Some (Z_to_bv 32 1050515). Proof. fw. Qed.
Lemma F_ecc : fetch_word tfibsegs (Z_to_bv 64 0x82130) = Some (Z_to_bv 32 5702935). Proof. fw. Qed.
Lemma F_ed0 : fetch_word tfibsegs (Z_to_bv 64 0x82134) = Some (Z_to_bv 32 2902788115). Proof. fw. Qed.
Lemma F_ed4 : fetch_word tfibsegs (Z_to_bv 64 0x82138) = Some (Z_to_bv 32 4293920019). Proof. fw. Qed.
Lemma F_ed8 : fetch_word tfibsegs (Z_to_bv 64 0x8213c) = Some (Z_to_bv 32 33904787). Proof. fw. Qed.
Lemma F_edc : fetch_word tfibsegs (Z_to_bv 64 0x82140) = Some (Z_to_bv 32 525587). Proof. fw. Qed.
Lemma F_114c : fetch_word tfibsegs (Z_to_bv 64 0x823b0) = Some (Z_to_bv 32 25474307). Proof. fw. Qed.
Lemma F_1150 : fetch_word tfibsegs (Z_to_bv 64 0x823b4) = Some (Z_to_bv 32 990192899). Proof. fw. Qed.
Lemma F_1154 : fetch_word tfibsegs (Z_to_bv 64 0x823b8) = Some (Z_to_bv 32 3758425363). Proof. fw. Qed.
Lemma F_1158 : fetch_word tfibsegs (Z_to_bv 64 0x823bc) = Some (Z_to_bv 32 10499379). Proof. fw. Qed.
Lemma F_115c : fetch_word tfibsegs (Z_to_bv 64 0x823c0) = Some (Z_to_bv 32 4294247699). Proof. fw. Qed.
Lemma F_1160 : fetch_word tfibsegs (Z_to_bv 64 0x823c4) = Some (Z_to_bv 32 4290083603). Proof. fw. Qed.

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

(* (s32) of a 32-bit value: its range, and 512 only for 512 (+0x1150 .. +0x1158). *)
Lemma oc_swrap : forall g, 0 <= g < 2 ^ 32 ->
  (- 2 ^ 31 <= bv_swrap 32 g < 2 ^ 31) /\ (bv_swrap 32 g = 512 -> g = 512).
Proof.
  intros g Hg. unfold bv_swrap, bv_wrap.
  change (bv_half_modulus 32) with 2147483648. change (bv_modulus 32) with 4294967296.
  Z.div_mod_to_equations. lia.
Qed.

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

(* +0xe70 .. +0xe78: ((key >> 16) | 8) & 0xff = kind | 8. *)
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

(* +0xea8 .. +0xeac: key & 0xff0000 = kind << 16. *)
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
Local Abbreviation tfib_sink_head := AE2k.tfib_sink_head.
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
  eapply ajournal_gx_materialize; first [exact LAWS | exact transport_segs_low | exact HJ].
Qed.

(* The registers lc_tag_common reads (lc_core: sp, gp, tp, s0, s1; lc_fr: s2, s10; s5; s7 .. s9, s11), with t2 and s4,
   which the cuts SYSJ, FIND and WANT fix. *)
Definition oc_kept : list Z := [2; 3; 4; 7; 8; 9; 18; 20; 21; 23; 24; 25; 26; 27].

Lemma tc_regs : forall cx op B1 ly S (W : world segs) R R2 mem md e,
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  (forall k, In k oc_kept -> YK11.getr R2 (Z_to_bv 5 k) = YK11.getr R (Z_to_bv 5 k)) ->
  lc_tag_common B MT cx op B1 ly S W R2 mem md e.
Proof.
  intros cx op B1 ly S W R R2 mem md e H HA.
  unfold lc_tag_common, lc_lcore, lc_core, lc_fr in *. nreg_in H. nreg.
  rewrite (HA 2), (HA 3), (HA 4), (HA 8), (HA 9), (HA 18), (HA 21), (HA 23), (HA 24), (HA 25), (HA 26), (HA 27)
    by (cbn [oc_kept In]; tauto).
  exact H.
Qed.

(* Registers and bounds a cut fixes. *)
Lemma oc_r : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_base B MT XL RLO RHI cx -> lc_tag_common B MT cx op B1 ly S W R mem md e ->
  YK11.getr R (Z_to_bv 5 23) = Z_to_bv 64 (lc_F cx + 32) /\ YK11.getr R (Z_to_bv 5 9) = Z_to_bv 64 (lc_sp1 cx) /\
  4096 <= lc_F cx /\ lc_F cx + 256 <= 2 ^ 47 /\ 0 <= lc_sp1 cx /\ lc_sp1 cx + 192 <= 2 ^ 47.
Proof.
  intros cx op B1 ly S W R mem md e HB H.
  destruct H as (_ & (Hcore & _) & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & R23).
  pose proof (lc_geom B MT XL RLO RHI cx ly S W R mem md e HB Hcore) as G.
  destruct G as [_ _ G2 G1 _ _ _ _ _].
  destruct Hcore as (_ & _ & _ & _ & _ & _ & R9 & _ & _ & Hsp & _ & _ & HF0 & _ & HF1 & _).
  nreg_in R23. nreg_in R9. unfold w64 in R23, R9.
  unfold LF_FBYTES, LF_FRAME in *. unfold alloc_ceiling in *.
  refine (conj R23 (conj R9 _)). lia.
Qed.

Lemma oc_nth_bu : forall (l : list byte) n, (n < length l)%nat ->
  nth n (map bv_unsigned l) 0 = bv_unsigned (nth n l (Z_to_bv 8 0)).
Proof.
  intros l n Hn. rewrite (nth_indep _ 0 (bv_unsigned (Z_to_bv 8 0))) by (rewrite length_map; lia).
  apply map_nth.
Qed.

(* +0xe6c: c.key's four bytes at c + 28. *)
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

(* +0xeb8 / +0x114c: the spill word at sp + 24, transport_hi 14 (lf_spill_init). *)
Lemma oc_sp_rd : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_base B MT XL RLO RHI cx -> lc_tag_common B MT cx op B1 ly S W R mem md e ->
  rdn segs (mrestrict (w_H W) mem) (Z_to_bv 64 (lc_sp1 cx + 24)) 8 = Some (Z_to_le_bytes 8 (transport_hi 14)).
Proof.
  intros cx op B1 ly S W R mem md e HB H.
  destruct (oc_r cx op B1 ly S W R mem md e HB H) as (_ & _ & _ & _ & Hs0 & Hs1).
  destruct H as (_ & (_ & _ & Hsp & _) & _).
  unfold lc_spills in Hsp. rewrite Forall_forall in Hsp.
  specialize (Hsp (24, transport_hi 14) ltac:(unfold lf_spill_loop, lf_spill_init; apply in_or_app; left;
    apply in_or_app; right; cbn [In]; right; left; reflexivity)).
  cbn [fst snd] in Hsp.
  pose proof (val_mem_of_rdword _ _ _ _ _ Hsp) as Hv.
  pose proof (YN01.bytes_rdn segs (mrestrict (w_H W) mem) (lc_sp1 cx + 24) 8 (transport_hi 14) ltac:(lia) ltac:(lia) Hv)
    as Hr.
  rewrite Z.mod_small in Hr by (vm_compute; split; congruence).
  exact Hr.
Qed.

(* +0xebc / +0x1150: g_nq's four bytes, from the world relation at tg_B2. *)
Lemma oc_nq_rd : forall cx op B1 ly S (W : world segs) R mem md e,
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  let tv := lc_tag_vals (l_pl cx) B1 (sv_c (lc_sub_kd (l_pl cx) (lc_oc (l_pl cx) (lo_c op)))) in
  rdn segs (mrestrict (w_H W) mem) (Z_to_bv 64 TA_g_nq) 4 = Some (Z_to_le_bytes 4 (TW.g_nq (tg_B2 tv))) /\
  0 <= TW.g_nq (tg_B2 tv) < 2 ^ 32.
Proof.
  intros cx op B1 ly S W R mem md e H tv.
  destruct H as (_ & _ & _ & _ & _ & Htw & _). fold tv in Htw. unfold lc_tw in Htw.
  pose proof (tw_read_val segs (mrestrict (w_H W) mem) TMAP_A (tg_B2 tv) TW.OFF_g_nq TA_g_nq TW.SZ_g_nq 0 4
    TMAP_A_ok Htw TMAP_A_g_nq ltac:(lia) ltac:(unfold TW.SZ_g_nq; lia)) as Hv.
  rewrite !Z.add_0_r in Hv.
  pose proof (TWL.u_at_range (tg_B2 tv) TW.OFF_g_nq 4) as Hg. change (8 * Z.of_nat 4) with 32 in Hg.
  destruct (YN01.bytes4_rdn segs (mrestrict (w_H W) mem) TA_g_nq (TW.u_at (tg_B2 tv) TW.OFF_g_nq 4)
    ltac:(unfold TA_g_nq; lia) ltac:(unfold TA_g_nq; lia) Hv) as [Hr _].
  rewrite Z.mod_small in Hr by lia.
  unfold TW.g_nq. split; [exact Hr | exact Hg].
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

(* The decoder's answer for a closed word, computed once, then matched against the step lemma's pattern (vm_compute on
   the goal itself, with the pattern's operands still existential variables, did not finish in 30 s). *)
Ltac dec := lazymatch goal with |- decode_any ?w = _ =>
  let d := eval vm_compute in (decode_any w) in
  transitivity d; [vm_compute; reflexivity | reflexivity] end.

(* One machine step: the step lemma L at the fetch lemma F; SIDE closes the load's read goals or the branch's
   condition. The cut's common facts (the hypothesis HT) follow the model the step materializes (tc_mat). *)
Ltac stp L F SIDE :=
  npc;
  eapply (SRr_step segs AF0x.Hwx_tfa);
  [ reflexivity
  | rewrite YA0o.restrict_mkst_fx; etransitivity;
    [ eapply L; [exact F | reflexivity | dec | SIDE .. ]
    | rewrite ?ifx0f by reflexivity; reflexivity ]
  | let m := fresh "md" in let Hs := fresh "Hs" in intros m Hs; rewrite YA0o.unrestrict_mkst_mrestrict; nreg;
    match goal with
    | LW : AR_laws _ _, HT0 : lc_tag_common _ _ _ _ _ _ _ _ _ _ _ _ |- _ =>
        let H' := fresh "HT" in pose proof (tc_mat _ _ _ _ _ _ _ _ _ m _ LW HT0 Hs) as H'; clear HT0 Hs; rename H' into HT
    end ].

(* +0xe8c .. +0x1160: the arms that reach the join +0xe8c (lc_at = Some (-1)) end at WANT. *)
Lemma oc_nc : forall cx op B1 ly S (W : world segs) R mem md e,
  AR_laws segs B -> lc_base B MT XL RLO RHI cx ->
  let D := l_pl cx in
  let kd := lc_sub_kd D (lc_oc D (lo_c op)) in
  let tv := lc_tag_vals D B1 (sv_c kd) in
  lc_tag_common B MT cx op B1 ly S W R mem md e ->
  YK11.getr R (Z_to_bv 5 20) = Z_to_bv 64 (if lc_sys tv then 1 else 0) ->
  YK11.getr R (Z_to_bv 5 19) = Z_to_bv 64 (2 ^ 32 - 1) ->
  lc_at tv (sv_key kd) = Some (-1) ->
  SRr segs W (lc_cfg cx 0xe8c R mem md) (fun W2 c2 => lc_st_find B MT cx op 0 W2 c2 \/ lc_st_want B MT cx op W2 c2).
Proof.
  intros cx op B1 ly S W R mem md e LAWS HB D kd tv HT R20 R19 HAT.
  destruct (oc_r cx op B1 ly S W R mem md e HB HT) as (_ & R9 & _ & _ & Hs0 & Hs1).
  pose proof (oc_sp_rd cx op B1 ly S W R mem md e HB HT) as RDS.
  destruct (oc_nq_rd cx op B1 ly S W R mem md e HT) as (RDQ & Hg). fold D kd tv in RDQ, Hg.
  set (g := TW.g_nq (tg_B2 tv)) in *.
  unfold lc_cfg. set (FX := l_fx cx).
  destruct (lc_sys tv) eqn:Esys.
  - (* +0xe8c `beqz s4` falls through: s6 = SPEC_E_REFUSED, `j` WANT *)
    stp YK11.step_beq_ft F_e8c ltac:(nreg; rewrite R20, g0; reflexivity).
    stp YK11.step_addi F_e90 ltac:(idtac).
    stp oc_step_jal0 F_e94 ltac:(reflexivity).
    npc. apply SRr_ret. right.
    eexists ly, S, _, mem, _, e, B1, (-1).
    split; [unfold lc_cfg; reflexivity|].
    fold D kd tv g.
    split.
    { apply (tc_regs cx op B1 ly S W R _ mem _ e HT).
      intros k Hk. cbn [oc_kept In] in Hk. repeat (destruct Hk as [<-|Hk]; [gr; reflexivity|]). destruct Hk. }
    split; [exact HAT|].
    nreg. unfold w64. gr. nimm. rewrite R19.
    split; [unfold lc_want; rewrite Esys; wcl|].
    split; [wcl|].
    rewrite R20, Esys. reflexivity.
  - (* +0xe8c `beqz s4` taken; +0xe98 a0 = -1, `bltz` taken; +0x114c .. +0x1160 the g_nq test *)
    stp YK11.step_beq_tk F_e8c ltac:(nreg; rewrite R20, g0; reflexivity).
    stp YK11.step_addiw F_e98 ltac:(idtac).
    stp YK11.step_blt_tk F_e9c ltac:(nreg; gr; nimm; rewrite R19; vm_compute; reflexivity).
    stp YK11.step_ld F_114c ltac:(first
      [ nreg; gr; nimm; rewrite R9, vaddi; exact RDS
      | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by (vm_compute; split; congruence);
        symmetry; apply u64; vm_compute; split; congruence ]).
    stp YK11.step_lw F_1150 ltac:(first
      [ nreg; gr; nimm; rewrite vaddi; exact RDQ
      | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
    stp YK11.step_addi F_1154 ltac:(idtac).
    stp YK11.step_sltu F_1158 ltac:(idtac).
    stp YK11.step_addi F_115c ltac:(idtac).
    stp YK11.step_andi F_1160 ltac:(idtac).
    npc. apply SRr_ret. right.
    eexists ly, S, _, mem, _, e, B1, (-1).
    split; [unfold lc_cfg; reflexivity|].
    fold D kd tv g.
    split.
    { apply (tc_regs cx op B1 ly S W R _ mem _ e HT).
      intros k Hk. cbn [oc_kept In] in Hk. repeat (destruct Hk as [<-|Hk]; [gr; reflexivity|]). destruct Hk. }
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
    split; [rewrite R19; wcl|].
    rewrite R20, Esys. reflexivity.
Qed.

Lemma lc_op4coal_ok : lc_op4coal_stmt B MT XL RLO RHI.
Proof.
  unfold lc_op4coal_stmt. intros HP cx op W' c' HB HJ.
  destruct HJ as (ly' & S' & regs' & mem' & md' & e & B1 & Hc' & HT & R20 & R7). subst c'.
  pose proof (lp_laws _ _ _ _ _ HP) as LAWS.
  set (D := l_pl cx) in *.
  set (kd := lc_sub_kd D (lc_oc D (lo_c op))) in *.
  set (tv := lc_tag_vals D B1 (sv_c kd)) in *.
  nreg_in R20. nreg_in R7. unfold w64 in R20, R7.
  destruct (oc_r cx op B1 ly' S' W' regs' mem' md' e HB HT) as (R23 & R9 & HF0 & HF1 & Hs0 & Hs1).
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
  (* +0xe6c .. +0xe84: a2 = key, a0 = kind | 8, a1 = -1, s3 = 2^32 - 1, a1 = 8 *)
  stp YK11.step_lwu F_e6c ltac:(first
    [ nreg; rewrite R23; nimm; rewrite vaddi; exact RDK
    | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
  stp YK11.step_srli F_e70 ltac:(idtac).
  stp YK11.step_ori F_e74 ltac:(idtac).
  stp YK11.step_andi F_e78 ltac:(idtac).
  stp YK11.step_addi F_e7c ltac:(idtac).
  stp YK11.step_srli F_e80 ltac:(idtac).
  stp YK11.step_addi F_e84 ltac:(idtac).
  npc.
  match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R1 := R) end.
  assert (A10 : YK11.getr R1 (Z_to_bv 5 10) = Z_to_bv 64 (Z.lor (oc_kind key) 8)).
  { unfold R1. gr. nimm. rewrite vsrli, vori, vandi by lia. rewrite oc_lor8 by lia. reflexivity. }
  assert (A11 : YK11.getr R1 (Z_to_bv 5 11) = Z_to_bv 64 8) by (unfold R1; gr; nimm; wcl).
  assert (A12 : YK11.getr R1 (Z_to_bv 5 12) = Z_to_bv 64 key) by (unfold R1; gr; reflexivity).
  assert (A19 : YK11.getr R1 (Z_to_bv 5 19) = Z_to_bv 64 (2 ^ 32 - 1)) by (unfold R1; gr; nimm; wcl).
  assert (K1 : forall k, In k oc_kept -> YK11.getr R1 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
  { intros k Hk'. cbn [oc_kept In] in Hk'. repeat (destruct Hk' as [<-|Hk']; [unfold R1; gr; reflexivity|]). destruct Hk'. }
  destruct (Z.lor (oc_kind key) 8 =? 8) eqn:E8.
  - (* +0xe88 `bne` falls through: the kind is 0 or 8, not coalescable *)
    stp YK11.step_bne_ft F_e88 ltac:(nreg; rewrite A10, A11, ceq by lia; exact E8).
    assert (HC0 : TC.h_coalescable_m key = 0).
    { rewrite oc_coal. rewrite oc_lor8_cases in E8 by lia. rewrite E8. reflexivity. }
    npc. refine (oc_nc cx op B1 ly' S' W' R1 mem' _ e LAWS HB (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT K1) _ A19 _).
    + rewrite K1 by (cbn; tauto). exact R20.
    + unfold lc_at. fold D kd tv key. rewrite HC0. reflexivity.
  - (* +0xe88 `bne` taken; +0xea8 .. +0xeb0: a0 = key & 0xff0000, a1 = 0x90000 *)
    stp YK11.step_bne_tk F_e88 ltac:(nreg; rewrite A10, A11, ceq by lia; exact E8).
    stp YK11.step_lui F_ea8 ltac:(idtac).
    stp YK11.step_and F_eac ltac:(idtac).
    stp YK11.step_lui F_eb0 ltac:(idtac).
    npc.
    match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R2 := R) end.
    assert (B10 : YK11.getr R2 (Z_to_bv 5 10) = Z_to_bv 64 (oc_kind key * 65536)).
    { unfold R2. gr. nimm. rewrite A12. unfold v_lui. change (Z.shiftl 4080 12) with 16711680.
      rewrite vand by lia. rewrite oc_ff0000 by lia. reflexivity. }
    assert (B11 : YK11.getr R2 (Z_to_bv 5 11) = Z_to_bv 64 589824) by (unfold R2; gr; nimm; wcl).
    assert (K2 : forall k, In k oc_kept -> YK11.getr R2 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
    { intros k Hk'. rewrite <- (K1 k Hk'). cbn [oc_kept In] in Hk'. repeat (destruct Hk' as [<-|Hk']; [unfold R2; gr; reflexivity|]). destruct Hk'. }
    destruct (oc_kind key =? 9) eqn:E9.
    + (* +0xeb4 `beq` taken: the kind is 9, not coalescable *)
      stp YK11.step_beq_tk F_eb4 ltac:(nreg; rewrite B10, B11, ceq by lia;
        apply Z.eqb_eq; apply Z.eqb_eq in E9; lia).
      assert (HC0 : TC.h_coalescable_m key = 0).
      { rewrite oc_coal. rewrite E9. rewrite !orb_true_r. reflexivity. }
      npc. refine (oc_nc cx op B1 ly' S' W' R2 mem' _ e LAWS HB (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT K2) _ _ _).
      * rewrite K2 by (cbn; tauto). exact R20.
      * unfold R2. gr. exact A19.
      * unfold lc_at. fold D kd tv key. rewrite HC0. reflexivity.
    + (* +0xeb4 `beq` falls through: coalescable; +0xeb8 a0 = the spill, +0xebc a3 = g_nq *)
      stp YK11.step_beq_ft F_eb4 ltac:(nreg; rewrite B10, B11, ceq by lia;
        apply Z.eqb_neq; apply Z.eqb_neq in E9; lia).
      assert (HC1 : TC.h_coalescable_m key = 1).
      { rewrite oc_coal. rewrite oc_lor8_cases in E8 by lia. rewrite E8, E9. reflexivity. }
      stp YK11.step_ld F_eb8 ltac:(first
        [ nreg; gr; nimm; rewrite (K2 9 ltac:(cbn; tauto)), R9, vaddi; exact RDS
        | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by (vm_compute; split; congruence);
          symmetry; apply u64; vm_compute; split; congruence ]).
      stp YK11.step_lwu F_ebc ltac:(first
        [ nreg; gr; nimm; rewrite vaddi; exact RDQ
        | rewrite YN01.bytes_le_to_Z_Z_to_le_bytes by lia; symmetry; apply u64; lia ]).
      npc.
      match goal with |- SRr _ _ (mkCfg (@YK11.mkst _ ?R _ _ _) _) _ => set (R3 := R) end.
      assert (C13 : YK11.getr R3 (Z_to_bv 5 13) = Z_to_bv 64 g) by (unfold R3; gr; reflexivity).
      assert (K3 : forall k, In k oc_kept -> YK11.getr R3 (Z_to_bv 5 k) = YK11.getr regs' (Z_to_bv 5 k)).
      { intros k Hk'. rewrite <- (K2 k Hk'). cbn [oc_kept In] in Hk'. repeat (destruct Hk' as [<-|Hk']; [unfold R3; gr; reflexivity|]). destruct Hk'. }
      destruct (g =? 0) eqn:Eg.
      * (* +0xec0 `beqz a3` taken: g_nq = 0, the find answers -1 *)
        stp YK11.step_beq_tk F_ec0 ltac:(nreg; rewrite C13, g0, ceq by lia; exact Eg).
        apply Z.eqb_eq in Eg.
        npc. refine (oc_nc cx op B1 ly' S' W' R3 mem' _ e LAWS HB (tc_regs _ _ _ _ _ _ _ _ _ _ _ HT K3) _ _ _).
        -- rewrite K3 by (cbn; tauto). exact R20.
        -- unfold R3. gr. unfold R2. gr. exact A19.
        -- unfold lc_at. fold D kd tv key. rewrite HC1. cbn [negb Z.eqb]. cbn [TOP.submit_find_at].
           fold g. rewrite Eg. reflexivity.
      * (* +0xec0 `beqz a3` falls through; +0xec4 .. +0xedc the find loop's entry *)
        stp YK11.step_beq_ft F_ec0 ltac:(nreg; rewrite C13, g0, ceq by lia; exact Eg).
        apply Z.eqb_neq in Eg.
        stp YK11.step_addi F_ec4 ltac:(idtac).
        stp YK11.step_addi F_ec8 ltac:(idtac).
        stp YK11.step_auipc F_ecc ltac:(idtac).
        stp YK11.step_addi F_ed0 ltac:(idtac).
        stp YK11.step_addi F_ed4 ltac:(idtac).
        stp YK11.step_srli F_ed8 ltac:(idtac).
        stp YK11.step_addi F_edc ltac:(idtac).
        npc. apply SRr_ret. left.
        eexists ly', S', _, mem', _, e, B1.
        split; [unfold lc_cfg; reflexivity|].
        fold D kd tv key g.
        split.
        { apply (tc_regs cx op B1 ly' S' W' regs' _ mem' _ e HT).
          intros k Hk'. rewrite <- (K3 k Hk'). cbn [oc_kept In] in Hk'. repeat (destruct Hk' as [<-|Hk']; [gr; reflexivity|]). destruct Hk'. }
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
        rewrite (K3 20) by (cbn; tauto). exact R20.
Qed.

End s.
