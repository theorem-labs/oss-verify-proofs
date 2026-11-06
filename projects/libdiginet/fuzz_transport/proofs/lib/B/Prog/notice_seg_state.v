(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to rc.2's binaries and LPS 2afba80c; the theorem statements are restated in the form rc.2 states them. *)
(* Modified by Theorem Labs, 2026-10: the entry segment of the image-A walk of libreac/fuzz_decode's LLVMFuzzerTestOneInput, with proof steps adapted from proofs/libreac/fuzz_grant/lib/A/Prog/CtrlStampHeadamp.v (pb_reac_ctrl_stamp_headamp's prologue and its class-0 stack malloc, origin/cold/pg-prog), proofs/libreac/fuzz_grant/lib/A/Prog/GrantACja.v (land_m32, denot_and_m32, sp1_facts), proofs/libreac/fuzz_grant/lib/A/Prog/GrantFrame.v (val_mem_of_rd32, rdword_of_val_mem, val_mem_moved), lib/Reusable/YCbq.v (call_effect_journal) and lib/A/Prog/YC85.v (aj_stack_malloc_atS); module paths changed. *)
(* Modified by Theorem Labs, 2026-10: the walk is reac-repacer/fuzz_uci's check_clamp in image A, in the shape of the released image-A walks proofs/libreac/fuzz_decode/lib/A/Prog/LLVMFuzzerTestOneInput_seg_entry.v, .../LLVMFuzzerTestOneInput_seg_copy.v and .../LLVMFuzzerTestOneInput_seg_exit_tail.v at origin/ossv/recipes 88154566652a: module paths, listing symbol type, the symbolic states, the cut points and every address and offset are this function's; the fake-frame class is 1, the single intrinsic is __asan_memcpy of 20 bytes, and the result is the caller-journal contract of lib/A/Prog/check_clamp_cg.v. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths changed; 663 of its 1139 lines of code are new or changed and 8 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/reac-repacer/fuzz_uci/lib/A/Prog/check_clamp_cgW.v, with its module paths, module names and numbers changed; 902 of its 1078 lines of code are new or changed and 963 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/A/Prog/SlostHead.v, with its module paths, module names and numbers changed; 2194 of its 2305 lines of code are new or changed and 967 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libdiginet/fuzz_transport/lib/B/Prog/diginet_session_init_cgW.v, with its module names changed; 706 of its 822 lines of code are new or changed and 2189 lines of the source are left out. *)
(* notice_seg_state: the N_STATE arm of notice's walk on fuzz_transport.asan-ubsan (lib/B/Prog/notice_cgW.v),
   from the jump `jr a0` (0x83474) with a0 = 0x834f4:
     0x834f4 - 0x83508  a6 = GOT (object 13), g = GOT.n (the 4-byte signed load at GOT + 0, read from the region of
                        that field, its value the world's u32), a0 = p + 4; `blt 15, g` splits g > 15 from g <= 15;
     [g <= 15]          the shadow check of p + 4 (the notice's shadow entry); `bgeu g, 16` to the trap 0x83610, which
                        notice_m rules out (g < 0 is None there); a2 = 12 g, `bltu ~(GOT + 4), 12 g` to the trap (on this
                        path 0 <= g <= 15: no wrap); a2 = GOT + 12 g + 4, pinned to atom 42 (= GOT + 12 g) + 4, the
                        record GOT.t[g] (a region based at atom 42, with a shadow entry: GOT's payload has shadow 0,
                        trans_notice_cells) gets n->state, n->old_state and n->reason, each after the shadow checks of
                        the record word and of the notice word;
     0x835bc - 0x835c4  GOT.n + 1, `blt` to the trap at INT_MAX (nt_ovf_br; notice_m's int_inc is None there), the
                        store of g + 1 at GOT + 0;
     0x835c8 - 0x835e0  the shadow check of p + 4, a0 = n->state; `bne a0, 2` to the epilogue (ret) when n->state is not
                        S_ONLINE; else ra loaded back, sp = sp + 16, the tail jump to check_state_online (0x85320).
   The world after the stores is nt_B2 Bw n (notice_seg_base.v): the record when 0 <= g < 16 (ntstate_tw4), then
   GOT.n := g + 1. check_state_online is a leaf: its statement (check_state_online_cg.v, read through DgnTransportBCg.v
   transport_leaf_at) is applied at the jump's state, notice's entry sp and ra, through TransportGCg.v gx_call_leaf and
   DgnTransportBLeafb.v decode_leafb_journal (ntstate_online); its model call is notice_m's (nt_m_state). *)
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0j YK0s YK0o.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP01 YP00 YP0i YCbn.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YN3v YI04 YI00 YI08 YG0s.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq YC5d.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require Import YM05 YImgTop.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable Require YI16 YI5b YI5c YO0f.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import PaTable PaSym PaStep PaRun PaShadow PaJournal.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import
DgnTransportBSyms DgnTransportBList DgnTransportBAddr DgnTransportBPa DgnTransportBImg DgnTransportBPaLib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import YC4b.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import YC1g YC1h.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require Import YB1v Img0.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B Require YE2k AsanCells TransportGB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A Require Import W_journalG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import DgnTransportBCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TransportGCg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TransportGRwB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.A.Prog Require Import TWorldG.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import TWorldB TImgB.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import m_set_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import check_state_data_cg check_state_desk_cg notice_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require Import notice_seg_base notice_seg_lib.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog Require
  DgnTransportBLeafb AsanKA check_state_wake_c check_state_online_c check_state_online_cg.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel Require TWorld TCb TImg TWorldLemmas.
From OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec Require DgnSpec.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
Open Scope Z_scope.
Module YK11 := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YK11.
Module TG := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.TransportGB.
Module TW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorld.
Module TC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TCb.
Module TI := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TImg.
Module TWL := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.TModel.TWorldLemmas.
Module DSpec := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Spec.DgnSpec.
Module BAC := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.AsanCells.
Module AKA := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.AsanKA.
Module CSW := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_wake_c.
Module LSOc := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_c.
Module LSO := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.check_state_online_cg.
Module LB := OSSVerify.Proofs.libdiginet.fuzz_transport.lib.B.Prog.DgnTransportBLeafb.
#[global] Remove Hints OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5b.src0_sink_head
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink
  OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YI5c.src0_sink_laws : typeclass_instances.

(* ------------------------------------------------------------------ *)
(* A leaf entered by a tail jump of the walk                           *)
(* ------------------------------------------------------------------ *)

(* Every byte of the harness globals' hull lies in one loaded segment of image B, so no world hides it. *)
Lemma ntstate_hull_vis : forall (W : world tfibsegs) x, TG.G_HARNESS_B_LO <= x < TG.G_HARNESS_B_HI ->
  w_H W (Z_to_bv 64 x) = false.
Proof.
  intros W x Hx. replace x with (TG.G_HARNESS_B_LO + (x - TG.G_HARNESS_B_LO)) by lia.
  apply (LB.decode_leafb_covers_visible (w_H W) TG.G_HARNESS_B_LO (TG.G_HARNESS_B_HI - TG.G_HARNESS_B_LO));
    [exact (w_Hoff W) | vm_compute; reflexivity | lia | unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia].
Qed.

(* The world relation at the view of a world is the world relation at the raw memory (the leaf's csw_view). *)
Lemma ntstate_tw_csw : forall (W : world tfibsegs) m Bw,
  tw_at TMAP_B (aview tfibsegs (w_H W) m) Bw -> tw_at TMAP_B (CSW.csw_view m) Bw.
Proof.
  intros W m Bw H. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  pose proof (LB.decode_leafb_mrd W m x (ntstate_hull_vis W x (TMAP_B_hull x Hx))) as E.
  unfold CSW.csw_view, aview. rewrite <- E. reflexivity.
Qed.

(* The leaf's footprint holds every range of the hull. *)
Lemma ntstate_rng_hull : forall (W : world tfibsegs) lo len,
  TG.G_HARNESS_B_LO <= lo -> lo + len <= TG.G_HARNESS_B_HI ->
  LB.LExecF.rng (LB.LCK.RNG_W (world tfibsegs) (@w_H tfibsegs) W) lo len.
Proof.
  intros W lo len H1 H2. apply LB.decode_leafb_rng;
    [unfold TG.G_HARNESS_B_LO in H1; lia | unfold TG.G_HARNESS_B_HI in H2; lia |].
  intros a Ha. apply ntstate_hull_vis. lia.
Qed.

(* The walk's kept bytes across a leaf entered at notice's entry sp: the leaf's window lies in notice's. *)
Lemma ntstate_KA_leaf : forall (W : world tfibsegs) memc (mT m2 : word -> option byte) regs Bw n spT,
  nt_KA W memc mT (nt_Zs regs Bw n) -> spT = spZ regs ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  (forall a, apresent (w_H W) mT a -> apresent (w_H W) m2 a) ->
  nt_KA W memc m2 (nt_Zs regs Bw n).
Proof.
  intros W memc mT m2 regs Bw n spT HKA Hsp Hk Hg.
  apply (nt_KA_step W memc mT m2 _ (fun a => spT - ESTACK <= a < spT) HKA); [| exact Hg |].
  - intros a Ha Hn. apply Hk; [exact Ha | exact Hn | intros Hw; inversion Hw].
  - intros a Ha. left. subst spT. assert (FS : NOTICE_STK = 8240) by reflexivity. unfold ESTACK in Ha. lia.
Qed.

(* The world relation across a leaf whose window lies above the hull. *)
Lemma ntstate_tw_leaf : forall (W : world tfibsegs) (mT m2 : word -> option byte) Bw spT,
  tw_at TMAP_B (aview tfibsegs (w_H W) mT) Bw -> TG.G_HARNESS_B_HI <= spT - ESTACK ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ (spT - ESTACK <= a < spT) -> ~ LB.LCK.in_wr [] a ->
     aview tfibsegs (w_H W) m2 a = aview tfibsegs (w_H W) mT a) ->
  tw_at TMAP_B (aview tfibsegs (w_H W) m2) Bw.
Proof.
  intros W mT m2 Bw spT H Hs Hk. apply (tw_kept TMAP_B _ _ Bw H). intros x Hx.
  pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in *.
  apply Hk; [lia | lia | intros Hw; inversion Hw].
Qed.

(* ------------------------------------------------------------------ *)
(* Values and branches                                                 *)
(* ------------------------------------------------------------------ *)

(* A u32 whose signed value is not negative is its signed value. *)
Lemma ntstate_u_small : forall u, 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u -> bv_swrap 32 u = u.
Proof.
  intros u R H. unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus in *.
  change (2 ^ Z.of_N 32) with (2 ^ 32) in *. change (2 ^ 32 / 2) with (2 ^ 31) in *.
  Z.div_mod_to_equations. lia.
Qed.

(* Byte j < 4 of a stored word of value v. *)
Lemma ntstate_byte4 : forall E e v (j : nat), sv_denot E e = Z_to_bv 64 v -> (j < 4)%nat ->
  bv_unsigned (YP09.byte_of_word (sv_denot E e) (Z.of_nat j)) = YO0f.le_byte v 4 j.
Proof.
  intros E e v j H Hj. rewrite H. unfold YP09.byte_of_word. rewrite !Z_to_bv_unsigned.
  unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 8) with 256. change (2 ^ Z.of_N 64) with (2 ^ 64).
  unfold YO0f.le_byte. change (8 * Z.of_nat 4) with 32.
  rewrite (LB.decode_leafb_byte_mod v 64 (8 * Z.of_nat j)) by lia.
  rewrite (LB.decode_leafb_byte_mod v 32 (8 * Z.of_nat j)) by lia.
  reflexivity.
Qed.

(* `blt 15, g` (0x83508): taken exactly when 15 < g. *)
Lemma ntstate_br15 : forall E u, ew E 37 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 ->
  branch_taken BC_LT (sv_denot E (SLit 15)) (sv_denot E (SExt true 32 (SOff 37 0))) = (15 <? bv_swrap 32 u).
Proof.
  intros E u H R. destruct (nt_inc_U E 37 u H R) as (_ & S1 & _).
  cbn [branch_taken]. unfold bv_lts.
  change (bv_signed (sv_denot E (SLit 15))) with (Sg E (SLit 15)).
  change (bv_signed (sv_denot E (SExt true 32 (SOff 37 0)))) with (Sg E (SExt true 32 (SOff 37 0))).
  rewrite S1, S_SLit. replace (bv_swrap 64 15) with 15 by reflexivity. reflexivity.
Qed.

Ltac ntstate_cases u :=
  let C := fresh "C" in
  assert (C : u = 0 \/ u = 1 \/ u = 2 \/ u = 3 \/ u = 4 \/ u = 5 \/ u = 6 \/ u = 7 \/ u = 8 \/ u = 9 \/
              u = 10 \/ u = 11 \/ u = 12 \/ u = 13 \/ u = 14 \/ u = 15) by lia;
  destruct C as [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | [-> | -> ] ] ] ] ] ] ] ] ] ] ] ] ] ] ].

(* `bgeu g, 16` (0x83520): not taken when 0 <= g < 16. *)
Lemma ntstate_br_geu : forall E u, ew E 37 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u < 16 ->
  branch_taken BC_GEU (sv_denot E (SExt true 32 (SOff 37 0))) (sv_denot E (SLit 16)) = false.
Proof.
  intros E u H R Hg. pose proof (ntstate_u_small u R ltac:(lia)) as Eu. rewrite Eu in Hg.
  cbn [sv_denot]. rewrite H. clear H Eu R. ntstate_cases u; vm_compute; reflexivity.
Qed.

(* `bltu ~(GOT + 4), 12 g` (0x83538, the pointer-overflow check): not taken when 0 <= g < 16. *)
Lemma ntstate_br_ptr : forall E u, ew E 37 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u < 16 ->
  bv_unsigned (ew E 254) = TB_GOT ->
  branch_taken BC_LTU (sv_denot E (SAlu ALU_XOR (SOff 254 4) (SLit (-1))))
    (sv_denot E (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 4))
       (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 2)))) = false.
Proof.
  intros E u H R Hg U13. pose proof (ntstate_u_small u R ltac:(lia)) as Eu. rewrite Eu in Hg.
  assert (E254 : ew E 254 = Z_to_bv 64 TB_GOT) by (rewrite <- U13; symmetry; apply Z_to_bv_bv_unsigned).
  cbn [sv_denot]. rewrite H, E254. clear H Eu R U13 E254. ntstate_cases u; vm_compute; reflexivity.
Qed.

(* The record's address (0x83540): GOT + 12 g + 4 = atom 42 + 4 when 0 <= g < 16. *)
Lemma ntstate_addr : forall E u, ew E 37 = Z_to_bv 64 u -> 0 <= u < 2 ^ 32 -> 0 <= bv_swrap 32 u < 16 ->
  bv_unsigned (ew E 254) = TB_GOT -> ew E 42 = Z_to_bv 64 (TB_GOT + 12 * bv_swrap 32 u) ->
  sv_denot E (SAlu ALU_ADD (SAlu ALU_ADD (SOff 254 0)
    (SAlu ALU_SUB (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 4))
       (SAlu ALU_SLL (SExt true 32 (SOff 37 0)) (SLit 2)))) (SLit 4)) = sv_denot E (SOff 42 4).
Proof.
  intros E u H R Hg U13 E42. pose proof (ntstate_u_small u R ltac:(lia)) as Eu. rewrite Eu in Hg, E42.
  assert (E254 : ew E 254 = Z_to_bv 64 TB_GOT) by (rewrite <- U13; symmetry; apply Z_to_bv_bv_unsigned).
  apply bv_eq. cbn [sv_denot]. rewrite H, E254, E42. clear H Eu R U13 E254 E42.
  ntstate_cases u; vm_compute; reflexivity.
Qed.

(* `bne n->state, 2` (0x835e0). *)
Lemma ntstate_br_ne : forall E (NB : list byte), ew E 34 = Z_to_bv 64 (TW.u_at NB 4 4) ->
  branch_taken BC_NE (sv_denot E (SExt true 32 (SOff 34 0))) (sv_denot E (SLit 2)) = negb (TW.s32_at NB 4 =? 2).
Proof.
  intros E NB H. pose proof (TWL.u_at_range NB 4 4) as R. change (8 * Z.of_nat 4) with 32 in R.
  cbn [branch_taken]. rewrite (nt_sext32 E 34 _ H R). change (bv_swrap 32 (TW.u_at NB 4 4)) with (TW.s32_at NB 4).
  pose proof (nt_s32_range NB 4) as Rs. f_equal.
  cbn [sv_denot]. unfold bv_eqb. rewrite !Z_to_bv_unsigned. unfold bv_wrap. change (bv_modulus 64) with (2 ^ 64).
  rewrite (Z.mod_small 2 (2 ^ 64)) by lia.
  destruct (Z.eqb_spec (TW.s32_at NB 4) 2) as [Heq | Hne].
  - rewrite Heq. apply Z.eqb_refl.
  - apply Z.eqb_neq. intros HH. apply Hne.
    destruct (Z_lt_le_dec (TW.s32_at NB 4) 0) as [Hneg | Hpos].
    + rewrite <- (Z.mod_unique (TW.s32_at NB 4) (2 ^ 64) (-1) (TW.s32_at NB 4 + 2 ^ 64)) in HH by lia. lia.
    + rewrite (Z.mod_small (TW.s32_at NB 4) (2 ^ 64)) in HH by lia. exact HH.
Qed.

(* ------------------------------------------------------------------ *)
(* The world after the record and GOT.n                                *)
(* ------------------------------------------------------------------ *)

Definition ntstate_inw (k x : Z) : bool := (TB_GOT + k <=? x) && (x <? TB_GOT + k + 4).
Definition ntstate_rdu (k : Z) (rdF rd : Z -> option Z) (x : Z) : option Z :=
  if ntstate_inw k x then rdF x else rd x.

Lemma ntstate_inw_in : forall k x, TB_GOT + k <= x < TB_GOT + k + 4 -> ntstate_inw k x = true.
Proof. intros k x Hx. unfold ntstate_inw. apply andb_true_iff. split; [apply Z.leb_le | apply Z.ltb_lt]; lia. Qed.
Lemma ntstate_inw_out : forall k x, ~ (TB_GOT + k <= x < TB_GOT + k + 4) -> ntstate_inw k x = false.
Proof.
  intros k x Hx. unfold ntstate_inw. apply andb_false_iff.
  destruct (Z_le_gt_dec (TB_GOT + k) x); [right; apply Z.ltb_ge | left; apply Z.leb_gt]; lia.
Qed.
Lemma ntstate_inw_false : forall k x, ntstate_inw k x = false -> ~ (TB_GOT + k <= x < TB_GOT + k + 4).
Proof. intros k x H Hx. rewrite (ntstate_inw_in k x Hx) in H. discriminate H. Qed.

(* One 4-byte word of the record written over a view. *)
Lemma ntstate_tw1 : forall (rd rdF : Z -> option Z) Bw k v,
  tw_at TMAP_B rd Bw -> 0 <= k -> k + 4 <= TW.SZ_GOT ->
  (forall j, (j < 4)%nat -> rdF (TB_GOT + k + Z.of_nat j) = Some (YO0f.le_byte v 4 j)) ->
  tw_at TMAP_B (ntstate_rdu k rdF rd) (TW.upd Bw (TW.OFF_GOT + k) (TW.put 4 v)).
Proof.
  intros rd rdF Bw k v H Hk Hk4 Hv.
  apply (tw_write TMAP_B rd (ntstate_rdu k rdF rd) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT k 4 v TMAP_B_ok H TMAP_B_GOT);
    [lia | lia | |].
  - intros j Hj. unfold ntstate_rdu. rewrite ntstate_inw_in by lia. exact (Hv j Hj).
  - intros x Hx Hn. unfold ntstate_rdu. rewrite ntstate_inw_out by lia. reflexivity.
Qed.

Lemma ntstate_tw4 : forall (rd0 rdF : Z -> option Z) Bw (g st old rs gn : Z),
  tw_at TMAP_B rd0 Bw -> 0 <= g < 16 ->
  (forall j, (j < 4)%nat -> rdF (TB_GOT + 12 * g + 4 + Z.of_nat j) = Some (YO0f.le_byte st 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_GOT + 12 * g + 8 + Z.of_nat j) = Some (YO0f.le_byte old 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_GOT + 12 * g + 12 + Z.of_nat j) = Some (YO0f.le_byte rs 4 j)) ->
  (forall j, (j < 4)%nat -> rdF (TB_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte gn 4 j)) ->
  (forall x, tw_in TMAP_B x -> ~ (TB_GOT + 12 * g + 4 <= x < TB_GOT + 12 * g + 16) -> ~ (TB_GOT <= x < TB_GOT + 4) ->
     rdF x = rd0 x) ->
  tw_at TMAP_B rdF
    (TW.set_GOT_n (TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw g st) g old) g rs) gn).
Proof.
  intros rd0 rdF Bw g st old rs gn H0 Hg H1 H2 H3 H4 HF.
  pose proof (ntstate_tw1 rd0 rdF Bw (4 + 12 * g) st H0 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)
    ltac:(intros j Hj; rewrite <- (H1 j Hj); f_equal; lia)) as T1.
  replace (TW.OFF_GOT + (4 + 12 * g)) with (TW.A_GOT_t_state g) in T1 by (unfold TW.A_GOT_t_state; lia).
  change (TW.upd Bw (TW.A_GOT_t_state g) (TW.put 4 st)) with (TW.set_GOT_t_state Bw g st) in T1.
  pose proof (ntstate_tw1 _ rdF _ (8 + 12 * g) old T1 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)
    ltac:(intros j Hj; rewrite <- (H2 j Hj); f_equal; lia)) as T2.
  replace (TW.OFF_GOT + (8 + 12 * g)) with (TW.A_GOT_t_old g) in T2 by (unfold TW.A_GOT_t_old; lia).
  change (TW.upd (TW.set_GOT_t_state Bw g st) (TW.A_GOT_t_old g) (TW.put 4 old))
    with (TW.set_GOT_t_old (TW.set_GOT_t_state Bw g st) g old) in T2.
  pose proof (ntstate_tw1 _ rdF _ (12 + 12 * g) rs T2 ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)
    ltac:(intros j Hj; rewrite <- (H3 j Hj); f_equal; lia)) as T3.
  replace (TW.OFF_GOT + (12 + 12 * g)) with (TW.A_GOT_t_reason g) in T3 by (unfold TW.A_GOT_t_reason; lia).
  change (TW.upd (TW.set_GOT_t_old (TW.set_GOT_t_state Bw g st) g old) (TW.A_GOT_t_reason g) (TW.put 4 rs))
    with (TW.set_GOT_t_reason (TW.set_GOT_t_old (TW.set_GOT_t_state Bw g st) g old) g rs) in T3.
  unfold TW.set_GOT_n, TW.A_GOT_n.
  apply (tw_write TMAP_B _ rdF _ TW.OFF_GOT TB_GOT TW.SZ_GOT 0 4 gn TMAP_B_ok T3 TMAP_B_GOT);
    [lia | unfold TW.SZ_GOT; lia | exact H4 |].
  intros x Hx Hn. unfold ntstate_rdu.
  destruct (ntstate_inw (12 + 12 * g) x) eqn:E3; [reflexivity|].
  destruct (ntstate_inw (8 + 12 * g) x) eqn:E2; [reflexivity|].
  destruct (ntstate_inw (4 + 12 * g) x) eqn:E1; [reflexivity|].
  apply ntstate_inw_false in E1, E2, E3.
  apply HF; [exact Hx | lia | lia].
Qed.

(* No payload byte outside GOT.n and (when 0 <= g < 16) the record is a byte the walk may change. *)
Lemma ntstate_notzs : forall regs Bw n x, TI.n_kind n = TC.N_STATE ->
  TG.G_HARNESS_B_HI <= spZ regs - NOTICE_STK -> tw_in TMAP_B x ->
  (0 <= TW.GOT_n Bw < 16 -> ~ (TB_GOT + 12 * TW.GOT_n Bw + 4 <= x < TB_GOT + 12 * TW.GOT_n Bw + 16)) ->
  ~ (TB_GOT <= x < TB_GOT + 4) -> ~ nt_Zs regs Bw n x.
Proof.
  intros regs Bw n x Ek Hce Hx Hr Hn [Hz | Hz].
  - pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_HI in *. lia.
  - unfold notice_wr in Hz.
    unfold TC.N_STATE, TC.N_ACKED, TC.N_ACK_LOST, TC.N_DESK, TC.N_DATA, TC.N_FOREIGN in Hz, Ek.
    destruct Hz as [(_ & [(Hg & Hw) | Hw]) | [(E' & _) | [(E' & _) | [(E' & _) | [(E' & _) | (E' & _)]]]]]; try lia.
    + unfold TC.TRANS_MAX in Hg. apply (Hr Hg). unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ in Hw. lia.
    + unfold twb_fld, TW.A_GOT_n in Hw. lia.
Qed.

(* A range the call stores into lies off the notice's first 16 bytes (notice_apart, pointwise). *)
Lemma ntstate_apart_iv : forall p q m, 0 < m ->
  (forall x, q <= x < q + m -> ~ (p <= x < p + 72)) -> p + 16 <= q \/ q + m <= p.
Proof.
  intros p q m Hm H. destruct (Z_le_gt_dec (p + 16) q) as [L|L]; [left; exact L|].
  destruct (Z_le_gt_dec (q + m) p) as [R|R]; [right; exact R|].
  exfalso. apply (H (Z.max p q)); lia.
Qed.

(* ------------------------------------------------------------------ *)
(* The arm's facts                                                     *)
(* ------------------------------------------------------------------ *)

Section state. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Local Abbreviation tfib_sink_head := YE2k.tfib_sink_head.
Variable B : asyms.
Variable MT : ameter_ops.
Local Abbreviation segs := tfibsegs.
Local Abbreviation VAL := (@pa_val _ transportb_listing PI_transportb).
Local Abbreviation BASE := (@pa_val _ transportb_listing PI_transportb A_TEXT).

(* The shadow entries of the record path: the notice's 72 bytes and the record GOT.t[g]. *)
Definition ntstate_SH : list shent := [mkSHE 11 0 72; mkSHE 42 4 16].

(* The atoms the arm reads, at any valuation that agrees with the walk's below atom 43. *)
Lemma ntstate_envf : forall (E : env) regs NB Bw p,
  img_env VAL A_LIM E -> (forall j, (j < 43)%nat -> ew E j = ew (nt_E regs NB Bw) j) ->
  YK11.getr regs 11 = w64 p -> 0 <= p < 2 ^ 64 ->
  bv_unsigned (ew E 2) = spZ regs /\ ew E 1 = YK11.getr regs 1 /\ ew E 11 = Z_to_bv 64 p /\
  bv_unsigned (ew E 11) = p /\ ew E 32 = Z_to_bv 64 SHADOW_OFF /\
  ew E 33 = Z_to_bv 64 (TW.u_at NB 0 4) /\ ew E 34 = Z_to_bv 64 (TW.u_at NB 4 4) /\
  ew E 35 = Z_to_bv 64 (TW.u_at NB 8 4) /\ ew E 36 = Z_to_bv 64 (TW.u_at NB 12 4) /\
  ew E 37 = Z_to_bv 64 (TW.u_at Bw TW.A_GOT_n 4) /\ ew E 42 = Z_to_bv 64 (TB_GOT + 12 * TW.GOT_n Bw) /\
  bv_unsigned (ew E (A_OBJ 13)) = TB_GOT /\ bv_unsigned (ew E 254) = TB_GOT.
Proof.
  intros E regs NB Bw p HEI Elo H11 Hp.
  destruct nt_cvals as (_ & _ & _ & _ & V13 & _).
  assert (U13 : bv_unsigned (ew E (A_OBJ 13)) = TB_GOT)
    by (rewrite (HEI (A_OBJ 13) ltac:(unfold A_OBJ, A_TEXT, A_LIM; lia)), V13; reflexivity).
  assert (E11 : ew E 11 = Z_to_bv 64 p)
    by (rewrite (Elo 11%nat ltac:(lia)), (nt_E_reg regs NB Bw 11 11%bv eq_refl), H11; reflexivity).
  split; [rewrite (Elo 2%nat ltac:(lia)), (nt_E_reg regs NB Bw 2 2%bv eq_refl); reflexivity|].
  split; [rewrite (Elo 1%nat ltac:(lia)); exact (nt_E_reg regs NB Bw 1 1%bv eq_refl)|].
  split; [exact E11|].
  split; [rewrite E11; apply unsigned_lit_small; lia|].
  split; [rewrite (Elo 32%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 0 ltac:(lia))|].
  split; [rewrite (Elo 33%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 1 ltac:(lia))|].
  split; [rewrite (Elo 34%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 2 ltac:(lia))|].
  split; [rewrite (Elo 35%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 3 ltac:(lia))|].
  split; [rewrite (Elo 36%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 4 ltac:(lia))|].
  split; [rewrite (Elo 37%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 5 ltac:(lia))|].
  split; [rewrite (Elo 42%nat ltac:(lia)); exact (nt_E_atom regs NB Bw 10 ltac:(lia))|].
  split; [exact U13 | exact U13].
Qed.

(* The record's 12 bytes have shadow 0 at every AR state (trans_notice_cells), when 0 <= g < 16. *)
Lemma ntstate_rec_ra : forall ly S (W : world segs) mem md g,
  trans_notice_cells B -> @AR rc segs B ly S W mem md -> 0 <= g < 16 ->
  range_addressable (aview segs (w_H W) mem) SHADOW_OFF (TB_GOT + 12 * g + 4) 12.
Proof.
  intros ly S W mem md g HZ HAR Hg x Hx.
  pose proof (Z.div_mod x 8 ltac:(lia)) as Dx. pose proof (Z.mod_pos_bound x 8 ltac:(lia)) as Mx.
  unfold shadow_of_addr. exists 0. split; [|left; reflexivity].
  assert (Hz := decode_zshadow_rd B ly S W mem md TB_GOT (TB_GOT + TW.SZ_GOT) (8 * (x / 8)) HAR
    ltac:(rewrite Z.mul_comm; apply Z_mod_mult) ltac:(unfold TB_GOT in *; lia)
    ltac:(unfold TB_GOT, TW.SZ_GOT in *; lia) HZ).
  replace (SHADOW_OFF + x / 8) with (BAC.shadow_addr (8 * (x / 8))); [exact Hz|].
  unfold BAC.shadow_addr, BAC.ASAN_K, SHADOW_OFF. rewrite Z.mul_comm, Z.div_mul by lia. lia.
Qed.

(* The record's region at any memory: its 12 bytes are bytes of G, so writable. *)
Lemma ntstate_rec_ok : forall E (m : word -> option byte) g, bv_unsigned (ew E 42) = TB_GOT + 12 * g -> 0 <= g < 16 ->
  region_ok segs E m nt_reg_rec.
Proof.
  intros E m g HU Hg. unfold nt_reg_rec, region_ok.
  cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
  rewrite HU. split; [unfold TB_GOT; lia|]. split; [unfold TB_GOT; lia|]. split; [|constructor].
  intros o Ho. apply (gx_rw_writable segs TG.G_HARNESS_B (TB_GOT + 12 * g + o) G_HARNESS_B_rw).
  apply nt_inG_GOT. lia.
Qed.

(* The post at a leaf's return to notice's caller (a tail jump: the leaf ran from notice's entry sp with notice's
   entry ra, so it returns to raw = the entry ra), from the walk's last facts. *)
Lemma ntstate_close : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    regsF (raw : word) mF mdF,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    mF mdF k ->
  nt_KA W memc mF (nt_Zs regs Bw n) ->
  tw_at TMAP_B (aview segs (w_H W) mF) Bw' ->
  aregs_preserved regs regsF -> raw = YK11.getr regs 1 ->
  @transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw' W
    (mkCfg (@YK11.mkst fx regsF raw mF (YK11.seg_rom segs)) mdF).
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsF raw mF mdF HC HJF
    [KA GA] HtwF HP Hraw.
  destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
    as (HAR & Hwin & Hsp & Hce & _ & _ & _ & _ & _ & _).
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJ Hra Hra4 Hgp Htp H11 Hsp16 Hlo
    Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  assert (GLOW : forall a, inG TG.G_HARNESS_B a -> a < kLowMemEnd).
  { intros a Ha. exact (proj2 (transportb_segs_low a (proj1 (HGX a Ha)))). }
  unfold transport_notice_post, transport_cg_post.
  exists lyc, Sc, regsF, mF, mdF, 0.
  split; [rewrite Hraw; reflexivity|].
  split; [unfold NOTICE_EV; lia|].
  split; [rewrite Z.add_0_r; exact HJF|].
  split; [exact HP|].
  split; [reflexivity|].
  split; [apply Permutation_refl|].
  split.
  { apply (dk_kept_step_g segs B LAWS transportb_segs_low TG.G_HARNESS_B lyc Sc W memc mdc memc mF
      (spZ regs - NOTICE_STK) (spZ regs) (notice_wr Bw n) (nt_Zs regs Bw n) HAR).
    - apply dk_kept_refl_g. exact Hwin.
    - exact KA.
    - exact GA.
    - intros a [Hw | Hw] Hc; [exact Hw|]. exfalso. pose proof (GLOW a (nt_wr_G _ _ _ Hw)). unfold kLowMemEnd in *. lia.
    - intros b m i Hb Hi [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (al_blocks _ _ LAWS lyc Sc W memc mdc b m HAR Hb) as (_ & H4096 & Hbc & _). lia.
    - intros a [Hw | Hw] Hi HnG _ _.
      + pose proof (transportb_segs_low a Hi) as Hl. unfold kLowMemEnd in *. lia.
      + exact (HnG (nt_wr_G _ _ _ Hw)).
    - intros cid pos a Hin Hr [Hw | Hw]; [|exact Hw]. exfalso.
      destruct (frames_bounds segs B LAWS lyc Sc W memc mdc cid pos HAR Hin) as (F4096 & Fce & _).
      pose proof (fs_frame_bytes_nonneg cid) as Hfs.
      destruct Hr as [Hr | Hr]; unfold in_zr, frame_rng in Hr; cbn [fst snd] in Hr; [lia|].
      pose proof (shadow_range_end (frame_addr lyc cid pos) (fs_frame_bytes cid) Hfs) as Hse.
      assert (Hd : (frame_addr lyc cid pos + fs_frame_bytes cid) / 8 <= 2 ^ 47 / 8) by (apply Z.div_le_mono; lia).
      unfold shadow_addr, SHADOW_OFF in *. change (2 ^ 47 / 8) with (2 ^ 44) in Hd. lia. }
  split; [exact (mo_le_refl MT MTL Sc)|].
  exact HtwF.
Qed.

(* The S_ONLINE tail: check_state_online at the jump's state (notice's entry sp, ra, gp, tp and callee-saved
   registers), at the world nt_B2 Bw n, through the leaf bridge lifted into the G journal. *)
Lemma ntstate_online : forall STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
    regsT memT mdT,
  @nt_ctx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB ->
  TI.n_kind n = TC.N_STATE -> TI.n_state n = TC.S_ONLINE ->
  @W_journalG.ajournal_gx rc tfib_sink_head segs B TG.G_HARNESS_B 0 [] STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
    memT mdT k ->
  nt_KA W memc memT (nt_Zs regs Bw n) ->
  tw_at TMAP_B (aview segs (w_H W) memT) (nt_B2 Bw n) ->
  aregs_preserved regs regsT -> YK11.getr regsT 1 = YK11.getr regs 1 ->
  YK11.getr regsT 3 = YK11.getr regs 3 -> YK11.getr regsT 4 = YK11.getr regs 4 ->
  SRr segs W (mkCfg (@YK11.mkst fx regsT (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) memT (YK11.seg_rom segs)) mdT)
    (@transport_notice_post fx rc B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc k regs n Bw Bw').
Proof.
  intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regsT memT mdT
    HC Ek Hst HJ KAT HtwT HPT RT1 RT3 RT4.
  destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
    as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
  pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo
    Hhi HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
  pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
  assert (FS : NOTICE_STK = 8240) by reflexivity.
  destruct (nt_m_state timg_B Fr Bw n Bw' Ek Hm) as (_ & _ & Hon & _).
  pose proof (Hon Hst) as HMo.
  assert (RT2 : YK11.getr regsT (Z_to_bv 5 2) = YK11.getr regs (Z_to_bv 5 2))
    by exact (HPT 2 ltac:(unfold acallee_saved; lia)).
  assert (Hsp1 : spZ regsT = spZ regs) by exact (f_equal bv_unsigned RT2).
  assert (Hsp2 : bv_unsigned (YK11.getr regsT (Z_to_bv 5 2)) = spZ regs) by exact (f_equal bv_unsigned RT2).
  eapply SRr_mono.
  { eapply (@gx_call_leaf fx rc tfib_sink_head segs B TG.G_HARNESS_B STK sp0 FP ly S W0 mem0 md0 own lyc Sc W
      memT mdT k _ _ _ HJ).
    intros memS HJS.
    apply (@LB.decode_leafb_journal fx rc tfib_sink_head B LAWS W regsT memT STK sp0 FP ly S W0 memS
      md0 own lyc Sc mdT k (spZ regs - sp0) LSOc.CHECK_STATE_ONLINE None []
      (fun _ => Bw' = nt_B2 Bw n) HJS).
    - rewrite Hsp1. lia.
    - replace (spZ regs - sp0) with (spZ regs - 16 - sp0 + 1 * 16) by lia. rewrite Z_mod_plus_full. exact Hm16.
    - lia.
    - unfold ESTACK. lia.
    - exact (eq_ind_r YK0s.ret_ok Hra RT1).
    - exact (eq_trans RT3 Hgp).
    - exact (eq_trans RT4 Htp).
    - intros a Ha. inversion Ha.
    - intros HPRE.
      pose proof (HONL fx) as LF.
      unfold transport_leaf_at, LSO.transport_check_state_online_cg in LF.
      specialize (LF lyc Sc W regsT memT mdT (spZ regs - NOTICE_STK) (nt_B2 Bw n) Bw' HPRE).
      cbv zeta in LF. unfold AKA.off_stk in LF. rewrite Hsp2 in LF.
      apply LF; clear LF.
      + exact (ntstate_tw_csw W memT _ HtwT).
      + exact HMo.
      + exact (@LB.decode_leafb_stk_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W memT
          mdT k (spZ regs - NOTICE_STK) (spZ regs) HJS ltac:(lia) ltac:(lia)).
      + unfold LSOc.CHECK_STATE_ONLINE_FRAME. lia.
      + left. unfold LSOc.CHECK_STATE_ONLINE_FRAME, TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI. lia.
      + exact (@LB.decode_leafb_rng_journal rc tfib_sink_head B STK sp0 FP ly S W0 memS md0 own lyc Sc W memT
          mdT k (spZ regs - LSOc.CHECK_STATE_ONLINE_FRAME) LSOc.CHECK_STATE_ONLINE_FRAME HJS
          ltac:(unfold LSOc.CHECK_STATE_ONLINE_FRAME; lia) ltac:(lia)).
      + rewrite LSOc.check_state_online_e2_at.
        apply ntstate_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia.
      + rewrite LSOc.check_state_online_e1_at.
        apply ntstate_rng_hull; unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI; lia. }
  intros W2 c2 _ (-> & regs2 & mem2 & md2 & -> & HJ2 & HP2 & _ & HK2 & HG2 & HX).
  assert (Htw2 : tw_at TMAP_B (aview segs (w_H W) mem2) Bw').
  { rewrite HX. apply (ntstate_tw_leaf W memT mem2 _ (spZ regsT) HtwT); [|exact HK2].
    rewrite Hsp1. unfold TG.G_HARNESS_B_HI, ESTACK. lia. }
  exact (ntstate_close STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB regs2 _ mem2 md2
    HC HJ2 (ntstate_KA_leaf W memc memT mem2 regs Bw n _ KAT Hsp1 HK2 HG2) Htw2
    (aregs_preserved_trans regs regsT regs2 HPT HP2) RT1).
Qed.

(* ------------------------------------------------------------------ *)
(* Tactics of the walk                                                 *)
(* ------------------------------------------------------------------ *)

(* U42 when the path knows 0 <= g < 16. *)
Ltac ntstate_u42 :=
  lazymatch goal with E42 : ew ?Ex 42 = Z_to_bv 64 (TB_GOT + 12 * ?g) |- _ =>
    assert (U42 : bv_unsigned (ew Ex 42) = TB_GOT + 12 * g)
      by (rewrite E42; apply unsigned_lit_small; unfold TB_GOT; lia) end.

(* The atoms of the current valuation En (ntstate_envf), under fixed names. *)
Ltac ntstate_facts En :=
  repeat match goal with
  | H : bv_unsigned (ew _ 2) = spZ _ |- _ => clear H
  | H : ew _ 1 = YK11.getr _ _ |- _ => clear H
  | H : ew _ 11 = Z_to_bv 64 _ |- _ => clear H
  | H : bv_unsigned (ew _ 11) = _ |- _ => clear H
  | H : ew _ 32 = _ |- _ => clear H
  | H : ew _ 33 = _ |- _ => clear H
  | H : ew _ 34 = _ |- _ => clear H
  | H : ew _ 35 = _ |- _ => clear H
  | H : ew _ 36 = _ |- _ => clear H
  | H : ew _ 37 = _ |- _ => clear H
  | H : ew _ 42 = _ |- _ => clear H
  | H : bv_unsigned (ew _ (A_OBJ 13)) = _ |- _ => clear H
  | H : bv_unsigned (ew _ 254) = _ |- _ => clear H
  | H : bv_unsigned (ew _ 42) = _ |- _ => clear H
  end;
  match goal with
  | HEIx : img_env _ _ En, Elo0 : forall j, (j < 43)%nat -> ew En j = ew (nt_E ?regs ?NB ?Bw) j,
    H110 : YK11.getr ?regs _ = w64 ?p |- _ =>
    destruct (ntstate_envf En regs NB Bw p HEIx Elo0 H110 ltac:(lia))
      as (Usp & E1r & E11 & U11 & E32 & E33 & E34 & E35 & E36 & E37 & E42 & U13 & U13n)
  end;
  try ntstate_u42.

(* After a run: the valuation of HS (the run's extK of fresh atoms) named, Elo / Ed for it, its atoms. *)
Ltac ntstate_env :=
  let Ex := lazymatch goal with
    | HS : st_ok_pi _ _ ?Ex _ _ |- _ => Ex
    | HS : OSSVerify.Proofs.libdiginet.fuzz_transport.lib.Reusable.YP0l.st_ok _ ?Ex _ _ |- _ => Ex end in
  let Elo' := fresh "Elo" in let Ed' := fresh "Ed" in
  lazymatch goal with
  | Elo0 : forall j, (j < 43)%nat -> ew _ j = ew ?Eb j, Ed0 : ed _ = ed ?Eb |- _ =>
    assert (Elo' : forall j, (j < 43)%nat -> ew Ex j = ew Eb j)
      by (intros j Hj; repeat rewrite ew_ewset_other by lia; exact (Elo0 j Hj));
    assert (Ed' : ed Ex = ed Eb) by exact Ed0;
    clear Elo0 Ed0
  end;
  rename Elo' into Elo; rename Ed' into Ed;
  let En := fresh "E" in set (En := Ex) in *; clearbody En;
  ntstate_facts En.

(* The facts that name a region's base, rewritten in H. *)
Ltac ntstate_rw H :=
  repeat match goal with
  | U : bv_unsigned (ew _ 2) = spZ _ |- _ => progress rewrite U in H
  | U : bv_unsigned (ew _ 11) = _ |- _ => progress rewrite U in H
  | U : bv_unsigned (ew _ 254) = TB_GOT |- _ => progress rewrite U in H
  | U : bv_unsigned (ew _ (A_OBJ 13)) = TB_GOT |- _ => progress rewrite U in H
  | U : bv_unsigned (ew _ 42) = _ |- _ => progress rewrite U in H
  end.

(* The write rights of a run: GOT's regions (bytes of G), the notice's region (no window), the frame. *)
Ltac ntstate_awr :=
  lazymatch goal with |- awr_ok_x ?Ex ?rs ?Gx ?XO ?OUT ?stk ?sp0q ?fp ?b0 ?bc ?lyq ?ownq =>
    let rs' := eval vm_compute in rs in change (awr_ok_x Ex rs' Gx XO OUT stk sp0q fp b0 bc lyq ownq) end;
  repeat first
    [ apply awr_ok_x_nil
    | apply awr_ok_x_cons_g;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ntstate_rw Ha;
        apply nt_inG_GOT; unfold TB_GOT in *; lia | ]
    | apply awr_ok_x_cons;
      [ let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha;
        cbn [YP09.r_base YP09.r_wlo YP09.r_whi base_val] in Ha; ntstate_rw Ha;
        left; split; [unfold awr_byte; left; lia | lia] | ] ].

(* A window of the walk's regions lies in the bytes the walk may change. *)
Ltac ntstate_zs :=
  let Ek := lazymatch goal with H : TI.n_kind _ = TC.N_STATE |- _ => H end in
  first
  [ left; lia
  | right; unfold notice_wr; left; split; [exact Ek|]; right; unfold twb_fld, TW.A_GOT_n; lia
  | right; unfold notice_wr; left; split; [exact Ek|]; left; split;
      [unfold TC.TRANS_MAX; lia | unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ; lia] ].

(* After a run: the model and the machine state named, the kept bytes, the valuation. *)
Ltac ntstate_post mdo mdn msn KAo KAn mat HF HFr HG :=
  set (mdn := with_vm_backing (m_vm_lazy mdo) mat mdo) in *; clearbody mdn; clear mat;
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msn end;
  lazymatch type of KAo with nt_KA ?W ?memc _ ?Zs =>
    assert (KAn : nt_KA W memc (ms_mem msn) Zs) by
      (apply (nt_KA_run _ _ W memc _ _ _ KAo HFr HG); intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(ntstate_rw Hx; ntstate_zs)) end;
  clear HF HFr HG KAo;
  ntstate_env.

(* After the last run: from the memory at the bne mB to the end only the frame changes, so the world nt_B2 Bw n is
   kept. *)
Ltac ntstate_fin mdo KAo Htwo msF mdF KAF HtwF mat HF HFr HG :=
  let mB := lazymatch type of Htwo with tw_at _ (aview _ _ (ms_mem ?m)) _ => m end in
  set (mdF := with_vm_backing (m_vm_lazy mdo) mat mdo) in *; clearbody mdF; clear mat;
  lazymatch goal with |- SRr _ _ (mkCfg ?m _) _ => rename m into msF end;
  let KAT := fresh "KAT" in
  lazymatch type of KAo with nt_KA ?W ?memc _ (nt_Zs ?regs ?Bw ?n) =>
    assert (KAT : nt_KA W (ms_mem mB) (ms_mem msF) (nt_Wn regs)) by
      (apply (nt_KA_run _ _ W (ms_mem mB) _ _ _ (nt_KA_refl _ _ _) HFr HG); intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(ntstate_rw Hx; unfold nt_Wn; lia));
    assert (KAF : nt_KA W memc (ms_mem msF) (nt_Zs regs Bw n)) by
      (apply (nt_KA_run _ _ W memc _ _ _ KAo HFr HG); intros b wlo whi x Hin Hx; cbv beta;
       nt_win Hin Hx ltac:(ntstate_rw Hx; ntstate_zs));
    pose proof (nt_tw_Wn W (ms_mem mB) (ms_mem msF) regs _ ltac:(unfold TG.G_HARNESS_B_HI; lia) Htwo KAT) as HtwF
  end;
  clear HF HFr HG KAT;
  ntstate_env.

(* ------------------------------------------------------------------ *)
(* The arm                                                             *)
(* ------------------------------------------------------------------ *)

Lemma nt_state : @nt_path fx rc B MT TC.N_STATE NT_STATE.
Proof.
intros STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB E ms md
  HC Ek HS HEI Elo Ed SHOK HJ KA0.
destruct (nt_basics B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB HC)
  as (HAR & Hwin & Hsp & Hce & Hm16 & Hp4096 & Hp47 & Hp8 & Hoffp & Hrd).
pose proof HC as [HCELLS HNCELLS LAWS MTL HGX HGE HDESK HLOST HDATA HACK HONL HJc Hra Hra4 Hgp Htp H11 Hsp16 Hlo Hhi
    HNT HTF HRO Htw Hm HAP HDT Hev HNB HNBL HK0 HK4 HK8 HK12 HK64 HK68].
pose proof asan_consts as (C1 & C2 & C3 & C4 & C5).
assert (FS : NOTICE_STK = 8240) by reflexivity.
unfold decode_off_win in Hoffp.
destruct (nt_m_state timg_B Fr Bw n Bw' Ek Hm) as (Hmax & Hnn & Hon & Hoff).
pose proof (TWL.u_at_range Bw TW.A_GOT_n 4) as R37. change (8 * Z.of_nat 4) with 32 in R37.
pose proof (TWL.u_at_range NB 4 4) as R34. change (8 * Z.of_nat 4) with 32 in R34.
pose proof (TWL.u_at_range NB 8 4) as R35. change (8 * Z.of_nat 4) with 32 in R35.
pose proof (TWL.u_at_range NB 12 4) as R36. change (8 * Z.of_nat 4) with 32 in R36.
assert (Gg : TW.GOT_n Bw = bv_swrap 32 (TW.u_at Bw TW.A_GOT_n 4)) by reflexivity.
ntstate_facts E.
(* the world and the notice's bytes at the arm's entry *)
pose proof (nt_tw_Wn W memc (ms_mem ms) regs Bw ltac:(unfold TG.G_HARNESS_B_HI; lia) Htw KA0) as Htw0.
assert (HNB0 : garr8 segs (mrestrict (w_H W) (ms_mem ms)) p (map DSpec.bz NB)).
{ apply (nt_garr8_keep W memc (ms_mem ms) (nt_Wn regs) p _ KA0 HNB).
  rewrite length_map, HNBL. intros a Ha. split; [lia|]. unfold nt_Wn. lia. }
(* GOT.n's region *)
pose proof (nt_add E _ _ (nt_reg_fld 13 37) HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts nt_ss_jr] in HS2.
specialize (HS2 ltac:(cbn [ms_mem restrict];
  exact (nt_fld_ok W (ms_mem ms) E Bw 13 37 0 ltac:(rewrite U13; lia) ltac:(lia) ltac:(unfold TW.SZ_GOT; lia)
    E37 Htw0))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|exact I];
  unfold extent_disjoint, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite Usp, U13; unfold TB_GOT; lia)).
rename HS2 into HS.
(* the notice's first 16 bytes *)
assert (DG : p + 16 <= TB_GOT \/ TB_GOT + 4 <= p).
{ apply (ntstate_apart_iv p TB_GOT 4 ltac:(lia)). intros x Hx.
  assert (Hw : notice_wr Bw n x)
    by (unfold notice_wr; left; split; [exact Ek | right; unfold twb_fld, TW.A_GOT_n; lia]).
  pose proof (proj1 (HAP x Hw)) as H. unfold NTC_SIZE in H. exact H. }
pose proof (nt_add E _ _ nt_reg_p HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
specialize (HS2 ltac:(cbn [ms_mem restrict];
  exact (nt_preg_ok E _ p NB E11 ltac:(lia) ltac:(lia) E33 E34 E35 E36 HNB0 HNBL))).
specialize (HS2 ltac:(cbn [all_disjoint]; split; [|split; [|exact I]];
  unfold extent_disjoint, nt_reg_p, nt_reg_fld, nt_reg_frame;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val]; rewrite ?Usp, ?U11, ?U13; unfold TB_GOT in *; lia)).
rename HS2 into HS.
pose proof (nt_facts_set E _ _ (nt_facts_g 13 TB_GOT) HS
  (nt_facts_g_ok E (spZ regs) p 13 TB_GOT Usp U11 E32 U13 ltac:(lia) Hsp16 ltac:(lia) Hp8
    ltac:(unfold TB_GOT; reflexivity))) as HS2.
clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
pose proof (@paj_run_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B HGX 0 [])
  as RUN.
pose proof (@paj_run_to_x fx rc tfib_sink_head transportb_listing PL_transportb PI_transportb B LAWS TG.G_HARNESS_B
  HGX 0 []) as RUNTO.
pose proof (paj_branch (fx := fx) (PI := PI_transportb)) as BR.
pose proof (paj_ret_at (fx := fx) (PL := PL_transportb) (PI := PI_transportb)) as RET.
pose proof (nt_KA_mono W memc _ _ _ (nt_Wn_Zs regs Bw n) KA0) as KA. clear KA0.
(* run 1: the jump, a6 = GOT, g = GOT.n, a0 = p + 4, to `blt 15, g` *)
paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
{ ntstate_awr. }
ntstate_post md md1 ms1 KA KA1 mat HF HFr HG.
psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
- (* 15 < GOT.n: the log is full; GOT.n + 1 *)
  rewrite (ntstate_br15 _ _ E37 R37), <- Gg in Hc. apply Z.ltb_lt in Hc. rename Hc into Hhi15.
  (* run 2: the increment, to `blt` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md1 md2 ms2 KA1 KA2 mat HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { rewrite (nt_ovf_br _ 37 _ E37 R37) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc. }
  rewrite (nt_ovf_br _ 37 _ E37 R37) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hinc.
  (* run 3: the store of GOT.n + 1, the shadow check of p + 4, n->state, to `bne` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md2 md3 ms3 KA2 KA3 mat HF HFr HG.
  pose proof (st_ok_pi_region_nth _ _ (restrict (w_H W) ms3) 1 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF. destruct RGF as (_ & _ & _ & HCH).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _]. rewrite ?U13n in HCH.
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem ms3) (TB_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte (TW.GOT_n Bw + 1) 4 j)).
  { intros j Hj. rewrite (nt_chunk_aview W (ms_mem ms3) _ TB_GOT 0 4 _ (Z.of_nat j) HCH ltac:(lia)). f_equal.
    rewrite Gg. exact (nt_inc_bytes _ 37 _ j E37 R37 Hinc Hj). }
  assert (HB2 : nt_B2 Bw n = TW.set_GOT_n Bw (TW.GOT_n Bw + 1)).
  { unfold nt_B2, nt_B1.
    rewrite (proj2 (Z.ltb_ge (TW.GOT_n Bw) TC.TRANS_MAX) ltac:(unfold TC.TRANS_MAX; lia)). reflexivity. }
  assert (Htw3 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms3)) (nt_B2 Bw n)).
  { rewrite HB2. unfold TW.set_GOT_n, TW.A_GOT_n.
    apply (nt_tw_set4 W memc (ms_mem ms3) Bw TW.OFF_GOT TB_GOT TW.SZ_GOT 0 (TW.GOT_n Bw + 1) Htw TMAP_B_GOT);
      [lia | unfold TW.SZ_GOT; lia | exact HV4 |].
    intros x Hx Hn. apply (proj1 KA3).
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + apply (ntstate_notzs regs Bw n x Ek ltac:(unfold TG.G_HARNESS_B_HI; lia) Hx); [intros Hg'; lia | lia]. }
  clear HCH HV4.
  pose proof (nt_drop _ _ _ [nt_reg_frame] HS ltac:(cbn [ss_mem nt_reg_frame]; submem_tac)
    ltac:(vm_compute; reflexivity)) as HSd.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSd. rename HSd into HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* n->state <> S_ONLINE: the epilogue and `ret` *)
    rewrite (ntstate_br_ne _ NB E34) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rewrite HK4 in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ntstate_awr. }
    ntstate_fin md3 KA3 Htw3 msF mdF KAF HtwF mat HF HFr HG.
    assert (HBw : Bw' = nt_B2 Bw n) by (apply Hoff; unfold TC.S_ONLINE; exact Hc).
    rewrite <- HBw in HtwF.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite E1r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) _ _ msF regs (nt_vals NB Bw) HS).
      - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
               | rewrite Ed; reflexivity].
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC HJ KAF HtwF HPF RF1 mat').
  + (* n->state = S_ONLINE: ra loaded back, sp = sp + 16, the tail jump to check_state_online *)
    rewrite (ntstate_br_ne _ NB E34) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rewrite HK4 in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ntstate_awr. }
    ntstate_fin md3 KA3 Htw3 msF mdF KAF HtwF mat HF HFr HG.
    pmkst HS.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1
      ltac:(cbn [sv_denot]; rewrite E1r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3
      ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
              Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4
      ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
              Z_to_bv_bv_unsigned; reflexivity).
    assert (HPT : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) _ _ msF regs (nt_vals NB Bw) HS).
      - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
               | rewrite Ed; reflexivity].
      - vm_compute. reflexivity. }
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) mm rom) mdx) Q) end.
    exact (ntstate_online STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC Ek ltac:(unfold TC.S_ONLINE; exact Hc) HJ KAF HtwF HPT RT1 RT3 RT4).
- (* GOT.n <= 15: the record GOT.t[GOT.n], then GOT.n + 1 *)
  rewrite (ntstate_br15 _ _ E37 R37), <- Gg in Hc. apply Z.ltb_ge in Hc.
  assert (Hg : 0 <= TW.GOT_n Bw < 16) by (pose proof (Hnn ltac:(unfold TC.TRANS_MAX; lia)); lia).
  clear Hc. ntstate_u42.
  pose proof (st_ok_pi_add_fact _ _ _ 42 (mkAF TB_GOT (TB_GOT + 180) 2) HS
    ltac:(unfold afact_ok; cbn [af_lo af_hi af_al2]; rewrite U42; change (2 ^ 2) with 4; unfold TB_GOT;
      split; [lia|]; split; [|lia];
      replace (6180704 + 12 * TW.GOT_n Bw) with ((1545176 + 3 * TW.GOT_n Bw) * 4) by lia; apply Z_mod_mult)) as HS2.
  clear HS. nt_norm HS2. rename HS2 into HS.
  (* the record's shadow entry *)
  assert (RA0 : range_addressable (aview segs (w_H W) memc) SHADOW_OFF (TB_GOT + 12 * TW.GOT_n Bw + 4) 12)
    by exact (ntstate_rec_ra lyc Sc W memc mdc (TW.GOT_n Bw) HNCELLS HAR Hg).
  assert (RA1 : range_addressable (aview segs (w_H W) (ms_mem ms1)) SHADOW_OFF (TB_GOT + 12 * TW.GOT_n Bw + 4) 12).
  { apply (nt_ra_kept W memc (ms_mem ms1) _ 12 (nt_Zs regs Bw n) RA0 KA1).
    intros x Hx. pose proof (Z.div_pos x 8 ltac:(unfold TB_GOT in *; lia) ltac:(lia)) as D1.
    assert (D2 : x / 8 < 2 ^ 44) by (apply Z.div_lt_upper_bound; unfold TB_GOT in *; lia).
    unfold SHADOW_OFF. split; [lia|]. intros Hz.
    destruct (nt_Zs_far regs Bw n _ Hce Hz) as [Hf | Hf]; unfold TB_M, TB_GOT in Hf; lia. }
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    assert (SHOK2 : sh_ok segs NT_Bx ntstate_SH Ex (mrestrict (w_H W) (ms_mem ms1))) end.
  { pose proof SHOK as SH1. unfold sh_ok, NT_SH in SH1. apply Forall_inv in SH1.
    unfold sh_ok, ntstate_SH. constructor; [exact SH1 | constructor; [|constructor]].
    apply (shent_ok_of_range segs (w_H W) (ms_mem ms1) _ NT_Bx 42 _ 12 (TB_GOT + 12 * TW.GOT_n Bw) 4 16 RA1).
    - unfold U, NT_Bx. cbn [sv_denot]. rewrite E32, Z.add_0_r, Z_to_bv_bv_unsigned.
      rewrite unsigned_lit_small by (unfold SHADOW_OFF; lia). reflexivity.
    - unfold U. cbn [sv_denot]. rewrite Z.add_0_r, Z_to_bv_bv_unsigned. exact U42.
    - lia.
    - lia.
    - intros x Hx. cbn [Z.min Z.max] in Hx. unfold SHADOW_OFF, TB_GOT in *. lia. }
  clear SHOK RA0. rename SHOK2 into SHOK.
  (* run 2: the shadow check of p + 4, to `bgeu g, 16` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md1 md2 ms2 KA1 KA2 mat HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { rewrite (ntstate_br_geu _ _ E37 R37 ltac:(rewrite <- Gg; lia)) in Hc. discriminate Hc. }
  clear Hc.
  (* run 3: 12 g and ~(GOT + 4), to the pointer-overflow `bltu` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md2 md3 ms3 KA2 KA3 mat HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { rewrite (ntstate_br_ptr _ _ E37 R37 ltac:(rewrite <- Gg; lia) U13n) in Hc. discriminate Hc. }
  clear Hc.
  (* run 4: a2 = GOT + 12 g + 4, to 0x83544 *)
  paj_run_to_tok RUNTO HS HJ SHOK YC4b.Bspan (AF_notice + 0x128).
  { ntstate_awr. }
  ntstate_post md3 md4 ms4 KA3 KA4 mat HF HFr HG.
  (* a2 pinned to atom 42 + 4, the record's region added *)
  lazymatch type of HS with st_ok_pi _ _ ?Ex _ _ =>
    nt_reg HS (Z_to_bv 5 12) (sv_denot Ex (SOff 42 4)) Q12
      ltac:(apply (ntstate_addr _ _ E37 R37 ltac:(rewrite <- Gg; lia) U13n ltac:(rewrite E42, Gg; reflexivity))) end.
  pose proof (nt_pin _ _ _ (Z_to_bv 5 12) (SOff 42 4) HS ltac:(cbn [ms_regs restrict]; exact Q12)
    ltac:(vm_compute; reflexivity)) as HS2.
  clear HS Q12. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2. rename HS2 into HS.
  assert (DR : p + 16 <= TB_GOT + 12 * TW.GOT_n Bw + 4 \/ TB_GOT + 12 * TW.GOT_n Bw + 4 + 12 <= p).
  { apply (ntstate_apart_iv p _ 12 ltac:(lia)). intros x Hx.
    assert (Hw : notice_wr Bw n x)
      by (unfold notice_wr; left; split; [exact Ek | left; split;
            [unfold TC.TRANS_MAX; lia | unfold twb_fld, TW.A_GOT_t_state, TW.GOT_t_ESZ; lia]]).
    pose proof (proj1 (HAP x Hw)) as H. unfold NTC_SIZE in H. exact H. }
  pose proof (nt_add _ _ _ nt_reg_rec HS ltac:(vm_compute; reflexivity)) as HS2. clear HS.
  cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS2.
  specialize (HS2 ltac:(cbn [ms_mem restrict]; exact (ntstate_rec_ok _ _ _ U42 Hg))).
  specialize (HS2 ltac:(cbn [all_disjoint]; repeat split;
    unfold extent_disjoint, nt_reg_rec; cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
    rewrite ?Usp, ?U11, ?U13n, ?U42; unfold TB_GOT in *; lia)).
  rename HS2 into HS.
  (* run 5: the record's three words, the increment, to `blt` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md4 md5 ms5 KA4 KA5 mat HF HFr HG.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  { rewrite (nt_ovf_br _ 37 _ E37 R37) in Hc. apply Z.eqb_eq in Hc. exfalso. apply Hmax. exact Hc. }
  rewrite (nt_ovf_br _ 37 _ E37 R37) in Hc. apply Z.eqb_neq in Hc. rename Hc into Hinc.
  (* run 6: the store of GOT.n + 1, the shadow check of p + 4, n->state, to `bne` *)
  paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
  { ntstate_awr. }
  ntstate_post md5 md6 ms6 KA5 KA6 mat HF HFr HG.
  (* the stored bytes: the record's three words and GOT.n *)
  pose proof (st_ok_pi_region_nth _ _ (restrict (w_H W) ms6) 0 _ HS eq_refl) as RGR.
  cbn [ms_mem restrict] in RGR. destruct RGR as (_ & _ & _ & HCR).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCR. rewrite U42 in HCR.
  apply Forall_cons_iff in HCR as [HC12 HCR]. apply Forall_cons_iff in HCR as [HC8 HCR].
  apply Forall_cons_iff in HCR as [HC4 _].
  pose proof (st_ok_pi_region_nth _ _ (restrict (w_H W) ms6) 2 _ HS eq_refl) as RGF.
  cbn [ms_mem restrict] in RGF. destruct RGF as (_ & _ & _ & HCH).
  cbn [YP09.r_base YP09.r_chunks base_val] in HCH.
  apply Forall_cons_iff in HCH as [HCH _]. rewrite ?U13n in HCH.
  lazymatch type of E34 with ew ?Ex _ = _ =>
    pose proof (nt_sext32 Ex 34 _ E34 R34) as D34; pose proof (nt_sext32 Ex 35 _ E35 R35) as D35;
    pose proof (nt_sext32 Ex 36 _ E36 R36) as D36 end.
  change (bv_swrap 32 (TW.u_at NB 4 4)) with (TW.s32_at NB 4) in D34. rewrite HK4 in D34.
  change (bv_swrap 32 (TW.u_at NB 8 4)) with (TW.s32_at NB 8) in D35. rewrite HK8 in D35.
  change (bv_swrap 32 (TW.u_at NB 12 4)) with (TW.s32_at NB 12) in D36. rewrite HK12 in D36.
  assert (HV1 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem ms6) (TB_GOT + 12 * TW.GOT_n Bw + 4 + Z.of_nat j) =
    Some (YO0f.le_byte (TI.n_state n) 4 j)).
  { intros j Hj. rewrite (nt_chunk_aview W (ms_mem ms6) _ _ 4 4 _ (Z.of_nat j) HC4 ltac:(lia)). f_equal.
    exact (ntstate_byte4 _ _ _ j D34 Hj). }
  assert (HV2 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem ms6) (TB_GOT + 12 * TW.GOT_n Bw + 8 + Z.of_nat j) =
    Some (YO0f.le_byte (TI.n_old n) 4 j)).
  { intros j Hj. rewrite (nt_chunk_aview W (ms_mem ms6) _ _ 8 4 _ (Z.of_nat j) HC8 ltac:(lia)). f_equal.
    exact (ntstate_byte4 _ _ _ j D35 Hj). }
  assert (HV3 : forall j, (j < 4)%nat -> aview segs (w_H W) (ms_mem ms6) (TB_GOT + 12 * TW.GOT_n Bw + 12 + Z.of_nat j) =
    Some (YO0f.le_byte (TI.n_reason n) 4 j)).
  { intros j Hj. rewrite (nt_chunk_aview W (ms_mem ms6) _ _ 12 4 _ (Z.of_nat j) HC12 ltac:(lia)). f_equal.
    exact (ntstate_byte4 _ _ _ j D36 Hj). }
  assert (HV4 : forall j, (j < 4)%nat ->
    aview segs (w_H W) (ms_mem ms6) (TB_GOT + 0 + Z.of_nat j) = Some (YO0f.le_byte (TW.GOT_n Bw + 1) 4 j)).
  { intros j Hj. rewrite (nt_chunk_aview W (ms_mem ms6) _ TB_GOT 0 4 _ (Z.of_nat j) HCH ltac:(lia)). f_equal.
    rewrite Gg. exact (nt_inc_bytes _ 37 _ j E37 R37 Hinc Hj). }
  assert (HB2 : nt_B2 Bw n = TW.set_GOT_n (TW.set_GOT_t_reason (TW.set_GOT_t_old
      (TW.set_GOT_t_state Bw (TW.GOT_n Bw) (TI.n_state n)) (TW.GOT_n Bw) (TI.n_old n)) (TW.GOT_n Bw) (TI.n_reason n))
      (TW.GOT_n Bw + 1)).
  { unfold nt_B2, nt_B1.
    rewrite (proj2 (Z.ltb_lt (TW.GOT_n Bw) TC.TRANS_MAX) ltac:(unfold TC.TRANS_MAX; lia)). reflexivity. }
  assert (Htw6 : tw_at TMAP_B (aview segs (w_H W) (ms_mem ms6)) (nt_B2 Bw n)).
  { rewrite HB2.
    apply (ntstate_tw4 (aview segs (w_H W) memc) _ Bw (TW.GOT_n Bw) _ _ _ _ Htw Hg HV1 HV2 HV3 HV4).
    intros x Hx Hr Hn. apply (proj1 KA6).
    + pose proof (TMAP_B_hull x Hx) as Hh. unfold TG.G_HARNESS_B_LO, TG.G_HARNESS_B_HI in Hh. lia.
    + exact (ntstate_notzs regs Bw n x Ek ltac:(unfold TG.G_HARNESS_B_HI; lia) Hx (fun _ => Hr) Hn). }
  clear HC12 HC8 HC4 HCH HV1 HV2 HV3 HV4 D34 D35 D36.
  pose proof (nt_drop _ _ _ [nt_reg_frame] HS ltac:(cbn [ss_mem nt_reg_frame]; submem_tac)
    ltac:(vm_compute; reflexivity)) as HSd.
  clear HS. cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HSd. rename HSd into HS.
  psrr_branch_tok RUN BR HS SHOK YC4b.Bspan.
  + (* n->state <> S_ONLINE: the epilogue and `ret` *)
    rewrite (ntstate_br_ne _ NB E34) in Hc. apply negb_true_iff, Z.eqb_neq in Hc. rewrite HK4 in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ntstate_awr. }
    ntstate_fin md6 KA6 Htw6 msF mdF KAF HtwF mat HF HFr HG.
    assert (HBw : Bw' = nt_B2 Bw n) by (apply Hoff; unfold TC.S_ONLINE; exact Hc).
    rewrite <- HBw in HtwF.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RF1
      ltac:(cbn [sv_denot]; rewrite E1r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    assert (HPF : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) _ _ msF regs (nt_vals NB Bw) HS).
      - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
               | rewrite Ed; reflexivity].
      - vm_compute. reflexivity. }
    eapply (RET W _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity)).
    intros mat'.
    exact (nt_close B MT STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC HJ KAF HtwF HPF RF1 mat').
  + (* n->state = S_ONLINE: ra loaded back, sp = sp + 16, the tail jump to check_state_online *)
    rewrite (ntstate_br_ne _ NB E34) in Hc. apply negb_false_iff, Z.eqb_eq in Hc. rewrite HK4 in Hc.
    paj_run_tok RUN HS HJ SHOK YC4b.Bspan.
    { ntstate_awr. }
    ntstate_fin md6 KA6 Htw6 msF mdF KAF HtwF mat HF HFr HG.
    pmkst HS.
    nt_reg HS (1%bv : bv 5) (YK11.getr regs 1) RT1
      ltac:(cbn [sv_denot]; rewrite E1r, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (3%bv : bv 5) (YK11.getr regs 3) RT3
      ltac:(cbn [sv_denot]; rewrite (Elo 3%nat ltac:(lia)), (nt_E_reg regs NB Bw 3 3%bv eq_refl), Z.add_0_r,
              Z_to_bv_bv_unsigned; reflexivity).
    nt_reg HS (4%bv : bv 5) (YK11.getr regs 4) RT4
      ltac:(cbn [sv_denot]; rewrite (Elo 4%nat ltac:(lia)), (nt_E_reg regs NB Bw 4 4%bv eq_refl), Z.add_0_r,
              Z_to_bv_bv_unsigned; reflexivity).
    assert (HPT : aregs_preserved regs (ms_regs msF)).
    { apply (aregs_preserved_of_st_ok segs (w_H W) _ _ msF regs (nt_vals NB Bw) HS).
      - split; [intros j Hj; rewrite (Elo j ltac:(lia)); unfold nt_E; apply Eimg_low; unfold A_TEXT; lia
               | rewrite Ed; reflexivity].
      - vm_compute. reflexivity. }
    lazymatch goal with |- SRr ?sg ?Wx (mkCfg (?mk ?rg _ ?mm ?rom) ?mdx) ?Q =>
      change (SRr sg Wx (mkCfg (mk rg (Z_to_bv 64 LSOc.CHECK_STATE_ONLINE) mm rom) mdx) Q) end.
    exact (ntstate_online STK sp0 FP ly S W0 mem0 md0 own lyc Sc W memc mdc k regs p n Fr Bw Bw' NB
      (ms_regs msF) (ms_mem msF) mdF HC Ek ltac:(unfold TC.S_ONLINE; exact Hc) HJ KAF HtwF HPT RT1 RT3 RT4).
Qed.
End state.
