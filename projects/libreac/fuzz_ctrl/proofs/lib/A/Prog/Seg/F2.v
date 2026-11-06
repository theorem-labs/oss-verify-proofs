(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 2065 of its 2181 lines of code are new or changed and 895 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F3.v, with its module paths and module names changed; 1051 of its 1229 lines of code are new or changed and 2003 lines of the source are left out. *)
(* Segment F2 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, patched image A): 0x81da4-0x81dcc, 11 instructions.
     81da4 mv s7,a0; 81da8 bnez a0,81db0 (taken: a0 = Phi, the block F1's allocation returned, Phi <> 0, so the
     abort edge 81dac `bnez s2,82bf4` is not reached); 81db0 sltiu s6,s2,50; 81db4 sd s4,216(s1);
     81db8 sd s6,232(s1); 81dbc beqz s2,81e54 (len = 0: to F4's second entry 0x81e54);
     81dc0 mv a0,s7; mv a1,s4; mv a2,s2; 81dcc jal checked_memcpy@0x52008 (returns to 0x81dd0, F3's entry).
   The checked memcpy (Section Hypothesis MCPY, asan_memcpy_c.v) copies the frame body (len bytes of the input at
   p + body) into the block Phi; both ranges are addressable, and it writes only Phi and its own stack window
   [sp - 2224, sp). Its contract asks for mem_inv, which no cut carries, so the len > 0 run is made on the
   normalized memory (MemNorm.evt_normalize from FRA's ro_agree) and carried back by mem_rel (f2_run).

   Cuts (all official, SlotInv.v push 14D): entry Inv_A81da4_at, exits Inv_A81dd0_at (b5_CUT at 0x81dd0) and
   Inv_A81e54_at. FRA / ENT move across the len = 0 run by F1.f1_fra_spill and across the len > 0 run by
   Tac_slot.sl_fr_cl / ent_munch (after a Theorem Labs lane's R8.v); the b5_CUT carry b5_C is produced by f2_b5C from the
   entry's FLSH, IFS and FLC, the block's AH (b5_PH's placement), FRA (b5_FS, b5_KN: f2_b5fs, f2_b5kn), s7 = Phi,
   the [A + 232] store and the copied record; b5_PF at 0x81e54 is vacuous (flen = 0, so t_big and t_8819 are
   false). The instruction-level run lemmas are a Theorem Labs lane's (a working branch 6175db87b6e).
   rule 24: no function proved. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFP RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import asan_memcpy_c reac_ctrl_parse_c reac_ctrl_kind_name_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require reac_ctrl_identity_fragment_c asan_stack_malloc_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_slot Tac_b5 F1.
(* last, so that munch / wmono / outside / bytes_at of this file are lib/Lib's, the ones the callee contract and
   the transport lemmas of Tac_slot and RcAsanFPLib speak about *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes.
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.
Module LE := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Exec.
(* the step tactics leave the compare of 0x81db0 in lib/Lib's PropExec, which a later import shadows *)
Module LP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.PropExec.
Module LM := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module SMC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.asan_stack_malloc_c.
Module FP := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.RcAsanFP.
Module FGA := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.reac_ctrl_identity_fragment_c.

(* ---- frame-loop model facts (the ubsan twin's Tac_u4.v) ---- *)

Lemma f2_byte_nn : forall b : byte, 0 <= bv_unsigned b.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. lia. Qed.

Lemma f2_fL_nn : forall inp c, 0 <= f_L inp c.
Proof.
  intros inp c. unfold f_L, inb, RcIdentModel.bz.
  pose proof (f2_byte_nn (RcIdentModel.nthb inp (Z.to_nat c))).
  pose proof (f2_byte_nn (RcIdentModel.nthb inp (Z.to_nat (c + 1)))).
  destruct (2 <=? f_left inp c); lia.
Qed.

Lemma f2_fc_range : forall inp j, 0 <= fc inp j <= nlen inp.
Proof.
  intros inp j. assert (Hn : 0 <= nlen inp) by (unfold nlen; lia).
  induction j as [|j IH]; cbn [fc].
  - unfold c0. lia.
  - pose proof (f2_fL_nn inp (fc inp j)). unfold f_next, f_body, f_len, f_h, f_left. lia.
Qed.

Lemma f2_len_range : forall inp j,
  0 <= t_len inp j /\ 0 <= t_body inp j /\ t_body inp j + t_len inp j <= nlen inp.
Proof.
  intros inp j. pose proof (f2_fc_range inp j). pose proof (f2_fL_nn inp (fc inp j)).
  unfold t_len, t_body, f_len, f_body, f_h, f_left. lia.
Qed.

Lemma f2_phi_len : forall inp j, length (t_phi inp j) = Z.to_nat (t_len inp j).
Proof.
  intros inp j. pose proof (f2_len_range inp j) as (H1 & H2 & H3).
  unfold t_phi, f_phi. fold (t_len inp j). fold (t_body inp j).
  rewrite length_firstn, length_skipn. unfold nlen in H3. lia.
Qed.

(* ---- the image's pages, the bytes above them ---- *)

(* Every address of [2^21, GT) lies on a page the image maps: the last LOAD segment runs to GT. *)
Lemma f2_img_page : forall a, 2 ^ 21 <= a < AC.GT -> AC.a_on_img_page a.
Proof.
  intros a Ha.
  assert (H : existsb (fun s => (Z.of_N (seg_base s) / 4096 * 4096 <=? 2 ^ 21) &&
                                (AC.GT <=? (Z.of_N (seg_base s) + Z.of_N (seg_size s) + 4095) / 4096 * 4096))
                rsegs = true) by (vm_compute; reflexivity).
  apply existsb_exists in H. destruct H as (s & Hin & Hc).
  apply andb_true_iff in Hc. destruct Hc as (H1 & H2). apply Z.leb_le in H1. apply Z.leb_le in H2.
  exists s. split; [exact Hin | lia].
Qed.

Lemma f2_segs_below : forallb (fun s => Z.of_N (seg_base s) + Z.of_N (seg_size s) <=? AC.GT) rsegs = true.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_wx : MemNorm.wx_apart rsegs = true.
Proof. vm_compute. reflexivity. Qed.

(* No segment of the image holds a byte at or above GT. *)
Lemma f2_noseg : forall x, AC.GT <= x -> find_segment rsegs x 1 = None.
Proof.
  intros x Hx. destruct (find_segment rsegs x 1) as [s|] eqn:E; [|reflexivity].
  exfalso. destruct (kb_find_segment rsegs x 1 s E) as (Hin & H1 & H2).
  pose proof f2_segs_below as Hb. rewrite forallb_forall in Hb. specialize (Hb s Hin).
  apply Z.leb_le in Hb. lia.
Qed.

Lemma f2_ro_hi : forall x, AC.GT <= x < 2 ^ 64 -> ro_addr rsegs (wa x) = false.
Proof.
  intros x Hx. assert (HG : AC.GT = 6283264) by reflexivity.
  unfold ro_addr. rewrite wa_unsigned by lia. rewrite (f2_noseg x) by lia. reflexivity.
Qed.

(* A writable byte at or above GT is present: wview there is the overlay byte. *)
Lemma f2_rd_of_wr : forall m a, AC.GT <= a < 2 ^ 64 -> writable_at rsegs m a ->
  exists b, mrd rsegs m (wa a) = Some b.
Proof.
  intros m a Ha Hw. assert (HG : AC.GT = 6283264) by reflexivity.
  unfold mrd, wa.
  destruct (m (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
  exfalso. unfold writable_at, wview in Hw. rewrite E in Hw.
  rewrite MState.unsigned_lit in Hw by lia. rewrite (f2_noseg a) in Hw by lia. apply Hw. reflexivity.
Qed.

(* A byte of application memory is outside a write set all of whose ranges are application memory, when it is a
   shadow byte (the two ranges are apart). *)
Lemma f2_sh_out : forall W x, all_app W -> in_shadow x -> outside W x.
Proof.
  induction W as [|[lo hi] W IH]; intros x HW Hx; cbn [outside]; [exact I|].
  destruct HW as (Happ & HW). split; [|exact (IH x HW Hx)].
  intros Hin. pose proof (Happ x Hin) as Ha.
  unfold app_mem, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG, APPMEM_END in *. lia.
Qed.

(* ---- small arithmetic facts of the branches and of the compare ---- *)

Lemma f2_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

Lemma f2_eqb0 : forall x, 0 < x < 2 ^ 64 -> bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0) = false.
Proof. intros x Hx. unfold bv_eqb. rewrite !MState.unsigned_lit by lia. apply Z.eqb_neq. lia. Qed.

Lemma f2_sltiu : forall x i, 0 <= x < 2 ^ 64 -> bv_wrap 64 i = 50 ->
  LP.v_sltiu (Z_to_bv 64 x) i = Z_to_bv 64 (b2z (x <? 50)).
Proof.
  intros x i Hx Hi. unfold LP.v_sltiu. rewrite MState.unsigned_lit by lia. rewrite Hi.
  destruct (x <? 50); reflexivity.
Qed.

Lemma f2_c_bytes : forall m A c, rw_cells rsegs m A [c] -> bytes_at rsegs m A (cbytes c).
Proof.
  intros m A c ((_ & Hb) & _). cbn [cells_bytes] in Hb. rewrite app_nil_r in Hb. exact Hb.
Qed.

(* ---- the normalized memory: the premises move to it, its results move back ---- *)

Lemma f2_mrd_norm : forall m a, MemNorm.ro_agree rsegs m -> mrd rsegs (MemNorm.normalize rsegs m) a = mrd rsegs m a.
Proof. intros m a H. symmetry. exact (MemNorm.mrd_rel rsegs m _ a (MemNorm.mem_rel_normalize rsegs m H)). Qed.

Lemma f2_wview_norm : forall m a, ro_addr rsegs a = false ->
  wview rsegs (MemNorm.normalize rsegs m) a = wview rsegs m a.
Proof. intros m a E. unfold wview, MemNorm.normalize. rewrite E. reflexivity. Qed.

Lemma f2_stk_norm : forall m lo hi, MemNorm.ro_agree rsegs m ->
  (forall x, lo <= x < hi -> ro_addr rsegs (wa x) = false) ->
  stk rsegs m lo hi -> stk rsegs (MemNorm.normalize rsegs m) lo hi.
Proof.
  intros m lo hi HRO HE (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite (f2_wview_norm m (wa a) (HE a Ha)). exact Hv.
  - exists b. rewrite (f2_mrd_norm m (wa a) HRO). exact Hb.
Qed.

Lemma f2_wr_norm : forall m a n, (forall i, 0 <= i < n -> ro_addr rsegs (wa (a + i)) = false) ->
  wr_at rsegs m a n -> wr_at rsegs (MemNorm.normalize rsegs m) a n.
Proof.
  intros m a n HE (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros i Hi.
  rewrite (f2_wview_norm m (wa (a + i)) (HE i Hi)). exact (H i Hi).
Qed.

Lemma f2_rw_norm : forall m A cs, MemNorm.ro_agree rsegs m ->
  (forall i, 0 <= i < Z.of_nat (cells_size cs) -> ro_addr rsegs (wa (A + i)) = false) ->
  rw_cells rsegs m A cs -> rw_cells rsegs (MemNorm.normalize rsegs m) A cs.
Proof.
  intros m A cs HRO HE ((Hwf & Hb) & Hw). split.
  - split; [exact Hwf | exact (MemNorm.bytes_at_normalize rsegs m A _ HRO Hb)].
  - exact (f2_wr_norm m A _ HE Hw).
Qed.

Lemma f2_addr_norm : forall m p n, MemNorm.ro_agree rsegs m ->
  addressable m p n -> addressable (MemNorm.normalize rsegs m) p n.
Proof.
  intros m p n HRO (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b.
  rewrite (f2_mrd_norm m _ HRO). split; [exact Hb | exact Hok].
Qed.

Lemma f2_shrw_norm : forall m, MemNorm.ro_agree rsegs m -> shadow_rw m -> shadow_rw (MemNorm.normalize rsegs m).
Proof.
  intros m HRO H a Ha.
  assert (HE : ro_addr rsegs (wa a) = false).
  { apply f2_ro_hi. unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in Ha.
    assert (HG : AC.GT = 6283264) by reflexivity. lia. }
  destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite (f2_wview_norm m (wa a) HE). exact Hv.
  - exists b. rewrite (f2_mrd_norm m (wa a) HRO). exact Hb.
Qed.

Lemma f2_ac_norm : forall m, MemNorm.ro_agree rsegs m -> asan_cells m -> asan_cells (MemNorm.normalize rsegs m).
Proof.
  intros m HRO H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end;
    (eapply MemNorm.bytes_at_normalize; [exact HRO | eassumption]).
Qed.

(* back from the normalized run: mem_rel m m0 moves the results to m *)
Lemma f2_stk_of : forall m m0 lo hi, MemNorm.mem_rel rsegs m m0 -> stk rsegs m0 lo hi -> stk rsegs m lo hi.
Proof.
  intros m m0 lo hi HR (H0 & H1 & H). split; [exact H0|]. split; [exact H1|]. intros a Ha.
  destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite <- (MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (MemNorm.ro_false_of_wview rsegs m m0 (wa a) HR Hv)).
    exact Hv.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_rw_of : forall m m0 A cs, MemNorm.mem_rel rsegs m m0 -> rw_cells rsegs m0 A cs -> rw_cells rsegs m A cs.
Proof.
  intros m m0 A cs HR ((Hwf & Hb) & Hw). split.
  - split; [exact Hwf | exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 A _ HR) Hb)].
  - exact (MemNorm.wr_at_rel rsegs m m0 A _ HR Hw).
Qed.

Lemma f2_addr_of : forall m m0 p n, MemNorm.mem_rel rsegs m m0 -> addressable m0 p n -> addressable m p n.
Proof.
  intros m m0 p n HR (H0 & H1 & H2 & H). split; [exact H0|]. split; [exact H1|]. split; [exact H2|].
  intros i Hi. destruct (H i Hi) as (Hap & b & Hb & Hok). split; [exact Hap|]. exists b.
  rewrite (MemNorm.mrd_rel rsegs m m0 _ HR). split; [exact Hb | exact Hok].
Qed.

Lemma f2_shrw_of : forall m m0, MemNorm.mem_rel rsegs m m0 -> shadow_rw m0 -> shadow_rw m.
Proof.
  intros m m0 HR H a Ha. destruct (H a Ha) as (Hv & b & Hb). split.
  - rewrite <- (MemNorm.wview_rel_rw rsegs m m0 (wa a) HR (MemNorm.ro_false_of_wview rsegs m m0 (wa a) HR Hv)).
    exact Hv.
  - exists b. rewrite (MemNorm.mrd_rel rsegs m m0 (wa a) HR). exact Hb.
Qed.

Lemma f2_ac_of : forall m m0, MemNorm.mem_rel rsegs m m0 -> asan_cells m0 -> asan_cells m.
Proof.
  intros m m0 HR H. unfold asan_cells in *.
  repeat match goal with Hc : _ /\ _ |- _ => destruct Hc end.
  repeat match goal with |- _ /\ _ => split end;
    (apply (proj2 (MemNorm.bytes_at_rel rsegs m m0 _ _ HR)); eassumption).
Qed.

Lemma f2_bytes_of : forall m m0 a bs, MemNorm.mem_rel rsegs m m0 -> bytes_at rsegs m0 a bs -> bytes_at rsegs m a bs.
Proof. intros m m0 a bs HR H. exact (proj2 (MemNorm.bytes_at_rel rsegs m m0 a bs HR) H). Qed.

Lemma f2_addr_sub : forall m p n q k, addressable m p n -> p <= q -> 0 <= k -> q + k <= p + n ->
  addressable m q k.
Proof.
  intros m p n q k (H0 & H1 & H2 & H) Hq Hk Hqk. split; [lia|]. split; [lia|]. split; [lia|].
  intros i Hi. replace (q + i) with (p + (q - p + i)) by lia. apply H. lia.
Qed.

(* n present and writable bytes at a are a byte cell of n junk bytes. *)
Lemma f2_rw_ex : forall m a (n : nat), 0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
  (forall x, a <= x < a + Z.of_nat n -> writable_at rsegs m x /\ exists b, mrd rsegs m (wa x) = Some b) ->
  exists junk, rw_cells rsegs m a [CB n junk].
Proof.
  intros m a n Ha Hn H.
  assert (HS : stk rsegs m a (a + Z.of_nat n)) by (split; [lia|]; split; [lia|]; exact H).
  destruct (stk_carve rsegs m a (a + Z.of_nat n) n HS ltac:(lia)) as (_ & junk & HJ).
  replace (a + Z.of_nat n - Z.of_nat n) with a in HJ by lia. exists junk. exact HJ.
Qed.

(* ---- the run of the segment on the normalized memory ---- *)

(* len <> 0: the two spills, then the checked memcpy; the write set is the two spill words, the block Phi and the
   callee's stack window [sp - 2224, sp). Reads: the input bytes [S, S + len), the block, the window. *)
Lemma f2_evt : asan_memcpy_contract ->
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte)
         (spv A phi S N lo : Z) (src junk j1 j2 : list byte),
    sp = Z_to_bv 64 spv -> s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 N -> s4 = Z_to_bv 64 S ->
    0 < phi -> 0 < N -> 0 <= S -> N <= 2 ^ 40 -> RT_HI <= phi ->
    phi + N <= lo -> S + N <= lo -> (S + N <= phi \/ phi + N <= S) ->
    HIGHMEM_BEG <= lo -> lo + ASAN_MEMCPY_K <= spv -> spv <= A -> A + 416 <= APPMEM_END ->
    spv <= APPMEM_END -> spv mod 16 = 0 ->
    bytes_at rsegs m S src -> length src = Z.to_nat N ->
    rw_cells rsegs m phi [CB (Z.to_nat N) junk] ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    addressable m S N -> addressable m phi N -> end_in_app S N -> end_in_app phi N ->
    app_mem (S + 7) -> app_mem (phi + 7) ->
    stk rsegs m lo spv -> asan_cells m -> shadow_rw m -> mem_inv rsegs m ->
    LE.evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word)
                         (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x81dd0) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 phi)
                       a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 N) s3 (Z_to_bv 64 S) s5
                       (Z_to_bv 64 (b2z (N <? 50))) (Z_to_bv 64 phi) s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x81dd0) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m m' /\
         wmono rsegs m m' /\ stk rsegs m' lo spv /\
         rw_cells rsegs m' phi [CB (Z.to_nat N) src] /\ bytes_at rsegs m' S src /\
         asan_cells m' /\ shadow_rw m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 (b2z (N <? 50)))))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros MCPY ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv A phi S N lo src junk j1 j2 -> -> -> -> -> Hph0 HN0 HS0 HN40 HRT Hphlo HSlo Hdj
    Hlo Hlosp HspA HA64 HspE Hal HbS HLs HRWd HR216 HR232 HAS HAD HES HED HAPS HAPD HST HAC HSW HMI.
  assert (HK : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HRTH : RT_HI = 0xa9578) by reflexivity.
  assert (HAWW : all_app [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N);
                          (spv - ASAN_MEMCPY_K, spv)]).
  { cbn [all_app app_ivl]. split; [|split; [|split; [|split; [|exact I]]]].
    - intros x Hx. unfold app_mem. right. lia.
    - intros x Hx. unfold app_mem. right. lia.
    - intros x Hx. destruct HAD as (_ & _ & _ & HAb). destruct (HAb (x - phi) ltac:(lia)) as (Hap & _).
      replace (phi + (x - phi)) with x in Hap by lia. exact Hap.
    - intros x Hx. unfold app_mem. right. lia. }
  pose proof (munch_refl [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + N); (spv - ASAN_MEMCPY_K, spv)] m)
    as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.                                              (* 81da4 mv s7,a0 *)
  step. if_true_by (f2_neqb0 phi ltac:(lia)).         (* 81da8 bnez a0,81db0 *)
  step.                                              (* 81db0 sltiu s6,s2,50 *)
  lazymatch goal with
  | |- context [LP.v_sltiu (Z_to_bv 64 N) ?i] =>
      rewrite (f2_sltiu N i ltac:(lia) ltac:(vm_compute; reflexivity))
  end.
  step.                                              (* 81db4 sd s4,216(s1) *)
  step.                                              (* 81db8 sd s6,232(s1) *)
  (* the runtime cells, the shadow map and the two addressable ranges move across the two spill stores *)
  pose proof (fl_asan_cells _ m _ HAC MU
                ltac:(intros x Hx; cbn [outside]; repeat split; try exact I; lia)) as HAC1.
  pose proof (fl_shadow_rw _ m _ HSW MU WM
                ltac:(intros x Hx; exact (f2_sh_out _ x HAWW Hx))) as HSW1.
  pose proof (fl_addressable _ m _ S N HAS MU
                ltac:(intros x Hx; exact (f2_sh_out _ x HAWW Hx))) as HAS1.
  pose proof (fl_addressable _ m _ phi N HAD MU
                ltac:(intros x Hx; exact (f2_sh_out _ x HAWW Hx))) as HAD1.
  step. if_false_by (f2_eqb0 N ltac:(lia)).           (* 81dbc beqz s2,81e54 *)
  step. step. step.                                  (* mv a0,s7; mv a1,s4; mv a2,s2 *)
  step.                                              (* 81dcc jal checked_memcpy *)
  unfold asan_memcpy_contract in MCPY.
  eapply evt_cut.
  { eapply MCPY with (src := src) (junk := junk) (lo := lo);
      rewrite ?MState.unsigned_lit by lia.
    - exact HbS.
    - exact HLs.
    - exact HRWd.
    - destruct Hdj as [Hd|Hd]; [right; left; lia | right; right; lia].
    - lia.
    - exact HAS1.
    - exact HAD1.
    - exact HES.
    - exact HED.
    - right. split; [exact HAPS | exact HAPD].
    - right. lia.
    - left. lia.
    - left. lia.
    - exact HST.
    - lia.
    - lia.
    - lia.
    - exact HAC1.
    - exact HSW1.
    - assumption. }
  intros ms' PO. unfold asan_memcpy_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MUc & WMc & MI' & STc & RWc & HBc & AC' & SW').
  subst ms'.
  assert (Ephi : bv_unsigned (Z_to_bv 64 phi) = phi) by (apply LM.unsigned_lit; lia).
  assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply LM.unsigned_lit; lia).
  assert (Esp : bv_unsigned (Z_to_bv 64 spv) = spv) by (apply LM.unsigned_lit; lia).
  assert (ES : bv_unsigned (Z_to_bv 64 S) = S) by (apply LM.unsigned_lit; lia).
  rewrite Ephi in MUc, RWc. rewrite EN in MUc, RWc. rewrite Esp in MUc, STc. rewrite ES in HBc.
  rewrite (LM.ret_pc_even 0x81dd0) by (first [reflexivity | lia]).
  apply evt_done. do 15 eexists. split; [reflexivity|].
  split.
  { apply (munch_trans _ m _ m' MU). eapply munch_weaken; [|exact MUc].
    intros x (O1 & O2 & O3 & O4 & _). cbn [outside].
    split; [exact O3|]. split; [exact O4 | exact I]. }
  split; [exact (wmono_trans rsegs _ _ m' WM WMc)|].
  split; [exact STc|].
  split; [exact RWc|].
  split; [exact HBc|].
  split; [exact AC'|].
  split; [exact SW'|].
  split.
  { apply (bytes_at_transport rsegs _ _ m' _ _ (f2_c_bytes _ _ _ HR216) MUc).
    cbn [disjoint_from Cells.cbytes]. rewrite ?length_le8. cbn [length].
    repeat split; try exact I; lia. }
  { apply (bytes_at_transport rsegs _ _ m' _ _ (f2_c_bytes _ _ _ HR232) MUc).
    cbn [disjoint_from Cells.cbytes]. rewrite ?length_le8. cbn [length].
    repeat split; try exact I; lia. }
Qed.

(* len = 0: the same two spills, then 0x81dbc goes to 0x81e54; no call, so this run is made on the real memory. *)
Lemma f2z_evt :
  forall (ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (A phi S : Z) (j1 j2 : list byte),
    s1 = Z_to_bv 64 A -> a0 = Z_to_bv 64 phi -> s2 = Z_to_bv 64 0 -> s4 = Z_to_bv 64 S ->
    0 < phi < 2 ^ 64 -> 0 <= A -> A + 416 <= 2 ^ 64 ->
    rw_cells rsegs m (A + 216) [CB 8 j1] -> rw_cells rsegs m (A + 232) [CB 8 j2] ->
    LE.evt rsegs
      (fun ms' => exists m' : word -> option byte,
         ms' = MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 phi) a1 a2 a3 a4 a5 a6 a7
                       (Z_to_bv 64 0) s3 (Z_to_bv 64 S) s5 (Z_to_bv 64 1) (Z_to_bv 64 phi)
                       s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 0x81e54) fc None m' (seg_rom rsegs) /\
         munch [(A + 216, A + 224); (A + 232, A + 240)] m m' /\ wmono rsegs m m' /\
         bytes_at rsegs m' (A + 216) (le8 (Z_to_bv 64 S)) /\
         bytes_at rsegs m' (A + 232) (le8 (Z_to_bv 64 1)))
      (MS (mkR ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x81da4) fc None m (seg_rom rsegs)).
Proof.
  intros ra0 sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m A phi S j1 j2 -> -> -> -> Hph HA0 HA64 HR216 HR232.
  pose proof (munch_refl [(A + 216, A + 224); (A + 232, A + 240)] m) as MU.
  pose proof (wmono_refl rsegs m) as WM.
  step.
  step. if_true_by (f2_neqb0 phi ltac:(lia)).
  step.
  lazymatch goal with
  | |- context [LP.v_sltiu (Z_to_bv 64 0) ?i] =>
      rewrite (f2_sltiu 0 i ltac:(lia) ltac:(vm_compute; reflexivity))
  end.
  cbn [Z.ltb Z.compare b2z].
  step.
  step.
  step. if_true.
  apply evt_done. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|].
  split; [exact (f2_c_bytes _ _ _ HR216) | exact (f2_c_bytes _ _ _ HR232)].
Qed.

(* ---- the SR bridge: run on the normalized memory, carry the result back to the real memory ---- *)

Section R.
Context {fx : FPState}.

Lemma f2_run : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None -> MemNorm.ro_agree rsegs mem ->
  LE.evt rsegs
    (fun ms => exists R pc' mem0', ms = MS R fp_regs pc' fp_csr None mem0' (seg_rom rsegs) /\ K R pc' mem0')
    (MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None (MemNorm.normalize rsegs mem) (seg_rom rsegs)) ->
  (forall R pc' mem0' mem' regs' md', K R pc' mem0' -> MemNorm.mem_rel rsegs mem' mem0' ->
     MemNorm.ro_same rsegs mem mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HRO HE HK.
  apply (sl_run_lib regs pc mem md
    (fun R pc' mem' => exists mem0', K R pc' mem0' /\ MemNorm.mem_rel rsegs mem' mem0' /\
                       MemNorm.ro_same rsegs mem mem') P Hh).
  - eapply LE.evt_mono; [exact (MemNorm.evt_normalize rsegs _ _ _ _ _ _ _ _ f2_wx HRO HE)|].
    intros ms (s0 & (R & pc' & mem0' & -> & HKR) & Hrel & Hro).
    destruct Hrel as (HRg & HFg & HPg & HSg & HVg & HCg & HMg & HRel).
    destruct ms as [R1 F1 pc1 svc1 rv1 fc1 m1 ro1]. cbn in HRg, HFg, HPg, HSg, HVg, HCg, HMg, HRel, Hro.
    exists R1, pc1, m1. split.
    + unfold MS. rewrite HFg, HSg, HVg, HCg, HMg. reflexivity.
    + exists mem0'. split; [rewrite HRg, HPg; exact HKR|]. split; [exact HRel | exact Hro].
  - intros R pc' mem' regs' md' (mem0' & HKR & HRel & Hro) Hreg Hmat.
    exact (HK R pc' mem0' mem' regs' md' HKR HRel Hro Hreg Hmat).
Qed.

End R.

(* ---- more generic helpers ---- *)

Lemma f2_stk_sub : forall m lo hi a b, stk rsegs m lo hi -> lo <= a -> b <= hi -> a <= b -> stk rsegs m a b.
Proof.
  intros m lo hi a b (H0 & H1 & H) Ha Hb Hab. split; [lia|]. split; [lia|]. intros x Hx. apply H. lia.
Qed.

Lemma f2_dj_sub3 : forall (W1 W2 W3 : list ivl) X, fp_dj (W1 ++ W2 ++ W3) X -> fp_dj (W1 ++ W2) X.
Proof.
  intros W1 W2 W3 X H. unfold fp_dj in *.
  apply Forall_app in H as (H1 & H2). apply Forall_app in H2 as (H2 & _).
  apply Forall_app. split; [exact H1 | exact H2].
Qed.

Lemma f2_rd_of_bytes : forall m a bs x, bytes_at rsegs m a bs -> a <= x < a + Z.of_nat (length bs) ->
  exists b, mrd rsegs m (wa x) = Some b.
Proof.
  intros m a bs x (H0 & H1 & H) Hx.
  assert (Hi : (Z.to_nat (x - a) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (x - a)) Hi) as E.
  replace (a + Z.of_nat (Z.to_nat (x - a))) with x in E by lia.
  destruct (nth_error bs (Z.to_nat (x - a))) as [b|] eqn:En;
    [exists b; rewrite E; first [reflexivity | exact En]|].
  apply nth_error_None in En. lia.
Qed.

(* every address of a read-only segment is below GT, so a run that writes only above GT keeps ro_agree *)
Lemma f2_ro_keep : forall m m' W, ro_agree rsegs m -> munch W m m' ->
  (forall x, 0 <= x < 6283264 -> outside W x) -> ro_agree rsegs m'.
Proof.
  intros m m' W HRO MU HW a Ha.
  pose proof (u64_range a) as Har.
  assert (Hlt : bv_unsigned a < 6283264).
  { unfold ro_addr in Ha. destruct (find_segment rsegs (bv_unsigned a) 1) as [s|] eqn:E; [|discriminate].
    destruct (kb_find_segment rsegs (bv_unsigned a) 1 s E) as (Hin & H1 & H2).
    pose proof f2_segs_below as Hb. rewrite forallb_forall in Hb. specialize (Hb s Hin).
    apply Z.leb_le in Hb. assert (HG : AC.GT = 6283264) by reflexivity. lia. }
  unfold mrd. rewrite (MU a (HW (bv_unsigned a) ltac:(lia))). exact (HRO a Ha).
Qed.

(* application memory is two intervals more than 2^43 apart, so a point between two application bytes that are
   nearer to each other than that is application memory too. *)
Lemma f2_app_mid : forall a b x, app_mem a -> app_mem b -> a <= x <= b -> b - a <= 2 ^ 43 -> app_mem x.
Proof. intros a b x. unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END. lia. Qed.


(* ---- byte helpers for the exit cuts ---- *)

(* A byte outside the write set reads the same. *)
Lemma f2_mb_keep : forall W m m' x, munch W m m' -> 0 <= x < 2 ^ 64 -> outside W x ->
  mbyte rsegs m' x = mbyte rsegs m x.
Proof.
  intros W m m' x MU Hx Ho. unfold mbyte. rewrite (MU (Z_to_bv 64 x)); [reflexivity|].
  rewrite MState.unsigned_lit by lia. exact Ho.
Qed.

(* A spill read off register 9 is at the base A of the cut (both hold s1; the spill's base is in range). *)
Lemma f2_sq : forall regs m A off v, spill regs m off v -> rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  A + 416 <= 2 ^ 64 -> 0 <= off <= 408 -> q64 m (A + off) v.
Proof.
  intros regs m A off v (A' & H9' & Hq) H9 HA HAb Hoff.
  assert (Hqb : 0 <= A' + off /\ A' + off + Z.of_nat (length (le8 (Z_to_bv 64 v))) <= 2 ^ 64)
    by (unfold q64 in Hq; exact (bytes_at_bound rsegs m (A' + off) _ Hq)).
  rewrite length_le8 in Hqb.
  assert (HAA : A' = A).
  { pose proof (rg_eq64 regs 9 A' A H9' H9) as Hm. rewrite !Z.mod_small in Hm by lia. exact Hm. }
  subst A'. exact Hq.
Qed.

Lemma f2_nth_firstn : forall (l : list byte) k i, (i < k)%nat -> nth_error (firstn k l) i = nth_error l i.
Proof.
  induction l as [|x l IH]; intros k i H; [rewrite firstn_nil; reflexivity|].
  destruct k as [|k]; [lia|]. destruct i as [|i]; [reflexivity|]. cbn. apply IH. lia.
Qed.

Lemma f2_nth_skipn : forall (l : list byte) k i, nth_error (skipn k l) i = nth_error l (k + i).
Proof.
  induction l as [|x l IH]; intros k i; destruct k as [|k]; cbn; try reflexivity.
  - destruct i; reflexivity.
  - apply IH.
Qed.

(* A sub-list of a byte list at A (a Theorem Labs lane's P7.v p7_ba_sub). *)
Lemma f2_ba_sub : forall m A bs k jj, bytes_at rsegs m A bs -> (k + jj <= length bs)%nat ->
  bytes_at rsegs m (A + Z.of_nat k) (firstn jj (skipn k bs)).
Proof.
  intros m A bs k jj (H0 & H1 & H) Hk.
  assert (Hl : length (firstn jj (skipn k bs)) = jj) by (rewrite length_firstn, length_skipn; lia).
  split; [lia|]. split; [rewrite Hl; lia|].
  intros i Hi. rewrite Hl in Hi. rewrite f2_nth_firstn by lia. rewrite f2_nth_skipn.
  replace (A + Z.of_nat k + Z.of_nat i) with (A + Z.of_nat (k + i)) by lia. apply H. lia.
Qed.

(* The first k bytes of a byte list at a. *)
Lemma f2_ba_firstn : forall m a bs k, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn k bs).
Proof.
  intros m a bs k (H0 & H1 & H). split; [exact H0|]. rewrite length_firstn. split; [lia|].
  intros i Hi. rewrite f2_nth_firstn by lia. apply H. lia.
Qed.

(* The record's first 50 bytes, when it has at least 50. *)
Lemma f2_fr50 : forall bs, (50 <= length bs)%nat -> fr50 bs = firstn 50 bs.
Proof.
  intros bs H. unfold fr50. rewrite firstn_app. replace (50 - length bs)%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. reflexivity.
Qed.

(* FSREC (the side-arm FakeStack frame record) moves across a run that writes no byte below GT and no byte of the
   FakeStack (a Theorem Labs lane's R8.v r8_fsrec). *)
Lemma f2_fsrec : forall mem mem' W fr, FSREC fr mem -> munch W mem mem' ->
  (forall x, 0 <= x < AC.GT -> outside W x) ->
  (forall x, AC.a_in_fs AC.ASYMS mem x -> outside W x) ->
  FSREC fr mem'.
Proof.
  intros mem mem' W fr (FS & j & Htp & HFSr & Hj & Hfr & Hflag & Htail) MU Hlow Hinfs.
  assert (HB6 : SMC.fs_B 6 = 4096) by reflexivity.
  assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
  assert (Hfl : SMC.fs_flag FS 6 j = FS + 36352 + j) by (unfold SMC.fs_flag; cbn; lia).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (Hfrv : fr = FS + 6328320 + j * 4096) by (rewrite Hfr; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
  rewrite HM6 in Hj.
  assert (Hin : forall x, FS <= x < FS + AC.FS_SIZE -> outside W x).
  { intros x Hx. apply Hinfs. exists FS. split; [exact HFSr|]. split; [exact Htp | exact Hx]. }
  exists FS, j.
  split.
  { intros k Hk.
    assert (Hx : 0 <= AC.as_tp AC.ASYMS + Z.of_nat k < 6283264)
      by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
    assert (Hm : mem' (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))
                 = mem (Z_to_bv 64 (AC.as_tp AC.ASYMS + Z.of_nat k))).
    { apply MU. rewrite MState.unsigned_lit by lia. apply Hlow. unfold AC.GT. lia. }
    unfold mbyte. rewrite Hm. exact (Htp k Hk). }
  split; [exact HFSr|].
  split; [rewrite HM6; exact Hj|].
  split; [exact Hfr|].
  split.
  { eapply fl_bytes; [exact Hflag | exact MU |]. cbn [length]. intros x Hx. apply Hin. lia. }
  { eapply fl_bytes; [exact Htail | exact MU |]. rewrite length_le8. intros x Hx. apply Hin.
    rewrite HB6 in Hx. lia. }
Qed.

(* The kind-name table KIND_NAME = 0x9e760 (112 bytes, the 14 string pointers) is a registered global of the
   image's RELRO, so FRA's G_img_c gives its bytes and its frame_AG conjunct its addressability. *)
Definition f2_ob_eqb (x y : option byte) : bool :=
  match x, y with Some a, Some b => Z.eqb (bv_unsigned a) (bv_unsigned b) | None, None => true | _, _ => false end.

Lemma f2_ob_eqb_eq : forall x y, f2_ob_eqb x y = true -> x = y.
Proof.
  intros [a|] [b|] H; cbn in H; try discriminate; [|reflexivity].
  apply Z.eqb_eq in H. f_equal. apply bv_eq. exact H.
Qed.

Lemma f2_kn_len : length kind_name_bytes = 112%nat.
Proof. vm_compute. reflexivity. Qed.

Lemma f2_kn_rom : forall i, (i < 112)%nat ->
  seg_rom rsegs (Z_to_bv 64 (KIND_NAME + Z.of_nat i)) = nth_error kind_name_bytes i.
Proof.
  assert (H : forallb (fun i => f2_ob_eqb (seg_rom rsegs (Z_to_bv 64 (KIND_NAME + Z.of_nat i)))
                                          (nth_error kind_name_bytes i)) (seq 0 112) = true)
    by (vm_compute; reflexivity).
  intros i Hi. rewrite forallb_forall in H. apply f2_ob_eqb_eq. apply H. apply in_seq. lia.
Qed.

Lemma f2_kn_ag : In (0x9e760, 112) AF.frame_AG.
Proof. unfold AF.frame_AG. cbn [In]. repeat (first [left; reflexivity | right]). Qed.

Lemma f2_kn_relro : In (0x9e348, 9344) AF.frame_RELRO.
Proof. unfold AF.frame_RELRO. cbn [In]. left. reflexivity. Qed.

Section S.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Local Notation API := (APIf rc).

(* ---- the parts of b5_C that the base gives ---- *)

(* b5_FS from FRA: on the real arm the frame is above FSFREE's side stack (FS + FS_SIZE <= S - SLOT_STACK and
   S - 4096 < sp = fr), so the containment premise is false; on the side arm the frame record puts fr at slot j
   < 256 of class 6, so fr + FRAME_BYTES <= FS + 6328320 + 255 * 4096 + 3136 <= FS + FS_SIZE. The thread word at tp + 8
   is FSFREE's DB, whose cells (DB + 24, DB + 32) are app memory. *)
Lemma f2_b5fs : forall g fr hb regs m md, FRA B APIf ra g fr hb regs m md -> b5_FS fr m.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs m md HFRA.
  destruct (fra_fsfree B APIf ra g fr hb regs m md HFRA)
    as (FS0 & Hw0 & HFS0r & Hok & HGT & Hal & Happ & Hbelow & Hfr6 & DT & TS & C & T & DB & k & HT & Hdj & Hall).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  assert (HFSZ : AC.FS_SIZE = 11571200) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (Htp : 0 <= AC.as_tp AC.ASYMS /\ AC.as_tp AC.ASYMS + 16 <= 2 ^ 64)
    by (unfold AC.as_tp, AC.ASYMS; cbn; lia).
  split.
  - intros FS Hw HFSr Hin.
    assert (E : FS = FS0) by (apply (fsf_wm_uniq m _ FS FS0 Hw Hw0 HFSr HFS0r); lia).
    subst FS0.
    destruct Hloc as [(_ & Hspfr & _) | (_ & _ & _ & Hrec)].
    + exfalso. lia.
    + destruct Hrec as (FS1 & j1 & Hw1 & HFS1r & Hj1 & Hfrj & _).
      assert (E1 : FS1 = FS) by (apply (fsf_wm_uniq m _ FS1 FS Hw1 Hw HFS1r HFSr); lia).
      subst FS1.
      assert (HM6 : SMC.fs_M 6 = 256) by reflexivity.
      assert (Hfrv : fr = FS + 6328320 + j1 * 4096) by (rewrite Hfrj; unfold SMC.fs_frame, SMC.fs_B; cbn; lia).
      rewrite HM6 in Hj1. lia.
  - destruct HT as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & HDB & _).
    exists (bv_unsigned DB).
    split; [exact (bytes_at_le8_word rsegs m _ DB HDB)|].
    pose proof (bv_unsigned_in_range 64 DB) as HDr.
    rewrite Forall_forall in Hall.
    assert (Hin : In (bv_unsigned DB + 24, bv_unsigned DB + 32) (FP.fp_tls (AC.as_tp AC.ASYMS) DT TS C T DB k)).
    { unfold FP.fp_tls. cbn [In]. repeat (first [left; reflexivity | right]). }
    destruct (Hall _ Hin) as (Hlt & Happ32). cbn [fst snd] in Hlt, Happ32.
    pose proof (Happ32 (bv_unsigned DB + 31) ltac:(lia)) as Ha.
    unfold app_mem, APPMEM_END, LOWMEM_END, HIGHMEM_BEG in Ha. split; lia.
Qed.

(* b5_KN from FRA: the table's bytes are the image's RELRO bytes (G_img_c), its 112 bytes a registered global. *)
Lemma f2_b5kn : forall g fr hb regs m md, FRA B APIf ra g fr hb regs m md -> b5_KN m.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g fr hb regs m md HFRA.
  pose proof (proj1 FF) as SEGS.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & _).
  assert (HKN : KIND_NAME = 0x9e760) by reflexivity.
  split.
  - split; [lia|]. rewrite f2_kn_len. split; [lia|].
    intros i Hi. rewrite <- fsf_mbyte_mrd.
    assert (Hin : in_globals AF.frame_RELRO (KIND_NAME + Z.of_nat i)).
    { exists 0x9e348, 9344. split; [exact f2_kn_relro | lia]. }
    pose proof (Hgimg _ Hin) as E. rewrite SEGS in E. rewrite E. apply f2_kn_rom. exact Hi.
  - apply f1_addr_join; [lia | lia | unfold APPMEM_END; lia |].
    intros a Ha. apply HAG. exists 0x9e760, 112. split; [exact f2_kn_ag | lia].
Qed.

(* b5_PH's placement and the 0x81e54 body's placement from the block's AH: the block (phi, a_size len) lies below
   stklo <= sp - FN_STACK, off the FakeStack; the frame is at or above stklo (real arm) or in the FakeStack (side
   arm), so the two are apart. *)
Lemma f2_place : forall g j phi fr regs m md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m md ->
  forall k, 0 < k <= AC.a_size (flen g j) ->
  (phi + k <= fr \/ fr + FRAME_BYTES <= phi) /\
  phi + k <= AC.aspZ regs - FN_STACK /\
  ~ AC.a_in_fs AC.ASYMS m phi.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs m md HFRA k Hk.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as ALAWS.
  destruct (fra_win B APIf ra g fr _ regs m md HFRA) as (Hwlo & _).
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & _).
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ ALAWS _ m md phi (AC.a_size (flen g j)) HAH Hinphi)
    as (_ & Hp4096 & Hend & _ & Hall).
  split; [|split].
  - destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    + left. pose proof (Hreal fr ltac:(lia)) as Hr. lia.
    + destruct (Z_le_gt_dec (phi + k) fr) as [Hl|Hl]; [left; exact Hl|].
      destruct (Z_le_gt_dec (fr + FRAME_BYTES) phi) as [Hr|Hr]; [right; exact Hr|].
      exfalso. destruct (Hall (Z.max phi fr) ltac:(lia)) as (_ & _ & _ & _ & Hnfs).
      exact (Hnfs (Hfs (Z.max phi fr) ltac:(lia))).
  - lia.
  - destruct (Hall phi ltac:(lia)) as (_ & _ & _ & _ & Hnfs). exact Hnfs.
Qed.

Lemma f2_b5ph : forall g j phi fr regs m md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m md ->
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) ->
  b5_PH g j phi fr regs m.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs m md HFRA Hbytes.
  assert (HKF : FGA.REAC_CTRL_IDENTITY_FRAGMENT_K = 4656) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  split; [exact Hbytes|]. split.
  - intros Hlen. destruct (f2_place g j phi fr regs m md HFRA 50 ltac:(unfold AC.a_size; lia))
      as (Hf & Hsp & _).
    split; [exact Hf|]. left. lia.
  - intros Hlen. destruct (f2_place g j phi fr regs m md HFRA 1 ltac:(unfold AC.a_size; lia))
      as (_ & _ & Hnfs). exact Hnfs.
Qed.

(* C5's producer: b5_C at any FRA state of the block (phi, a_size len) from what the F1 / F2 cuts carry (FLSH,
   IFS), the carry FLC, s7 = phi, s2 = len and (long frame) the record's first 50 bytes at phi. *)
Lemma f2_b5C : forall g j phi fr regs m md,
  FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs m md ->
  FLSH g j fr regs m -> IFS g fr j regs m -> FLC fr regs m ->
  rg regs 23 phi -> rg regs 18 (flen g j) -> spill regs m 232 (if t_big (g_in g) j then 0 else 1) ->
  (50 <= flen g j -> bytes_at rsegs m phi (t_g (g_in g) j)) ->
  b5_C g j phi fr regs m.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros g j phi fr regs m md HFRA HFLSH HIFS HFLC H23 H18 H232 Hbytes.
  pose proof HFRA as HF.
  destruct HF as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & _).
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HAE : APPMEM_END = 140737488355328) by reflexivity.
  assert (HA64 : 0 <= A < 2 ^ 64) by (pose proof Hwin as (Hw0 & Hw1 & _); lia).
  destruct HFLSH as ((_ & _ & _ & _ & _ & _ & _ & S248 & _) & _ & _ & S144 & _).
  destruct HFLC as (S256 & S184 & S208 & S64 & S72 & S80 & S272 & S264 & HA72 & HA38 & _).
  destruct (f1_FS_len (g_in g) j) as (_ & L72).
  pose proof HIFS as (_ & (HFG & _) & _).
  split; [exact H23|]. split; [exact H18|].
  split.
  { exists A. split; [exact Hr9|]. split; [exact HA64|].
    split; [|exact (f2_sq regs m A 232 _ H232 Hr9 HA64 ltac:(lia) ltac:(lia))].
    split; [exact (f2_sq regs m A 248 _ S248 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 256 _ S256 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 144 _ S144 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 184 _ S184 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 192 _ S208 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 80 _ S64 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 88 _ S72 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 96 _ S80 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    split; [exact (f2_sq regs m A 272 _ S272 Hr9 HA64 ltac:(lia) ltac:(lia))|].
    exact (f2_sq regs m A 264 _ S264 Hr9 HA64 ltac:(lia) ltac:(lia)). }
  split; [exact (f2_b5ph g j phi fr regs m md HFRA Hbytes)|].
  split.
  { split; [exact HA72|]. split; [exact HA38|]. split; [|exact L72]. exact HFG. }
  split; [exact (f2_b5fs g fr _ regs m md HFRA)|].
  split; [exact (f2_b5kn g fr _ regs m md HFRA)|].
  destruct HIFS as (_ & HFGj & HFSj). split; [exact HFGj | exact HFSj].
Qed.

(* The callee contract of the checked memcpy (0x81dcc), taken on its contract asan_memcpy_c.v. *)
Hypothesis MCPY : asan_memcpy_contract.

(* seg_F2 (S_F2): from F1's exit 0x81da4 through the two spill stores to 0x81e54 (len = 0) or through the checked
   memcpy to 0x81dd0 (len > 0). *)
Lemma seg_F2 : forall j : nat,
  Hat B APIf ra (Inv_A81dd0_at B APIf ra) j -> Hat B APIf ra (Inv_A81e54_at B APIf ra) j ->
  Hat B APIf ra (Inv_A81da4_at B APIf ra) j.
Proof.
  pose proof FRAME_BYTES_val as HFRAMEb. pose proof FRAME_SHADOW_val as HFRAMEs.
  intros j Hexit Hzero g c HInv.
  pose proof (proj1 FF) as SEGS.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT API) as LAWS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hn26 & Hj255 & Ha0 & HHB & HLK & HFC &
                    HFLSH & HINb & H248 & HIFS & HFLC).
  subst c. rewrite SEGS.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HMK : ASAN_MEMCPY_K = 2224) by reflexivity.
  assert (HGTv : AC.GT = 6283264) by reflexivity.
  assert (HHMv : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HAEv : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HRTHv : RT_HI = 0xa9578) by reflexivity.
  assert (HKv : ASAN_K = 0x7fff8000) by reflexivity.
  assert (HNe : flen g j = t_len (g_in g) j) by reflexivity.
  pose proof (f2_len_range (g_in g) j) as (HNnn & Hbody0 & Hbodyn).
  assert (Hgn : g_n g = nlen (g_in g)) by reflexivity.
  assert (Hdec : forall a b (x : Z), (a <= x < b) \/ ~ (a <= x < b)) by (intros; lia).
  pose proof HFRA as HFRAc.
  destruct HFRAc as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  pose proof (AsanRTInv.RT_cells _ _ _ HRT) as HAC0.
  pose proof (AsanRTInv.RT_shadow_rw _ _ _ HRT) as HSW0.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS _ mem md HAH) as Hhigh.
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hstklo2 & Hstkwin).
  destruct (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hapart & _).
  pose proof (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Happfr).
  assert (HA64 : 0 <= A < 2 ^ 64) by (pose proof Hwin as (Hw0 & Hw1 & _); lia).
  assert (Hsp0 : 0 <= sp) by (rewrite <- Haspz; apply u64_range).
  assert (Hfr0 : 0 <= fr).
  { pose proof (bytes_at_bound rsegs mem fr (le8 (Z_to_bv 64 0x41b58ab3)) Hhdr1) as (Hf0 & _). lia. }
  assert (Hfrm8 : fr mod 8 = 0) by (clear - HFRAMEb HFRAMEs Hfrm; Z.div_mod_to_equations; lia).
  rewrite Haspz in Hstklo2, Hstkwin.
  (* the block Phi *)
  assert (HaszN : 0 < AC.a_size (flen g j)) by (unfold AC.a_size; lia).
  assert (Hinphi : In (phi, AC.a_size (flen g j)) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
    by (cbn [hb1 app In]; left; reflexivity).
  destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hinphi)
    as (Hphal & Hph4096 & HphSt & HphEnd & HphAll).
  pose proof (AC.a_laws_block_end _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hinphi HaszN) as HphA7.
  pose proof (AC.a_laws_block_high _ _ _ _ _ LAWS _ mem md phi (AC.a_size (flen g j)) HAH Hinphi) as Hph21.
  assert (HGTph : AC.GT <= phi).
  { destruct (HphAll phi ltac:(lia)) as (_ & _ & _ & Hnp & _).
    destruct (Z_lt_le_dec phi AC.GT) as [Hlt|Hge]; [exfalso; apply Hnp; apply f2_img_page; lia | exact Hge]. }
  assert (Hfrblk : forall x, fr <= x < fr + FRAME_BYTES -> ~ (phi <= x < phi + AC.a_size (flen g j))).
  { intros x Hx Hb. destruct (HphAll x Hb) as (_ & _ & _ & _ & Hnfs).
    destruct Hloc as [(_ & _ & Hreal) | (_ & _ & Hfs & _)].
    - pose proof (Hreal x Hx). lia.
    - exact (Hnfs (Hfs x Hx)). }
  (* the input block: below stklo, apart from Phi *)
  destruct HINb as (HinP0 & HaddrP & HbytesP).
  assert (HIN : forall x, g_p g <= x < g_p g + g_n g ->
            (forall q k, In (q, k) (g_H g) -> 0 <= q /\ q + k <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md) ->
            0 <= x < AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).
  { intros x Hx Hq. pose proof (HinP0 ltac:(lia)) as Hin. destruct (Hq _ _ Hin). lia. }
  assert (HHq : forall q k, In (q, k) (g_H g) -> 0 <= q /\ q + k <= AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md).
  { intros q k Hin.
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md q k HAH (in_or_app _ _ _ (or_intror Hin)))
      as (_ & Hq4 & Hqk & _). lia. }
  assert (HPdj : forall x, g_p g <= x < g_p g + g_n g -> ~ (phi <= x < phi + AC.a_size (flen g j))).
  { intros x Hx Hb. pose proof (HinP0 ltac:(lia)) as Hin.
    pose proof (AC.a_laws_disjoint _ _ _ _ _ LAWS [] (g_H g) mem md phi (AC.a_size (flen g j))
                  (g_p g) (g_n g) HAH Hin) as Hd. lia. }
  (* the two spill words: present and writable in the slot window *)
  assert (HST216 : stk rsegs mem (A + 216) (A + 224))
    by (apply (f2_stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  assert (HST232 : stk rsegs mem (A + 232) (A + 240))
    by (apply (f2_stk_sub mem (g_S g - AF.SLOT_STACK) (g_S g)); [exact Hwin | lia | lia | lia]).
  destruct HST216 as (_ & _ & HST216c). destruct HST232 as (_ & _ & HST232c).
  destruct (f2_rw_ex mem (A + 216) 8 ltac:(lia) ltac:(lia)
              ltac:(intros x Hx; apply HST216c; lia)) as (j1 & HR216).
  destruct (f2_rw_ex mem (A + 232) 8 ltac:(lia) ltac:(lia)
              ltac:(intros x Hx; apply HST232c; lia)) as (j2 & HR232).
  destruct HFC as (Hs224 & H20 & H18).
  destruct HLK as (Hjj & H21 & HOUR).
  (* the shadow of an app byte is not app memory, so no all-app write set touches it *)
  assert (HSHA : forall W x, all_app W -> app_mem x -> outside W (shadow_addr x))
    by (intros W x HW Hx; exact (f2_sh_out W _ HW (shadow_of_app x Hx))).
  assert (HSHlo : forall x, app_mem x -> 0 <= shadow_addr x < 2 ^ 64).
  { intros x Hx. pose proof (in_shadow_range _ (shadow_of_app x Hx)) as R. lia. }
  destruct (Z.eq_dec (flen g j) 0) as [Hz | Hnz].
  - (* ---- len = 0: the two spills, then 0x81e54 ---- *)
    apply (sl_run_lib regs (Z_to_bv 64 0x81da4) mem md
      (fun R pc' mem' => pc' = Z_to_bv 64 0x81e54 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 10 = Z_to_bv 64 phi /\ getr R 18 = Z_to_bv 64 0 /\
         getr R 20 = Z_to_bv 64 (g_p g + t_body (g_in g) j) /\
         getr R 22 = Z_to_bv 64 1 /\ getr R 23 = Z_to_bv 64 phi /\
         munch [(A + 216, A + 224); (A + 232, A + 240)] mem mem' /\ wmono rsegs mem mem' /\
         bytes_at rsegs mem' (A + 216) (le8 (Z_to_bv 64 (g_p g + t_body (g_in g) j))) /\
         bytes_at rsegs mem' (A + 232) (le8 (Z_to_bv 64 1)))
      (Post B APIf ra g) Hhalt).
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply f2z_evt with (A := A) (phi := phi) (S := g_p g + t_body (g_in g) j) (j1 := j1) (j2 := j2).
        - exact Hr9.
        - exact Ha0.
        - rewrite <- Hz, HNe. exact H18.
        - exact H20.
        - lia.
        - lia.
        - lia.
        - exact HR216.
        - exact HR232. }
      { intros ms' (m' & E & MU0 & WM0 & Q216 & Q232).
        eexists _, (Z_to_bv 64 0x81e54), m'. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|].
        split; [exact MU0|]. split; [exact WM0|]. split; [exact Q216 | exact Q232]. }
    + intros R pc' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K10 & K18 & K20 & K22 & K23 &
        MU & WM & Q216 & Q232) Hreg Hmat.
      subst pc'.
      set (W2 := [(A + 216, A + 224); (A + 232, A + 240)]) in MU.
      assert (E2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
      assert (E3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
      assert (E4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
      assert (E8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
      assert (E9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      assert (E19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
      assert (E26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
      assert (HAW2 : all_app W2).
      { subst W2. cbn [all_app app_ivl]. split; [|split; [|exact I]]; intros x Hx; unfold app_mem; right; lia. }
      assert (HRB : forall x, outside W2 x \/ exists b, mrd rsegs mem' (wa x) = Some b).
      { intros x.
        destruct (Hdec (A + 216) (A + 224) x) as [i1|o1].
        { right. apply (f2_rd_of_bytes mem' (A + 216) _ x Q216). rewrite length_le8. lia. }
        destruct (Hdec (A + 232) (A + 240) x) as [i2|o2].
        { right. apply (f2_rd_of_bytes mem' (A + 232) _ x Q232). rewrite length_le8. lia. }
        left. subst W2. cbn [outside]. repeat split; try exact I; assumption. }
      assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g))
        by exact (fl_stk W2 mem mem' _ _ Hwin MU WM (fun x _ => HRB x)).
      destruct (f1_fra_spill B APIf ra empty FF g fr _ regs regs' mem mem' md md' A 216 224 232 240 HFRA HENT Hr9
                  HA64 ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia) MU WM HWIN' Hmat E2 E3 E4 E8 E9 E19 E26)
        as (HFRA' & HENT').
      assert (KO : forall x, 0 <= x < 2 ^ 64 -> ~ (A + 216 <= x < A + 224) -> ~ (A + 232 <= x < A + 240) ->
                mbyte rsegs mem' x = mbyte rsegs mem x).
      { intros x Hx H1 H2. apply (f2_mb_keep W2 mem mem' x MU Hx). subst W2. cbn [outside].
        split; [exact H1|]. split; [exact H2 | exact I]. }
      assert (KSH : forall x, app_mem x -> mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x))
        by (intros x Hx; exact (f2_mb_keep W2 mem mem' _ MU (HSHlo x Hx) (HSHA W2 x HAW2 Hx))).
      assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact Hr9).
      assert (HFLSH' : FLSH g j fr regs' mem').
      { apply (flsh_move g j fr regs regs' A mem mem' HFLSH Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; lia.
        - intros x Hx. apply KSH. apply Happfr. lia.
        - intros x Hx. pose proof (HIN x Hx HHq) as Hx'. split.
          + apply KO; lia.
          + apply KSH. pose proof (HinP0 ltac:(lia)) as Hin.
            destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md _ _ HAH (in_or_app _ _ _ (or_intror Hin)))
              as (_ & _ & _ & _ & Hall). exact (proj1 (Hall x Hx)).
        - exact (fra_stk B APIf ra g fr _ regs' mem' md' HFRA'). }
      assert (HIFS' : IFS g fr j regs' mem').
      { apply (f1_ifs_move g fr j regs regs' A mem mem' HIFS Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; lia.
        - intros x Hx. apply KO; lia.
        - intros x Hx. apply KSH. apply Happfr. lia. }
      assert (HFLC' : FLC fr regs' mem').
      { apply (flc_move fr regs regs' A mem mem' HFLC Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; lia.
        - intros x Hx. apply KSH. apply Happfr. lia. }
      rewrite <- SEGS. apply Hzero. cbv beta. exists phi, regs', mem', md', fr. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hn26|]. split; [exact Hj255|].
      split.
      { destruct HHB as (Hp0 & Had). split; [exact Hp0|].
        exact (sl_addr_keep mem mem' W2 phi (AC.a_size (flen g j)) Had MU HAW2). }
      split.
      { (* FLSI *)
        split; [exact HFLSH'|].
        split; [exists A; split; [exact H9' | exact Q216]|].
        split.
        { apply (f1_spill_move regs regs' A 224 _ mem mem' Hs224 Hr9 HA64 ltac:(lia) ltac:(lia) E9).
          intros x Hx. apply KO; lia. }
        split; [exact (f1_spill_move regs regs' A 248 _ mem mem' H248 Hr9 HA64 ltac:(lia) ltac:(lia) E9
                         ltac:(intros x Hx; apply KO; lia))|].
        split; [|exact HFLC'].
        split; [exact HinP0|]. split.
        - exact (sl_addr_keep mem mem' W2 (g_p g) (g_n g) HaddrP MU HAW2).
        - apply (f1_bkeep mem mem'); [|exact HbytesP]. intros x Hx. rewrite <- g_n_len in Hx.
          pose proof (HIN x Hx HHq). apply KO; lia. }
      split.
      { split; [exact Hjj|]. split; [unfold rg in *; rewrite Hreg, K21; exact H21|].
        unfold OURb in *. apply (f1_bkeep mem mem'); [|exact HOUR]. rewrite OUR_length.
        intros x Hx. apply KO; lia. }
      split.
      { apply (f2_b5C g j phi fr regs' mem' md' HFRA' HFLSH' HIFS' HFLC').
        - unfold rg. rewrite Hreg, K23. reflexivity.
        - unfold rg. rewrite Hreg, K18, Hz. reflexivity.
        - exists A. split; [exact H9'|].
          replace (if t_big (g_in g) j then 0 else 1) with 1; [exact Q232|].
          unfold t_big. rewrite <- HNe, Hz. reflexivity.
        - intros Hl. lia. }
      split; [exact Hz|].
      split.
      { destruct (f2_place g j phi fr regs' mem' md' HFRA' 1 ltac:(unfold AC.a_size; lia)) as (Hp & _).
        exact Hp. }
      split; [exact (proj1 HIFS')|].
      (* b5_PF: flen = 0, so both of its guards are false *)
      exists A. split; [exact H9'|]. split; [exact HA64|]. split; [intros Hl; lia|].
      intros H8819. exfalso.
      assert (Htb : t_big (g_in g) j = false) by (unfold t_big; rewrite <- HNe, Hz; reflexivity).
      unfold t_8819 in H8819. rewrite Htb in H8819. cbn in H8819. discriminate.
  - (* ---- len <> 0: the two spills, then the checked memcpy ---- *)
    assert (HN1 : 0 < flen g j) by lia.
    assert (HaszE : AC.a_size (flen g j) = flen g j) by (unfold AC.a_size; lia).
    assert (Hn0 : 0 < g_n g) by lia.
    pose proof (HinP0 Hn0) as HinP.
    assert (HinP' : In (g_p g, g_n g) (hb1 phi (AC.a_size (flen g j)) ++ g_H g))
      by (apply in_or_app; right; exact HinP).
    destruct (AC.a_laws_blocks _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HinP')
      as (_ & Hp4096 & HpSt & HpEnd & HpAll).
    assert (HSRC : bytes_at rsegs mem (g_p g + t_body (g_in g) j) (t_phi (g_in g) j)).
    { pose proof (f2_ba_sub mem (g_p g) (g_in g) (Z.to_nat (t_body (g_in g) j)) (Z.to_nat (t_len (g_in g) j))
                    HbytesP ltac:(unfold nlen in Hbodyn; lia)) as HH.
      rewrite Z2Nat.id in HH by lia. exact HH. }
    assert (HLs : length (t_phi (g_in g) j) = Z.to_nat (flen g j)) by (rewrite HNe; apply f2_phi_len).
    assert (HphN : phi + flen g j <= AC.aspZ regs - FN_STACK) by lia.
    assert (HSN : g_p g + t_body (g_in g) j + flen g j <= AC.aspZ regs - FN_STACK) by lia.
    assert (Hdisj : phi + AC.a_size (flen g j) <= g_p g \/ g_p g + g_n g <= phi)
      by exact (AC.a_laws_disjoint _ _ _ _ _ LAWS [] (g_H g) mem md phi (AC.a_size (flen g j))
                  (g_p g) (g_n g) HAH HinP).
    assert (Hdj2 : g_p g + t_body (g_in g) j + flen g j <= phi \/
                   phi + flen g j <= g_p g + t_body (g_in g) j) by lia.
    assert (HRTph : RT_HI <= phi) by lia.
    assert (HADD : addressable mem phi (flen g j)) by (rewrite <- HaszE; exact (proj2 HHB)).
    assert (HADS : addressable mem (g_p g + t_body (g_in g) j) (flen g j))
      by (apply (f2_addr_sub mem (g_p g) (g_n g)); [exact HaddrP | lia | lia | lia]).
    assert (HED : end_in_app phi (flen g j)) by (rewrite <- HaszE; exact HphEnd).
    assert (HESp : app_mem (g_p g)) by (destruct (HpAll (g_p g) ltac:(lia)) as (Ha & _); exact Ha).
    assert (HESq : app_mem (g_p g + g_n g)) by (destruct HpEnd as [He|He]; [lia | exact He]).
    pose proof (AC.a_laws_block_end _ _ _ _ _ LAWS _ mem md (g_p g) (g_n g) HAH HinP' Hn0) as HpA7.
    assert (HES : end_in_app (g_p g + t_body (g_in g) j) (flen g j))
      by (right; apply (f2_app_mid (g_p g) (g_p g + g_n g)); [exact HESp | exact HESq | lia | lia]).
    assert (HAPS : app_mem (g_p g + t_body (g_in g) j + 7))
      by (apply (f2_app_mid (g_p g) (g_p g + g_n g + 7)); [exact HESp | exact HpA7 | lia | lia]).
    assert (HAPDp : app_mem phi) by (destruct (HphAll phi ltac:(lia)) as (Ha & _); exact Ha).
    assert (HAPD : app_mem (phi + 7))
      by (apply (f2_app_mid phi (phi + AC.a_size (flen g j) + 7)); [exact HAPDp | exact HphA7 | lia | lia]).
    destruct (f2_rw_ex mem phi (Z.to_nat (flen g j)) ltac:(lia) ltac:(rewrite Z2Nat.id by lia; lia)
                ltac:(intros x Hx; rewrite Z2Nat.id in Hx by lia;
                      destruct (HphAll x ltac:(lia)) as (_ & Hw & _);
                      split; [exact Hw | apply f2_rd_of_wr; [lia | exact Hw]]))
      as (junk & HRWd).
    assert (HSTlo : stk rsegs mem (AC.aspZ regs - FN_STACK) (AC.aspZ regs)) by (rewrite Haspz; exact Hstkwin).
    assert (Hrel0 : MemNorm.mem_rel rsegs mem (MemNorm.normalize rsegs mem))
      by (apply MemNorm.mem_rel_normalize; exact Hro).
    assert (N_bS : bytes_at rsegs (MemNorm.normalize rsegs mem) (g_p g + t_body (g_in g) j) (t_phi (g_in g) j))
      by exact (proj1 (MemNorm.bytes_at_rel rsegs mem _ _ _ Hrel0) HSRC).
    assert (N_RWd : rw_cells rsegs (MemNorm.normalize rsegs mem) phi [CB (Z.to_nat (flen g j)) junk]).
    { apply f2_rw_norm; [exact Hro | | exact HRWd].
      intros i Hi. cbn [cells_size csize] in Hi. apply f2_ro_hi. lia. }
    assert (N_R216 : rw_cells rsegs (MemNorm.normalize rsegs mem) (A + 216) [CB 8 j1]).
    { apply f2_rw_norm; [exact Hro | | exact HR216].
      intros i Hi. cbn [cells_size csize] in Hi. apply f2_ro_hi. lia. }
    assert (N_R232 : rw_cells rsegs (MemNorm.normalize rsegs mem) (A + 232) [CB 8 j2]).
    { apply f2_rw_norm; [exact Hro | | exact HR232].
      intros i Hi. cbn [cells_size csize] in Hi. apply f2_ro_hi. lia. }
    assert (N_ADS : addressable (MemNorm.normalize rsegs mem) (g_p g + t_body (g_in g) j) (flen g j))
      by (apply f2_addr_norm; [exact Hro | exact HADS]).
    assert (N_ADD : addressable (MemNorm.normalize rsegs mem) phi (flen g j))
      by (apply f2_addr_norm; [exact Hro | exact HADD]).
    assert (N_ST : stk rsegs (MemNorm.normalize rsegs mem) (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
      by (apply f2_stk_norm; [exact Hro | intros x Hx; apply f2_ro_hi; lia | exact HSTlo]).
    assert (N_AC : asan_cells (MemNorm.normalize rsegs mem)) by (apply f2_ac_norm; [exact Hro | exact HAC0]).
    assert (N_SW : shadow_rw (MemNorm.normalize rsegs mem)) by (apply f2_shrw_norm; [exact Hro | exact HSW0]).
    pose proof (MemNorm.mem_inv_normalize rsegs mem) as N_MI.
    apply (f2_run regs (Z_to_bv 64 0x81da4) mem md
      (fun R pc' mem0' => pc' = Z_to_bv 64 0x81dd0 /\
         getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
         getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
         getr R 21 = getr regs 21 /\ getr R 26 = getr regs 26 /\
         getr R 18 = Z_to_bv 64 (flen g j) /\ getr R 20 = Z_to_bv 64 (g_p g + t_body (g_in g) j) /\
         getr R 22 = Z_to_bv 64 (b2z (flen g j <? 50)) /\ getr R 23 = Z_to_bv 64 phi /\
         munch [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + flen g j);
                      (AC.aspZ regs - ASAN_MEMCPY_K, AC.aspZ regs)] (MemNorm.normalize rsegs mem) mem0' /\
         wmono rsegs (MemNorm.normalize rsegs mem) mem0' /\
         stk rsegs mem0' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) /\
         rw_cells rsegs mem0' phi [CB (Z.to_nat (flen g j)) (t_phi (g_in g) j)] /\
         bytes_at rsegs mem0' (A + 216) (le8 (Z_to_bv 64 (g_p g + t_body (g_in g) j))) /\
         bytes_at rsegs mem0' (A + 232) (le8 (Z_to_bv 64 (b2z (flen g j <? 50)))))
      (Post B APIf ra g) Hhalt Hro).
    + eapply LE.evt_mono.
      { unfold Regs6ss.mkR_of.
        eapply (f2_evt MCPY) with (spv := AC.aspZ regs) (A := A) (phi := phi) (N := flen g j)
          (S := g_p g + t_body (g_in g) j) (lo := AC.aspZ regs - FN_STACK)
          (src := t_phi (g_in g) j) (junk := junk) (j1 := j1) (j2 := j2).
        - unfold AC.aspZ. symmetry. apply Z_to_bv_bv_unsigned.
        - exact Hr9.
        - exact Ha0.
        - rewrite HNe. exact H18.
        - exact H20.
        - lia.
        - lia.
        - lia.
        - lia.
        - exact HRTph.
        - exact HphN.
        - exact HSN.
        - exact Hdj2.
        - lia.
        - lia.
        - lia.
        - lia.
        - lia.
        - rewrite Haspz. exact Hspm.
        - exact N_bS.
        - exact HLs.
        - exact N_RWd.
        - exact N_R216.
        - exact N_R232.
        - exact N_ADS.
        - exact N_ADD.
        - exact HES.
        - exact HED.
        - exact HAPS.
        - exact HAPD.
        - exact N_ST.
        - exact N_AC.
        - exact N_SW.
        - exact N_MI. }
      { intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
          E & MU0 & WM0 & ST0 & RW0 & HB0 & AC0' & SW0' & Q216 & Q232).
        eexists _, (Z_to_bv 64 0x81dd0), m'. split; [exact E|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
        split; [reflexivity|].
        split; [exact MU0|]. split; [exact WM0|]. split; [exact ST0|]. split; [exact RW0|].
        split; [exact Q216 | exact Q232]. }
    + intros R pc' mem0' mem' regs' md' (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K26 & K18 & K20 & K22 & K23 &
        MU0 & WM0 & ST0 & RW0 & Q2160 & Q2320) HRel Hros Hreg Hmat.
      subst pc'.
      set (W4 := [(A + 216, A + 224); (A + 232, A + 240); (phi, phi + flen g j);
                  (AC.aspZ regs - ASAN_MEMCPY_K, AC.aspZ regs)]) in MU0.
      assert (MU : munch W4 mem mem')
        by (eapply MemNorm.munch_rel; [exact Hrel0 | exact HRel | exact Hros | exact MU0]).
      assert (WM : wmono rsegs mem mem')
        by (eapply MemNorm.wmono_rel; [exact Hrel0 | exact HRel | exact Hros | exact WM0]).
      assert (HRO' : ro_agree rsegs mem') by (eapply MemNorm.ro_agree_same; [exact Hro | exact Hros]).
      assert (ST' : stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
        by (eapply f2_stk_of; [exact HRel | exact ST0]).
      assert (RW' : rw_cells rsegs mem' phi [CB (Z.to_nat (flen g j)) (t_phi (g_in g) j)])
        by (eapply f2_rw_of; [exact HRel | exact RW0]).
      assert (Q216 : bytes_at rsegs mem' (A + 216) (le8 (Z_to_bv 64 (g_p g + t_body (g_in g) j))))
        by (eapply f2_bytes_of; [exact HRel | exact Q2160]).
      assert (Q232 : bytes_at rsegs mem' (A + 232) (le8 (Z_to_bv 64 (b2z (flen g j <? 50)))))
        by (eapply f2_bytes_of; [exact HRel | exact Q2320]).
      assert (E2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact K2).
      assert (E3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact K3).
      assert (E4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact K4).
      assert (E8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact K8).
      assert (E9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact K9).
      assert (E19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact K19).
      assert (E26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact K26).
      assert (HW4 : forall x, ~ (A + 216 <= x < A + 224) -> ~ (A + 232 <= x < A + 240) ->
                ~ (phi <= x < phi + flen g j) -> ~ (AC.aspZ regs - ASAN_MEMCPY_K <= x < AC.aspZ regs) ->
                outside W4 x).
      { intros x H1 H2 H3 H4. subst W4. cbn [outside].
        split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4 | exact I]. }
      assert (HAW4 : all_app W4).
      { subst W4. cbn [all_app app_ivl]. split; [|split; [|split; [|split; [|exact I]]]].
        - intros x Hx. unfold app_mem. right. lia.
        - intros x Hx. unfold app_mem. right. lia.
        - intros x Hx. destruct (HphAll x ltac:(lia)) as (Ha & _). exact Ha.
        - intros x Hx. unfold app_mem. right. lia. }
      assert (Hwinfr : forall x, fr <= x < fr + FRAME_BYTES -> ~ (AC.aspZ regs - ASAN_MEMCPY_K <= x < AC.aspZ regs)).
      { intros x Hx Hw. destruct (Hapart 2224 ltac:(lia)) as [Hd|Hd]; lia. }
      assert (Hfrout : forall x, fr <= x < fr + FRAME_BYTES -> outside W4 x).
      { intros x Hx. apply HW4; [lia | lia | | exact (Hwinfr x Hx)].
        intros Hb. apply (Hfrblk x Hx). lia. }
      assert (HAout : forall x, A + 32 <= x < A + 216 \/ A + 248 <= x < A + 416 -> outside W4 x)
        by (intros x Hx; apply HW4; lia).
      assert (HIout : forall x, g_p g <= x < g_p g + g_n g -> outside W4 x).
      { intros x Hx. pose proof (HIN x Hx HHq). apply HW4; [lia | lia | | lia].
        intros Hb. apply (HPdj x Hx). lia. }
      assert (HSHout : forall x, app_mem x -> outside W4 (shadow_addr x)) by (intros x Hx; exact (HSHA W4 x HAW4 Hx)).
      assert (HWlo : forall x, 0 <= x < 6283264 -> outside W4 x) by (intros x Hx; apply HW4; lia).
      assert (HRB : forall x, outside W4 x \/ exists b, mrd rsegs mem' (wa x) = Some b).
      { pose proof ST' as ST'c. destruct ST'c as (_ & _ & ST'c).
        intros x.
        destruct (Hdec (A + 216) (A + 224) x) as [i1|o1].
        { right. apply (f2_rd_of_bytes mem' (A + 216) _ x Q216). rewrite length_le8. lia. }
        destruct (Hdec (A + 232) (A + 240) x) as [i2|o2].
        { right. apply (f2_rd_of_bytes mem' (A + 232) _ x Q232). rewrite length_le8. lia. }
        destruct (Hdec phi (phi + flen g j) x) as [i3|o3].
        { right. apply (f2_rd_of_bytes mem' phi (t_phi (g_in g) j) x (f2_c_bytes _ _ _ RW')).
          rewrite HLs. lia. }
        destruct (Hdec (AC.aspZ regs - ASAN_MEMCPY_K) (AC.aspZ regs) x) as [i4|o4].
        { right. exact (proj2 (ST'c x ltac:(lia))). }
        left. apply HW4; assumption. }
      (* AH, ownership and the stack bounds after the run: every write is a_store_ok *)
      assert (Hwrit : forall x, 0 <= x < 2 ^ 64 -> writable_at rsegs mem x -> writable_at rsegs mem' x)
        by (intros x _ Hx; exact (WM (Z_to_bv 64 x) Hx)).
      assert (Hmc : forall x, 0 <= x < 2 ^ 64 ->
                ~ AC.a_store_ok (hb1 phi (AC.a_size (flen g j)) ++ g_H g)
                    (AC.aa_stklo AC.ASYMS AsanRTInv.RT API mem md) x ->
                mem' (Z_to_bv 64 x) = mem (Z_to_bv 64 x)).
      { intros x Hx Hnok. apply MU. rewrite MState.unsigned_lit by exact Hx. apply HW4.
        - intros Hin. apply Hnok. right; left. lia.
        - intros Hin. apply Hnok. right; left. lia.
        - intros Hin. apply Hnok. left. exists phi, (AC.a_size (flen g j)).
          split; [exact Hinphi | lia].
        - intros Hin. apply Hnok. right; left. lia. }
      destruct (AC.a_laws_store _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem mem' md HAH Hmc Hwrit)
        as (HAH' & HOWN' & HSTK' & HHI').
      assert (HDJ : rt_disjoint W4).
      { subst W4. unfold rt_disjoint. cbn [disjoint_from].
        unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
          RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN.
        repeat split; first [exact I | left; lia]. }
      assert (HWIN' : stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g))
        by exact (fl_stk W4 mem mem' _ _ Hwin MU WM (fun x _ => HRB x)).
      assert (HFSR : FSREC fr mem -> FSREC fr mem').
      { intros Hf. apply (f2_fsrec mem mem' W4 fr Hf MU).
        - intros x Hx. apply HW4; lia.
        - intros x Hfsx. pose proof Hfsx as (b0 & Hb0 & Hw0 & Hx0).
          destruct (AC.a_laws_fs_place _ _ _ _ _ LAWS _ mem md b0 HAH Hw0 Hb0) as (_ & Hend & _ & _).
          apply HW4; [lia | lia | | lia].
          intros Hin. destruct (HphAll x ltac:(lia)) as (_ & _ & _ & _ & Hnfs). exact (Hnfs Hfsx). }
      assert (HA9 : forall A0, getr regs 9 = Z_to_bv 64 A0 -> 0 <= A0 < 2 ^ 64 -> A0 = A).
      { intros A0 HA0 HA0r. pose proof (rg_eq64 regs 9 A0 A HA0 Hr9) as Hm.
        rewrite !Z.mod_small in Hm by lia. exact Hm. }
      assert (HFRAm : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md).
      { apply (sl_fr_cl B APIf ra empty FF g fr _ regs regs' mem mem' md W4 HFRA MU WM HRO' HAW4 HDJ HAH' HSTK').
        - exact HWlo.
        - intros x Hx. apply Hfrout. lia.
        - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx. apply HAout. lia.
        - intros x Hx. apply HW4; lia.
        - intros x Hx. assert (Hxs : x = shadow_addr (fr + 8 * (x - Sfr fr))).
          { unfold Sfr, shadow_addr in *.
            replace (fr + 8 * (x - (fr / 8 + ASAN_K))) with ((x - (fr / 8 + ASAN_K)) * 8 + fr) by lia.
            rewrite Z.div_add_l by lia. lia. }
          rewrite Hxs. apply HSHout. apply Happfr. lia.
        - intros A0 HA0 HA0r x Hx. rewrite (HA9 A0 HA0 HA0r) in Hx. apply HW4; lia.
        - exact HWIN'.
        - exact HFSR.
        - exact E2.
        - exact E3.
        - exact E4.
        - exact E8.
        - exact E9.
        - exact E19.
        - exact E26. }
      assert (HFRA' : FRA B APIf ra g fr (hb1 phi (AC.a_size (flen g j))) regs' mem' md')
        by (apply (sl_fra_move B APIf ra g fr _ regs' regs' mem' md md' HFRAm); try reflexivity; exact Hmat).
      (* ENT across the run: no write is an entry-block byte, an image byte, at or above S, or a shadow byte *)
      assert (HKEPT : forall x, ent_kept g x -> outside W4 x).
      { intros x Hkx.
        destruct Hkx as [(q & k & i & Hin & Hni & Hi & ->) | [Hik | [Habk | [(bq & Hor & ->) |
                         (q5 & k5 & i5 & Hin5 & _ & Hi5 & ->)]]]].
        - pose proof (AC.a_laws_disjoint _ _ _ _ _ LAWS [] (g_H g) mem md phi (AC.a_size (flen g j)) q k HAH Hin)
            as Hdj.
          destruct (HHq q k Hin). apply HW4; lia.
        - pose proof (img_below_GT x Hik) as Hxg. apply HW4; lia.
        - apply HW4; lia.
        - apply HSHout. destruct Hor as [Hib|Hrb].
          + pose proof (img_below_GT bq Hib) as Hbg. unfold app_mem. left. unfold LOWMEM_END. lia.
          + unfold app_mem. right. lia.
        - (* frame batch 2 item 9: the shadow byte of an entry block byte (app memory) *)
          destruct (AC.a_laws_blocks _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md q5 k5 HAH
                      (in_or_app _ _ _ (or_intror Hin5))) as (_ & _ & _ & _ & Hall5).
          destruct (Hall5 (q5 + i5) ltac:(lia)) as (Happq5 & _).
          exact (HSHout (q5 + i5) Happq5). }
      assert (HENT' : ENT APIf g (hb1 phi (AC.a_size (flen g j))) mem' md').
      { eapply ent_mat; [|exact Hmat].
        eapply ent_munch;
          [exact HENT | exact HAH | apply (proj1 (fr_munch_ul _ _ _)); exact MU |
           intros x Hx; apply (proj2 (fr_outside_lib _ _)); exact (HKEPT x Hx) | exact HSTK' | exact HHI' |].
        intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
      (* the keeps *)
      assert (KO : forall x, 0 <= x < 2 ^ 64 -> outside W4 x -> mbyte rsegs mem' x = mbyte rsegs mem x)
        by (intros x Hx Ho; exact (f2_mb_keep W4 mem mem' x MU Hx Ho)).
      assert (KSH : forall x, app_mem x -> mbyte rsegs mem' (shadow_addr x) = mbyte rsegs mem (shadow_addr x))
        by (intros x Hx; exact (KO _ (HSHlo x Hx) (HSHout x Hx))).
      assert (H9' : rg regs' 9 A) by (unfold rg in *; rewrite E9; exact Hr9).
      assert (HFLSH' : FLSH g j fr regs' mem').
      { apply (flsh_move g j fr regs regs' A mem mem' HFLSH Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; [lia | apply HAout; lia].
        - intros x Hx. apply KSH. apply Happfr. lia.
        - intros x Hx. split; [apply KO; [lia | exact (HIout x Hx)]|].
          apply KSH. exact (proj1 (HpAll x Hx)).
        - exact (fra_stk B APIf ra g fr _ regs' mem' md' HFRA'). }
      assert (HIFS' : IFS g fr j regs' mem').
      { apply (f1_ifs_move g fr j regs regs' A mem mem' HIFS Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; [lia | apply Hfrout; lia].
        - intros x Hx. apply KO; [lia | apply HAout; lia].
        - intros x Hx. apply KSH. apply Happfr. lia. }
      assert (HFLC' : FLC fr regs' mem').
      { apply (flc_move fr regs regs' A mem mem' HFLC Hr9 HA64 ltac:(lia) E9).
        - intros x Hx. apply KO; [lia | apply HAout; lia].
        - intros x Hx. apply KSH. apply Happfr. lia. }
      assert (HREC : bytes_at rsegs mem' phi (t_phi (g_in g) j)) by exact (f2_c_bytes _ _ _ RW').
      rewrite <- SEGS. apply Hexit. cbv beta. exists phi, regs', mem', md', fr. split; [reflexivity|].
      split; [exact HFRA'|]. split; [exact HENT'|].
      split; [exact Hn26|]. split; [exact Hj255|].
      split.
      { destruct HHB as (Hp0 & Had). split; [exact Hp0|].
        exact (sl_addr_keep mem mem' W4 phi (AC.a_size (flen g j)) Had MU HAW4). }
      split.
      { (* FLSI *)
        split; [exact HFLSH'|].
        split; [exists A; split; [exact H9' | exact Q216]|].
        split.
        { apply (f1_spill_move regs regs' A 224 _ mem mem' Hs224 Hr9 HA64 ltac:(lia) ltac:(lia) E9).
          intros x Hx. apply KO; [lia | apply HW4; lia]. }
        split; [exact (f1_spill_move regs regs' A 248 _ mem mem' H248 Hr9 HA64 ltac:(lia) ltac:(lia) E9
                         ltac:(intros x Hx; apply KO; [lia | apply HAout; lia]))|].
        split; [|exact HFLC'].
        split; [exact HinP0|]. split.
        - exact (sl_addr_keep mem mem' W4 (g_p g) (g_n g) HaddrP MU HAW4).
        - apply (f1_bkeep mem mem'); [|exact HbytesP]. intros x Hx. rewrite <- g_n_len in Hx.
          apply KO; [lia | exact (HIout x Hx)]. }
      split.
      { split; [exact Hjj|]. split; [unfold rg in *; rewrite Hreg, K21; exact H21|].
        unfold OURb in *. apply (f1_bkeep mem mem'); [|exact HOUR]. rewrite OUR_length.
        intros x Hx. apply KO; [lia | apply Hfrout; lia]. }
      split.
      { apply (f2_b5C g j phi fr regs' mem' md' HFRA' HFLSH' HIFS' HFLC').
        - unfold rg. rewrite Hreg, K23. reflexivity.
        - unfold rg. rewrite Hreg, K18. reflexivity.
        - exists A. split; [exact H9'|].
          replace (if t_big (g_in g) j then 0 else 1) with (b2z (flen g j <? 50)); [exact Q232|].
          unfold t_big, b2z. rewrite <- HNe.
          destruct (Z.ltb_spec (flen g j) 50); destruct (Z.leb_spec 50 (flen g j)); first [reflexivity | lia].
        - intros Hl. unfold t_g. rewrite f2_fr50 by lia. apply f2_ba_firstn. exact HREC. }
      split.
      { split; [|split].
        - apply (f1_spill_move regs regs' A 224 _ mem mem' Hs224 Hr9 HA64 ltac:(lia) ltac:(lia) E9).
          intros x Hx. apply KO; [lia | apply HW4; lia].
        - unfold rg. rewrite Hreg, K20. reflexivity.
        - unfold rg. rewrite Hreg, K18, HNe. reflexivity. }
      split.
      { intros Hl. unfold rg. rewrite Hreg, K22.
        rewrite (proj2 (Z.ltb_ge (flen g j) 50) ltac:(lia)). reflexivity. }
      split; [intros _; exact HREC|].
      exact (proj1 HIFS').
Qed.

End S.
