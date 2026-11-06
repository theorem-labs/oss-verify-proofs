(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGfu.v (a working branch 84ee52cd012, file sha256 e60eb686f429) onto omx-clap-core/fuzz_state's asan image (unstripped fuzz_state.asan, sha256 7c4afaee248b); module paths changed; its 3 image addresses moved by code-verified function pairs (14 port_addr_check 16f8a030c869 MAPS predictions, each code one re-derived by funcpair.py; 0 code pcs the tool read as sizes, by funcpair.py); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated to omx-clap-core fuzz_state image A (fs.asan): the decimal TFIB_TP numeral is fs's 6139696 (0x5daf30, AF0m.TFIB_TP; AFfu.v:491), not cgif's 6132240 (0x5d9210), which the relocation left. *)
(* The seed of the frame-generic Deallocate walk, arm "the last batch has room" (DGgi): DGgi.free_hyps holds at
   Deallocate's entry (A_Deallocate) from the generic precondition DeallocG.dealloc_pre (segs = tfibsegs, atp = 1)
   and the interface view DGif0.dview.  The virtual register file of the walk is
   regs0 = dregs regs pa inst bp so (x10 = the block's address, x11 = inst, x12 = bp, x13 = so); the machine
   registers [regs] are DGbase.REGS_G over E0.  The header byte [hb1] comes from dv_hdr; [j1], [j2], [j3] are the
   words at T + t_stats + 24, T + t_stats + 32 and at the block's address, read from present bytes.  No allocator
   model is used.  (Generalized from the released YFfu: the same region scripts, with the facts of ARm / YFex
   replaced by dview, layout_ok and dealloc_pre.) *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGbase DGgi.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import AGif2cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Ltac rne := first [ discriminate | let Hc := fresh "Hc" in intro Hc; vm_compute in Hc; discriminate Hc | vm_compute; discriminate ].
Ltac nums := unfold kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kHighMemBeg, kHighMemEnd,
kQuarantineCacheMax, DFSTACK, DFSTACK_G, TFIB_IMG_END, TFIB_IMG_LO, kLowShadowBeg, SHADOW_OFF, t_qc, t_stats, t_unwinding,
kNodesBlockSize, kStoreBlockSize in *.
Lemma le_byte_lt : forall v (w k : nat), 0 <= YG0f.le_byte v w k < 256.
Proof. intros v w k. unfold YG0f.le_byte. apply Z.mod_pos_bound. lia. Qed.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Lemma aview_vis_byte : forall H mem a, aview tfibsegs H mem a <> None ->
exists b, aview tfibsegs H mem a = Some b /\ 0 <= b < 256 /\ mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 b).
Proof.
intros H mem a Hv. destruct (aview tfibsegs H mem a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exists b. split; [reflexivity|]. pose proof E as E'. apply aview_some in E as (b8 & Hb & <-).
pose proof (bv_unsigned_in_range 8 b8) as R. change (bv_modulus 8) with 256 in R. split; [lia|]. exact (aview_byte _ _ _ _ E').
Qed.
Lemma vis_word : forall H mem a, (forall i, 0 <= i < 8 -> aview tfibsegs H mem (a + i) <> None) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 w /\ rdword (aview tfibsegs H mem) a = Some w.
Proof.
intros H mem a Hv.
destruct (aview_vis_byte H mem (a + 0) (Hv 0 ltac:(lia))) as (b0 & E0 & R0 & M0).
destruct (aview_vis_byte H mem (a + 1) (Hv 1 ltac:(lia))) as (b1 & E1 & R1 & M1).
destruct (aview_vis_byte H mem (a + 2) (Hv 2 ltac:(lia))) as (b2 & E2 & R2 & M2).
destruct (aview_vis_byte H mem (a + 3) (Hv 3 ltac:(lia))) as (b3 & E3 & R3 & M3).
destruct (aview_vis_byte H mem (a + 4) (Hv 4 ltac:(lia))) as (b4 & E4 & R4 & M4).
destruct (aview_vis_byte H mem (a + 5) (Hv 5 ltac:(lia))) as (b5 & E5 & R5 & M5).
destruct (aview_vis_byte H mem (a + 6) (Hv 6 ltac:(lia))) as (b6 & E6 & R6 & M6).
destruct (aview_vis_byte H mem (a + 7) (Hv 7 ltac:(lia))) as (b7 & E7 & R7 & M7).
set (w := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))).
exists w. split; [subst w; lia|]. split.
- assert (LB : forall k, (k < 8)%nat -> YO0f.le_byte w 8 k = nth k [b0; b1; b2; b3; b4; b5; b6; b7] 0).
{ intros k Hk. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small w (2 ^ 64)) by (subst w; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
[ change (2 ^ (8 * 0)) with 1 | change (2 ^ (8 * 1)) with 256 | change (2 ^ (8 * 2)) with 65536 | change (2 ^ (8 * 3)) with 16777216
| change (2 ^ (8 * 4)) with 4294967296 | change (2 ^ (8 * 5)) with 1099511627776 | change (2 ^ (8 * 6)) with 281474976710656
| change (2 ^ (8 * 7)) with 72057594037927936 ]; subst w; Z.div_mod_to_equations; nia. }
intros k Hk. rewrite (LB k Hk). rewrite Z.add_0_r in M0.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; assumption.
- unfold rdword. rewrite Z.add_0_r in E0. rewrite E0, E1, E2, E3, E4, E5, E6, E7. reflexivity.
Qed.
Lemma vis_writable_off : forall H mem a, off_img a -> aview tfibsegs H mem a <> None -> writable_at tfibsegs (mrestrict H mem) a.
Proof.
intros H mem a Ha Hv. destruct (aview_vis_byte H mem a Hv) as (b & _ & _ & M). exact (mbyte_off_writable _ a _ Ha M).
Qed.
Lemma val_mem_vis : forall H mem a (w : nat) v i, val_mem tfibsegs (mrestrict H mem) a w v -> 0 <= i < Z.of_nat w ->
aview tfibsegs H mem (a + i) <> None.
Proof.
intros H mem a w v i Hv Hi. unfold aview. replace i with (Z.of_nat (Z.to_nat i)) by lia. rewrite (Hv (Z.to_nat i) ltac:(lia)). discriminate.
Qed.
Lemma apresent_vis : forall H mem a, apresent H mem a -> aview tfibsegs H mem a <> None.
Proof. intros H mem a Hp. destruct (apresent_mbyte H mem a Hp) as [b Hb]. unfold aview. rewrite Hb. cbn. discriminate. Qed.
Lemma val_mem_writable : forall H mem a (w : nat) v o, val_mem tfibsegs (mrestrict H mem) a w v -> a <= o < a + Z.of_nat w -> off_img o ->
writable_at tfibsegs (mrestrict H mem) o.
Proof. intros H mem a w v o Hv Ho Ha. apply vis_writable_off; [exact Ha|]. replace o with (a + (o - a)) by lia. eapply val_mem_vis; [exact Hv | lia]. Qed.

Section g.
Variable B : asyms.
Hypothesis TS : TfibSyms B.
Section h.
Variables (ly : alayout) (S : astate) (W : world tfibsegs) (regs : bvmap 5 word) (mem : word -> option byte).
Variables (inst so bp : Z) (p : sptr) (n : Z) (tr : list Z) (lastb : batch) (initr : list batch) (hb1 j1 j2 j3 : Z).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Local Notation q := (st_qthread S).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation regs0 := (dregs regs (sptr_addr B ly p) inst bp so).
Local Notation E0 := (DGgi.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb j1 j2 j3).
Local Notation N8v := (DGgi.N8v (req_size n)).
Local Notation CNT8v := (DGgi.CNT8v (req_size n)).
Local Notation SPv := (DGgi.SPv (sptr_addr B ly p)).
Local Notation IMv := (DGgi.IMv (sptr_addr B ly p)).
Local Notation HWv := (DGgi.HWv hb1).
Local Notation Bv := (DGgi.Bv ly lastb).
Local Notation BBv := (DGgi.BBv lastb).
Local Notation BCv := (DGgi.BCv lastb).
Local Notation SLOTv := (DGgi.SLOTv ly lastb).
Local Notation QSv := (DGgi.QSv (st_qthread S)).
Local Notation QFv := (DGgi.QFv ly (st_qthread S)).
Local Notation QBv := (DGgi.QBv (st_qthread S)).
Hypothesis HIO : inst_ok inst.
Hypothesis DV : dview B W ly inst mem S p n.
Hypothesis Hrev : rev (qc_list q) = lastb :: initr.
Hypothesis Hroom : Z.of_nat (length (b_items lastb)) < kBatchSlots.
Hypothesis Hqb : qc_bytes q + nn <= kQuarantineCacheMax.
(* The facts of DeallocG.dealloc_pre used by the seed. *)
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4096 : 4096 <= raZ regs.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hlo : ly_stk_lo ly + DFSTACK_G <= spZ regs.
Hypothesis Hhi : spZ regs <= ly_stk_hi ly.
Hypothesis Hbot : ly_bot ly < spZ regs.
Hypothesis HPRES : forall a, spZ regs - DFSTACK_G <= a < spZ regs -> apresent (w_H W) mem a.
Hypothesis Htp : getr regs 4 = w64 (as_tp B).
Hypothesis H10 : getr regs 10 = w64 inst.
Hypothesis H11 : getr regs 11 = w64 (sptr_addr B ly p).
Hypothesis H12 : getr regs 12 = w64 0.
Hypothesis H13 : getr regs 13 = w64 0.
Hypothesis H14 : getr regs 14 = w64 so.
Hypothesis H15 : getr regs 15 = w64 1.
Hypothesis Hso1 : spZ regs <= so.
Hypothesis Hso2 : so + 16 <= ly_stk_hi ly.
Hypothesis Hso3 : so mod 8 = 0.
Hypothesis Hbp1 : spZ regs <= bp.
Hypothesis Hbp2 : bp + 8 * 30 <= ly_stk_hi ly.
Hypothesis Hbp3 : bp mod 8 = 0.
Hypothesis Htrlen : (1 <= length tr <= 30)%nat.
Hypothesis PSO : val_mem tfibsegs m0 so 8 bp.
Hypothesis PLEN : val_mem tfibsegs m0 (so + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF : forall i, (i < length tr)%nat -> val_mem tfibsegs m0 (bp + 8 * Z.of_nat i) 8 (nth i tr 0).
(* The header byte (dv_hdr) and the words read from present bytes. *)
Hypothesis Hb1 : 0 <= hb1 < 256.
Hypothesis Hb1m : Z.land hb1 127 = 17.
Hypothesis W1 : val_mem tfibsegs m0 (sptr_addr B ly p - 16) 4 (2 + 256 * hb1).
Hypothesis W2 : val_mem tfibsegs m0 (sptr_addr B ly p - 12) 4 (req_size n).
Hypothesis J1 : val_mem tfibsegs m0 (ly_T ly + t_stats + 24) 8 j1.
Hypothesis J1R : 0 <= j1 < 2 ^ 64.
Hypothesis J2 : val_mem tfibsegs m0 (ly_T ly + t_stats + 32) 8 j2.
Hypothesis J2R : 0 <= j2 < 2 ^ 64.
Hypothesis J3 : val_mem tfibsegs m0 (sptr_addr B ly p) 8 j3.
Hypothesis J3R : 0 <= j3 < 2 ^ 64.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The layout and the block, from the view.                                                                         *)
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\
zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
pose proof DV as [[LY IMG _ _ _ _ _] _ _ _ _ _ _ _ _ _].
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth_f _ _ 6 _ HA eq_refl) as IC.
pose proof (Forall_nth_f _ _ 4 _ HA eq_refl) as INB. pose proof (Forall_nth_f _ _ 5 _ HA eq_refl) as ISB.
cbn beta in IT, IC, INB, ISB. cbn [fst snd] in IT, IC, INB, ISB.
pose proof (zone3_intro ly T kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
pose proof (zone3_intro ly (ly_C ly) 256 IMG ltac:(clear_all; lia) IC (pairwise_ij_f _ _ 6 2 _ _ HD eq_refl eq_refl)) as ZC.
pose proof (zone3_intro ly (ly_NB ly) kNodesBlockSize IMG ltac:(clear_all; unfold kNodesBlockSize; lia) INB (pairwise_ij_f _ _ 4 4 _ _ HD eq_refl eq_refl)) as ZNB.
pose proof (zone3_intro ly (ly_SB ly) kStoreBlockSize IMG ltac:(clear_all; unfold kStoreBlockSize; lia) ISB (pairwise_ij_f _ _ 5 3 _ _ HD eq_refl eq_refl)) as ZSB.
clear HA HD. unfold in_high in IP. cbn [fst snd] in IP.
split; [exact ZT|]. split; [clear - ZT; unfold zone3 in ZT; lia|].
split; [clear - IP; unfold zone3, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg in *; lia|]. split; [clear - HSP; lia|]. split; [clear - HSP; lia|]. split; [clear - IP; lia|].
split; [exact ZC|]. split; [clear - ZC; unfold zone3 in ZC; lia|].
split; [exact ZNB|]. split; [clear - ZNB; unfold zone3 in ZNB; lia|].
split; [exact ZSB|]. split; [clear - ZSB; unfold zone3 in ZSB; lia|].
clear - T1 T2 T3 T4 T5 T6 T7. repeat split; lia.
Qed.
Lemma LYD3 : zdisjoint (ly_prim ly, kPrimResvSize) (T, kThreadObjSize) /\ zdisjoint (ly_prim ly, kPrimResvSize) (ly_C ly, 256) /\
zdisjoint (T, kThreadObjSize) (ly_C ly, 256) /\ ASAN_CEIL <= ly_stk_lo ly.
Proof.
pose proof DV as [[LY _ _ _ _ _ _] _ _ _ _ _ _ _ _ _]. pose proof (lo_disj ly LY) as HD.
split; [exact (pairwise_ij_f _ _ 0 1 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 0 5 _ _ HD eq_refl eq_refl)|].
split; [exact (pairwise_ij_f _ _ 2 3 _ _ HD eq_refl eq_refl)|].
exact (lo_stk_ceil ly LY).
Qed.
Lemma LYAL : T mod 4096 = 0 /\ ly_C ly mod 8 = 0 /\ SB mod 65536 = 0 /\ ly_top ly mod 4096 = 0.
Proof.
pose proof DV as [[LY _ _ _ _ _ _] _ _ _ _ _ _ _ _ _].
pose proof (lo_T_al ly LY) as A1. pose proof (lo_C_al ly LY) as A2. pose proof (lo_space_al ly LY) as A3.
pose proof (lo_top ly LY) as (_ & _ & A4 & _). unfold page_aligned in *. split; [exact A1|]. split; [exact A2|]. split; [exact A3 | exact A4].
Qed.
Lemma PZ : zone3 (pa - 16) (N8v + 16) /\ DGgi.PSTATIC ly pa nn /\ pa mod 16 = 0 /\ 1 <= nn < 2 ^ 28.
Proof. pose proof DV as [_ _ _ _ _ _ _ HZ _ _]. exact HZ. Qed.
Lemma N8_ge : 8 <= N8v /\ nn <= N8v < nn + 8.
Proof. pose proof PZ as (_ & _ & _ & Hn). unfold DGgi.N8v. pose proof (div8_bounds (nn + 7) ltac:(lia)). lia. Qed.
Lemma p_facts : 4096 + 16 <= pa /\ pa + N8v <= ASAN_CEIL /\ 8 <= N8v /\ nn <= N8v < nn + 8 /\ pa mod 16 = 0 /\ 1 <= nn < 2 ^ 28.
Proof.
pose proof PZ as ((Z1 & Z2 & _) & _ & P16 & Hn). pose proof N8_ge as [N1 N2].
split; [lia|]. split; [lia|]. split; [exact N1|]. split; [exact N2|]. split; [exact P16 | exact Hn].
Qed.
Lemma blk_out : forall lo len, 0 < len -> 0 <= N8v -> (forall a, pa - 16 <= a < pa + N8v -> ~ (lo <= a < lo + len)) ->
pa + N8v <= lo \/ lo + len <= pa - 16.
Proof.
intros lo len Hl HN H.
destruct (Z_le_gt_dec (pa + N8v) lo) as [L1|L1]; [left; exact L1|].
destruct (Z_le_gt_dec (lo + len) (pa - 16)) as [L2|L2]; [right; exact L2|].
exfalso. destruct (Z_le_gt_dec lo (pa - 16)) as [L3|L3].
- apply (H (pa - 16)); lia.
- apply (H lo); lia.
Qed.
Lemma blk_ivs : (pa + N8v <= T \/ T + kThreadObjSize <= pa - 16) /\ (pa + N8v <= ly_C ly \/ ly_C ly + 256 <= pa - 16).
Proof.
pose proof PZ as (_ & PST & _ & _). pose proof N8_ge as [N8a _].
split; apply blk_out; try (unfold kThreadObjSize; lia); intros a Ha; specialize (PST a Ha); tauto.
Qed.
Lemma DBV : dbview W ly mem q lastb pa nn.
Proof. pose proof DV as [_ _ _ _ _ _ _ _ _ HB]. exact (HB lastb initr Hrev). Qed.
Lemma B_facts : SB <= Bv /\ Bv + kBatchBytes <= SB + kSpaceSize /\ 0 <= QFv < 2 ^ 64 /\ Bv mod 8192 = 0 /\
0 <= BBv /\ BBv + nn < 2 ^ 48 /\ QSv < 2 ^ 48 /\ 1 <= QSv /\ 0 <= BCv < kBatchSlots /\ 0 <= QBv <= kQuarantineCacheMax /\
QBv + nn <= kQuarantineCacheMax /\ DGgi.PBDISJ ly pa nn lastb.
Proof.
pose proof DBV as [_ _ _ (R1 & R2 & (R3 & R3') & R4) DD (D1 & D2 & D3) _].
pose proof DV as [_ _ _ _ _ _ _ _ HQB _].
assert (QS1 : 1 <= QSv) by (unfold DGgi.QSv; rewrite <- length_rev, Hrev; cbn [length]; lia).
assert (BC0 : 0 <= BCv) by (unfold DGgi.BCv; lia).
assert (BC1 : BCv < kBatchSlots) by exact Hroom.
repeat split; first [assumption | lia | exact (proj1 HQB) | exact (proj2 HQB) | exact Hqb].
Qed.
Lemma IM_facts : 0xa9140 <= IMv <= 0xa9140 + 8 * 0x7fff /\ IMv mod 8 = 0.
Proof.
pose proof p_facts as (P1 & P2 & P3 & _). ceil. unfold ASAN_CEIL in *.
unfold DGgi.IMv. split.
- assert (D1 : 0 <= pa / 2 ^ 32) by (apply Z.div_pos; lia).
  assert (D2 : pa / 2 ^ 32 <= 32767).
  { change (2 ^ 32) with 4294967296. pose proof (Z.div_le_mono pa 140737479966720 4294967296 ltac:(lia) ltac:(lia)) as X.
    change (140737479966720 / 4294967296) with 32767 in X. exact X. }
  lia.
- rewrite (Z.mul_comm 8), Z_mod_plus_full. reflexivity.
Qed.
Lemma SP_facts : SHADOW_OFF + 514 <= SPv <= SHADOW_OFF + 140737479966720 / 8 /\ SPv mod 2 = 0.
Proof.
pose proof p_facts as (P1 & P2 & P3 & _ & P16 & _). ceil. unfold ASAN_CEIL in *.
unfold DGgi.SPv. split.
- pose proof (Z.div_le_mono 4112 pa 8 ltac:(lia) ltac:(lia)) as X1. change (4112 / 8) with 514 in X1.
  pose proof (Z.div_le_mono pa 140737479966720 8 ltac:(lia) ltac:(lia)) as X2. lia.
- apply Z.mod_divide in P16 as [c Hc]; [|lia]. rewrite Hc. replace (c * 16) with (c * 2 * 8) by lia. rewrite Z_div_mult by lia.
  unfold SHADOW_OFF. apply Z.mod_divide; [lia|]. exists (1073725440 + c). lia.
Qed.
Lemma N8_facts : 8 <= N8v <= 2 ^ 28 /\ N8v mod 8 = 0 /\ 1 <= CNT8v <= 2 ^ 25.
Proof.
pose proof p_facts as (_ & _ & P3 & P4 & _ & P6).
unfold DGgi.CNT8v. unfold DGgi.N8v in *. rewrite Z_div_mult by lia.
pose proof (div8_bounds (nn + 7) ltac:(lia)) as D. split; [lia|]. split; [apply Z_mod_mult|]. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The atoms of E0.                                                                                                 *)
Lemma R_sp : 0 <= spZ regs < 2 ^ 64. Proof. unfold spZ. apply u64_range. Qed.
Lemma E2w : ew E0 2 = w64 (spZ regs).
Proof.
unfold DGgi.E0. rewrite (ew_Ereg_nat _ _ 2 2%bv eq_refl). unfold dregs.
rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne.
unfold spZ, w64. symmetry. apply Z_to_bv_bv_unsigned.
Qed.
Lemma E10 : ew E0 10 = w64 pa. Proof. unfold DGgi.E0. rewrite (ew_Ereg_nat _ _ 10 10%bv eq_refl). apply dregs_10. Qed.
Lemma E11 : ew E0 11 = w64 inst. Proof. unfold DGgi.E0. rewrite (ew_Ereg_nat _ _ 11 11%bv eq_refl). apply dregs_11. Qed.
Lemma E12 : ew E0 12 = w64 bp. Proof. unfold DGgi.E0. rewrite (ew_Ereg_nat _ _ 12 12%bv eq_refl). apply dregs_12. Qed.
Lemma E13 : ew E0 13 = w64 so. Proof. unfold DGgi.E0. rewrite (ew_Ereg_nat _ _ 13 13%bv eq_refl). apply dregs_13. Qed.
Lemma Uw : forall k x, ew E0 k = w64 x -> 0 <= x < 2 ^ 64 -> bv_unsigned (ew E0 k) = x.
Proof. intros k x H R. rewrite H. unfold w64. apply unsigned_lit_small. exact R. Qed.
Lemma R_so : 0 <= so < 2 ^ 64 /\ 0 <= bp < 2 ^ 64.
Proof. pose proof R_sp. pose proof LYB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & S4 & _). unfold kHighMemEnd in S4. lia. Qed.
Lemma R_inst : 0 <= inst < 2 ^ 64. Proof. destruct HIO as (I1 & I2 & _). lia. Qed.
Lemma R_pa : 0 <= pa < 2 ^ 64. Proof. pose proof p_facts as (P1 & P2 & P3 & _). ceil. unfold ASAN_CEIL in *. lia. Qed.
Lemma R_T : 0 <= T < 2 ^ 64 /\ 0 <= ly_C ly < 2 ^ 64.
Proof. pose proof LYB as ((Z1 & Z2 & _) & _ & _ & _ & _ & _ & (C1 & C2 & _) & _). ceil. unfold ASAN_CEIL in *. unfold kThreadObjSize in *. lia. Qed.
Lemma R_B : 0 <= Bv /\ Bv + 8192 <= ASAN_CEIL /\ kHighMemBeg <= Bv /\ 0 <= SLOTv /\ SLOTv + 8 <= Bv + 8192 /\ SLOTv = Bv + 24 + 8 * BCv.
Proof.
pose proof LYB as (_ & _ & hP1 & hP2 & hP3 & hP4 & _). pose proof B_facts as (B1 & B2 & _ & _ & _ & _ & _ & _ & (BC0 & BC1) & _).
unfold DGgi.SLOTv. unfold kBatchBytes, kBatchSlots, kSpaceSize, kPrimResvSize, kHighMemBeg in *. lia.
Qed.
Lemma R_B64 : 0 <= Bv < 2 ^ 64 /\ 0 <= SLOTv < 2 ^ 64.
Proof. pose proof R_B as (X1 & X2 & _ & X4 & X5 & _). ceil. unfold ASAN_CEIL in *. lia. Qed.
Lemma U2 : bv_unsigned (ew E0 2) = spZ regs. Proof. apply Uw; [exact E2w | exact R_sp]. Qed.
Lemma U10 : bv_unsigned (ew E0 10) = pa. Proof. apply Uw; [exact E10 | exact R_pa]. Qed.
Lemma U11 : bv_unsigned (ew E0 11) = inst. Proof. apply Uw; [exact E11 | exact R_inst]. Qed.
Lemma U13 : bv_unsigned (ew E0 13) = so. Proof. apply Uw; [exact E13 | exact (proj1 R_so)]. Qed.
Lemma U32 : bv_unsigned (ew E0 32) = T. Proof. apply Uw; [reflexivity | exact (proj1 R_T)]. Qed.
Lemma U33 : bv_unsigned (ew E0 33) = ly_C ly. Proof. apply Uw; [reflexivity | exact (proj2 R_T)]. Qed.
Lemma U44 : bv_unsigned (ew E0 44) = Bv. Proof. apply Uw; [reflexivity | exact (proj1 R_B64)]. Qed.
Lemma U47 : bv_unsigned (ew E0 47) = SLOTv. Proof. apply Uw; [reflexivity | exact (proj2 R_B64)]. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of DGgi.REG0.                                                                                        *)
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) ->
val_mem tfibsegs m0 a w x.
Proof.
intros a w x E. pose proof DV as [[_ _ _ HCONST _ _ _] _ _ _ _ _ _ _ _ _].
apply (cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) HCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) ->
val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. pose proof DV as [[_ _ _ HCONST _ _ _] _ _ _ _ _ _ _ _ _].
apply (cell_holds_val_mem B ly (w_H W) mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) HCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma chunk_lit : forall a (w : BinNums.N) x, val_mem tfibsegs m0 a (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 0 (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | rewrite Z.add_0_l; exact Hm]. Qed.
Lemma chunk_lit_at : forall base a (w : BinNums.N) x, val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SLit x))).
Proof. intros base a w x Hm Hx Hw. eapply chunk_ok_val; [reflexivity | exact Hx | exact Hw | exact Hm]. Qed.
Lemma chunk_atom : forall base a (w : BinNums.N) k d x, ew E0 k = w64 (x - d) -> 0 <= x - d < 2 ^ 64 ->
val_mem tfibsegs m0 (base + a) (N.to_nat w) x -> 0 <= x < 2 ^ (8 * Z.of_N w) -> Z.of_N w <= 8 ->
YP09.chunk_ok tfibsegs E0 m0 base (YP09.mkChunk a (CVal w (SOff k d))).
Proof.
intros base a w k d x Hk Hr Hm Hx Hw. eapply chunk_ok_val; [| exact Hx | exact Hw | exact Hm].
cbn [sv_denot]. rewrite Hk. unfold w64. rewrite Zbv_add_unsigned. f_equal. lia.
Qed.
Lemma offT : forall a, T <= a < T + kThreadObjSize -> off_img a.
Proof. intros a Ha. exact (zone3_off_img _ _ a (proj1 LYB) Ha). Qed.
Lemma offP : forall a, pa - 16 <= a < pa + 8 -> off_img a.
Proof. intros a Ha. pose proof N8_ge as [N8a _]. exact (zone3_off_img _ _ a (proj1 PZ) ltac:(lia)). Qed.
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) DGgi.REG0.
Proof.
pose proof DV as [[LY IMG HTSD HCONST HINST HIAL HUNW] _ _ _ HPR HSHP HJUNK _ _ _].
change (ly_tsd ly = TFIB_TSD) in HTSD.
pose proof LYB as (hT1 & hT2 & hP1 & hP2 & hP3 & hP4 & hC1 & hC2 & _ & _ & _ & _ & S1 & S2 & S3 & S4 & S5).
pose proof LYD3 as (_ & _ & _ & SC). pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6).
pose proof B_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & (BC0 & BC1) & B10 & B11 & B12).
pose proof R_B as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
pose proof DBV as [(V1 & V2 & V3 & V4) (V5 & V6) DBP _ _ _ _].
change (forall a, Bv + 8 <= a < Bv + 24 \/ (BCv < kBatchSlots /\ SLOTv <= a < SLOTv + 8) -> apresent (w_H W) mem a) in DBP.
pose proof R_sp as Usp. pose proof R_so as [Uso Ubp]. pose proof R_T as [UT UC]. pose proof R_inst as Uin.
pose proof HIO as (IO1 & IO2 & IO3). destruct hT1 as (hT1a & hT1b & _). destruct hC1 as (hC1a & hC1b & _).
ceil; unfold ASAN_CEIL in *.
unfold DGgi.REG0, DGgi.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aQS, aQF, aQB, aB, aBB, aBC, aSLOT, aHW, aN, aINST, aSO, aBP, aLEN.
nums.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{ reg_intro. rewrite U13. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
  apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (chunk_atom so 0 8 12%nat 0 bp); [rewrite Z.sub_0_r; exact E12 | lia | rewrite Z.add_0_r; exact PSO | r8 | cbn; lia].
  - apply (chunk_atom so 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | lia | exact PLEN | r8 | cbn; lia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{ apply (region_ok_stack tfibsegs E0 m0 2 (spZ regs) (- 8192)); [exact U2 | lia | lia |].
  intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END; lia | apply HPRES; lia]. }
(* the two empty slots *)
do 2 (apply Forall_cons; [reg_intro; rewrite U2; split; [lia|]; split; [lia|]; split; [intros o Ho; lia | apply Forall_nil] |]).
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 2147450880); [reflexivity | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 11 (apply Forall_cons; [lit_region|]).
(* the instance's quarantine fields, based at aINST *)
apply Forall_cons. { reg_intro. rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact (proj1 HINST) | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. rewrite U11. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact (proj2 HINST) | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (6139696 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite Z.sub_0_r; reflexivity | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 6275800 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite U33.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite Z.sub_0_r; reflexivity | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite U32.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite Z.sub_0_r; reflexivity | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite Z.sub_0_r; reflexivity | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan));
  [change (ew E0 35) with (w64 (ly_top ly)); unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
(* the thread's quarantine cache *)
apply Forall_cons. { reg_intro. rewrite U32.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 88); [|destruct (Z_lt_le_dec o 96); [|destruct (Z_lt_le_dec o 104)]];
  [ apply (val_mem_writable _ _ _ _ _ _ V1) | apply (val_mem_writable _ _ _ _ _ _ V2) | apply (val_mem_writable _ _ _ _ _ _ V3) | apply (val_mem_writable _ _ _ _ _ _ V4) ];
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [lia | apply offT; unfold kThreadObjSize; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 48%nat 0 QSv); [rewrite Z.sub_0_r; reflexivity | lia | exact V1 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 49%nat 0 QFv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V2 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 44%nat 0 Bv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V3 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 50%nat 0 QBv); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact V4 | lia] | r8 | cbn; lia]. }
(* the unwinding flag *)
apply Forall_cons. { reg_intro. rewrite U32.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ _ _ HUNW); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; first [lia | apply offT; unfold kThreadObjSize; lia]. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact HUNW | cbn; lia | cbn; lia]. }
(* the thread's stats words *)
apply Forall_cons. { reg_intro. rewrite U32.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply offT; unfold kThreadObjSize; lia | apply HJUNK; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 51%nat 0 j1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 52%nat 0 j2); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J2 | lia] | r8 | cbn; lia]. }
(* the chunk header *)
apply Forall_cons. { reg_intro. rewrite U10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply offP; lia | apply HPR; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 4 38%nat 0 HWv); [rewrite Z.sub_0_r; reflexivity | unfold DGgi.HWv; lia | replace (pa + -16) with (pa - 16) by lia; exact W1 | unfold DGgi.HWv; r4 | cbn; lia].
- apply (chunk_atom _ _ 4 39%nat 0 nn); [rewrite Z.sub_0_r; reflexivity | lia | replace (pa + -12) with (pa - 12) by lia; exact W2 | r4 | cbn; lia]. }
(* the block's first word *)
apply Forall_cons. { reg_intro. rewrite U10.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable_off; [apply offP; lia | apply HPR; lia]. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 53%nat 0 j3); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact J3 | r8 | cbn; lia]. }
(* the last batch's byte and item counts *)
apply Forall_cons. { reg_intro. rewrite U44.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply apresent_writable; [unfold TFIB_IMG_END; lia | apply DBP; left; lia]. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 45%nat 0 BBv); [rewrite Z.sub_0_r; reflexivity | lia | exact V5 | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 46%nat 0 BCv); [rewrite Z.sub_0_r; reflexivity | lia | exact V6 | r8 | cbn; lia]. }
(* the free slot *)
apply Forall_cons; [|apply Forall_nil]. { reg_intro. rewrite U47.
split; [lia|]. split; [lia|]. split; [|apply Forall_nil].
intros o Ho. apply apresent_writable; [unfold TFIB_IMG_END; lia | apply DBP; right; split; [exact BC1 | lia]]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of DGgi.REG0 are pairwise disjoint.                                                                  *)
Local Ltac pl ZT ZC ZP DTC BT BC DPT DPC DPB :=
first [ clear ZT ZC ZP DTC BT BC DPT DPC DPB; lia
| clear ZC ZP DTC BT BC DPT DPC DPB; lia
| clear ZT ZP DTC BT BC DPT DPC DPB; lia
| clear ZT ZC DTC BT BC DPT DPC DPB; lia
| clear ZT ZC ZP BT BC DPT DPC DPB; lia
| clear ZT ZC ZP DTC BC DPT DPC DPB; lia
| clear ZT ZC ZP DTC BT DPT DPC DPB; lia
| clear ZT ZC ZP DTC BT BC DPC DPB; lia
| clear ZT ZC ZP DTC BT BC DPT DPB; lia
| clear ZT ZC ZP DTC BT BC DPT DPC; lia ].
Lemma PAIRS_ok : pairwise_disjoint E0 DGgi.REG0.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hP2 & hP3 & hP4 & hC1 & hC2 & _ & _ & _ & _ & S1 & S2 & S3 & S4 & S5).
pose proof LYD3 as (DPT & DPC & DTC & SC).
pose proof p_facts as (P1 & P2 & P3 & _ & _ & _). pose proof PZ as ((P1a & P1b & ZP) & _).
pose proof B_facts as (B1 & B2 & _ & _ & _ & _ & _ & _ & (BC0 & BC1) & _ & _ & DPB).
pose proof R_B as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
pose proof blk_ivs as (BT & BC). pose proof R_sp as Usp. pose proof HIO as (IO1 & IO2 & _).
destruct hT1 as (T1a & T1b & ZT). destruct hC1 as (C1a & C1b & ZC).
unfold zdisjoint in DPT, DPC, DTC. cbn [fst snd] in DPT, DPC, DTC. unfold DGgi.PBDISJ in DPB.
apply pairwise_disjoint_of_extents. unfold DGgi.REG0, DGgi.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aQS, aQF, aQB, aB, aBB, aBC, aSLOT, aHW, aN, aINST, aSO, aBP, aLEN.
rewrite U2, U10, U11, U13, U32, U33, U44, U47.
ceil.
clear - CR CR0 SC Hlo Hhi S4 Hso1 Hso2 T1a T1b ZT C1a C1b ZC P1 P2 P3 P1a P1b ZP IO1 IO2 hP1 hP2 hP3 hP4 B1 B2 BC0 BC1 RB1 RB2 RB3 RB4 RB5 RB6
  DPT DPC DTC BT BC DPB Usp.
unfold ASAN_CEIL in *. unfold zone3cases in ZT, ZC, ZP. nums. unfold TFIB_TP, TFIB_TSD in *.
cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
repeat split; pl ZT ZC ZP DTC BT BC DPT DPC DPB.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of DGgi.FFG: the frame atoms, then the released facts (AFeq.FF without its sp fact).                    *)
Lemma FACTS_ok : facts_ok E0 DGgi.FFG.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hP2 & hP3 & hP4 & hC1 & hC2 & _ & _ & _ & _ & S1 & S2 & S3 & S4 & S5).
pose proof LYD3 as (_ & _ & _ & SC). pose proof LYAL as (TAL & CAL & SAL & TOPAL).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6).
pose proof B_facts as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & (BC0 & BC1) & (Q1 & Q2) & B11 & _).
pose proof R_B as (RB1 & RB2 & RB3 & RB4 & RB5 & RB6).
pose proof IM_facts as (IM1 & IM2). pose proof SP_facts as (SP1 & SP2). pose proof N8_facts as (N1 & N2 & N3).
pose proof R_sp as Usp. pose proof HIO as (IO1 & IO2 & IO3).
pose proof DV as [[LY _ _ _ _ _ _] _ _ _ _ _ _ _ _ _]. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
destruct hT1 as (T1a & T1b & _). destruct hC1 as (C1a & C1b & _).
assert (SLAL : SLOTv mod 8 = 0).
{ rewrite RB6. apply Z.mod_divide in B4 as [c Hc]; [|lia]. rewrite Hc. apply Z.mod_divide; [lia|]. exists (c * 1024 + 3 + BCv). lia. }
assert (BAL : Bv mod 2 ^ 13 = 0) by exact B4.
assert (LEN : 1 <= Z.of_nat (length tr) <= 30) by lia.
ceil; unfold ASAN_CEIL in *. nums.
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX.
  split; [exact HB|]. split; [exact HM | exact HA]. }
assert (M1 : forall x, x mod 2 ^ 0 = 0) by (intros x; change (2 ^ 0) with 1; apply Z.mod_1_r).
unfold facts_ok, DGgi.FFG, frame_facts. cbn [f_atoms f_conds f_alias FF tl app atoms_ok conds_ok alias_ok].
split; [|split; exact I].
unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM, aHW, aN, aSP, aN8, aCNT8, aB, aBB, aBC, aSLOT, aQS, aQF, aQB, aJ1, aJ2, aJ3, aINST, aSO, aBP.
unfold kHighMemBeg, kHighMemEnd, DFSTACK, kBatchSlots, SHADOW_OFF.
(* the frame atoms: the entry sp, the instance, the stack object, the buffer *)
split. { apply (AF 2%nat (spZ regs)); [exact E2w | lia | lia | change (2 ^ 4) with 16; exact Hal | lia]. }
split. { apply (AF 11%nat inst); [exact E11 | lia | lia | change (2 ^ 3) with 8; exact IO3 | lia]. }
split. { apply (AF 13%nat so); [exact E13 | lia | lia | change (2 ^ 3) with 8; exact Hso3 | lia]. }
split. { apply (AF 12%nat bp); [exact E12 | lia | lia | change (2 ^ 3) with 8; exact Hbp3 | lia]. }
(* the released facts *)
split. { apply (AF 10%nat pa); [exact E10 | lia | lia | change (2 ^ 4) with 16; exact P5 | lia]. }
split. { apply (AF 32%nat T); [reflexivity | lia | lia | exact TAL | lia]. }
split. { apply (AF 33%nat (ly_C ly)); [reflexivity | lia | lia | exact CAL | lia]. }
split. { apply (AF 34%nat SB); [reflexivity | lia | lia | exact SAL | lia]. }
split. { apply (AF 35%nat (ly_top ly)); [reflexivity | lia | lia | exact TOPAL | lia]. }
split. { apply (AF 36%nat (Z.of_nat (length tr))); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 37%nat IMv); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact IM2 | lia]. }
split. { apply (AF 38%nat HWv); [reflexivity | unfold DGgi.HWv; lia | unfold DGgi.HWv; lia | apply M1 | lia]. }
split. { apply (AF 39%nat nn); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 40%nat 2147450880); [reflexivity | lia | lia | reflexivity | lia]. }
split. { apply (AF 41%nat SPv); [reflexivity | lia | lia | change (2 ^ 1) with 2; exact SP2 | lia]. }
split. { apply (AF 42%nat N8v); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact N2 | lia]. }
split. { apply (AF 43%nat CNT8v); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 44%nat Bv); [reflexivity | lia | lia | exact BAL | lia]. }
split. { apply (AF 45%nat BBv); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 46%nat BCv); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 47%nat SLOTv); [reflexivity | lia | lia | change (2 ^ 3) with 8; exact SLAL | lia]. }
split. { apply (AF 48%nat QSv); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 49%nat QFv); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 50%nat QBv); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 51%nat j1); [reflexivity | lia | lia | apply M1 | lia]. }
split. { apply (AF 52%nat j2); [reflexivity | lia | lia | apply M1 | lia]. }
split; [|exact I]. { apply (AF 53%nat j3); [reflexivity | lia | lia | apply M1 | lia]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine registers at Deallocate's entry are REGS_G over E0.                                                  *)
Lemma HUo : forall r : bv 5, bv_unsigned r <> 10 -> bv_unsigned r <> 11 -> bv_unsigned r <> 12 -> bv_unsigned r <> 13 ->
getr regs r = getr regs0 r.
Proof. intros r A1 A2 A3 A4. symmetry. apply dregs_other; assumption. Qed.
Lemma HU10 : getr regs 10%bv = getr regs0 11%bv. Proof. transitivity (w64 inst); [exact H10 | symmetry; apply dregs_11]. Qed.
Lemma HU11 : getr regs 11%bv = getr regs0 10%bv. Proof. transitivity (w64 pa); [exact H11 | symmetry; apply dregs_10]. Qed.
Lemma HU14 : getr regs 14%bv = getr regs0 13%bv. Proof. transitivity (w64 so); [exact H14 | symmetry; apply dregs_13]. Qed.
Lemma HTP4 : getr regs 4%bv = w64 TFIB_TP. Proof. rewrite <- (ts_tp B TS). exact Htp. Qed.
Local Ltac reg_atom :=
first
[ cbn [sv_denot]; unfold DGgi.E0; rewrite Z.add_0_r, ew_Ereg_lt by lia;
  match goal with |- _ = Z_to_bv 64 (bv_unsigned (getr _ ?x)) => let y := eval vm_compute in x in change x with y end;
  rewrite Z_to_bv_bv_unsigned; reflexivity
| cbn -[Z_to_bv getr dregs];
  repeat match goal with |- context [Z.of_nat ?k] => let y := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with y end;
  rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity ].
Local Ltac reg_case :=
match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) => let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end;
first
[ transitivity (Z_to_bv 64 0); [apply getr_zero | reflexivity]
| transitivity (getr regs0 11%bv); [exact HU10 | reg_atom]
| transitivity (getr regs0 10%bv); [exact HU11 | reg_atom]
| transitivity (getr regs0 13%bv); [exact HU14 | reg_atom]
| transitivity (w64 0); [exact H12 | reflexivity]
| transitivity (w64 0); [exact H13 | reflexivity]
| transitivity (w64 1); [exact H15 | reflexivity]
| transitivity (w64 TFIB_TP); [exact HTP4 | reflexivity]
| rewrite HUo by rne; reg_atom ].
Lemma REGS_ok : regs_ok E0 REGS_G regs.
Proof.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [reg_case|]).
destruct Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed and the record.                                                                                         *)
Lemma SEED_ok : st_ok tfibsegs E0 DGgi.SS0 (restrict (w_H W) (mkst regs (w64 A_Deallocate) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold DGgi.SS0, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact REGS_ok|]. split; [|exact FACTS_ok].
split; [vm_compute; reflexivity|]. split; [exact REG0_ok | exact PAIRS_ok].
Qed.
Lemma SP_eq : bv_unsigned (getr regs0 2) = spZ regs.
Proof. unfold dregs. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. reflexivity. Qed.
Lemma SO_eq : bv_unsigned (getr regs0 13) = so.
Proof. assert (E : getr regs0 13 = w64 so) by exact (dregs_13 regs pa inst bp so). rewrite E. unfold w64. apply unsigned_lit_small. exact (proj1 R_so). Qed.
Lemma BP_eq : bv_unsigned (getr regs0 12) = bp.
Proof. assert (E : getr regs0 12 = w64 bp) by exact (dregs_12 regs pa inst bp so). rewrite E. unfold w64. apply unsigned_lit_small. exact (proj2 R_so). Qed.
Lemma INST_eq : bv_unsigned (getr regs0 11) = inst.
Proof. assert (E : getr regs0 11 = w64 inst) by exact (dregs_11 regs pa inst bp so). rewrite E. unfold w64. apply unsigned_lit_small. exact R_inst. Qed.
Lemma R1_eq : getr regs0 1 = getr regs 1.
Proof. unfold dregs. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. reflexivity. Qed.
Lemma R4_eq : getr regs0 4 = w64 TFIB_TP.
Proof. unfold dregs. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. rewrite getr_other by rne. exact HTP4. Qed.
Theorem FH_ok : DGgi.free_hyps W ly regs0 mem tr pa nn hb1 q lastb j1 j2 j3 regs.
Proof.
pose proof DV as [[LY IMG _ _ _ HIAL _] _ _ _ HPR HSHP _ (HZ1 & HZ2 & HZ3 & HZ4) HQB _].
pose proof DBV as [_ _ DBP (R1 & R2 & R3 & R4) DBD (D1 & D2 & D3) _].
pose proof SO_eq as ESO. pose proof BP_eq as EBP. pose proof INST_eq as EIN. pose proof SP_eq as ESP.
apply DGgi.FreeHyps.
- exact LY.
- exact (dregs_10 regs pa inst bp so).
- exact R4_eq.
- rewrite R1_eq. exact Hra.
- rewrite R1_eq. exact Hra4096.
- rewrite ESP. unfold DFSTACK, DFSTACK_G in *. lia.
- unfold DGgi.AL. rewrite ESP. exact Hal.
- exact Htrlen.
- rewrite ESP, ESO. lia.
- rewrite ESP, EBP. lia.
- rewrite EIN. exact HIO.
- exact HZ1.
- exact IMG.
- unfold DGgi.AL. exact HZ3.
- exact HZ4.
- exact Hb1.
- unfold DGgi.HB1MASK. exact Hb1m.
- exact HZ2.
- exact HPR.
- intros a Ha. apply HSHP. unfold dshadow. exact Ha.
- split; [intros E; rewrite E in Hrev; cbn in Hrev; discriminate Hrev|].
  split; [exact Hroom|]. split; [exact (proj1 HQB)|]. split; [exact Hqb|].
  split; [exact D1|]. split; [exact D2 | exact D3].
- rewrite Hrev. reflexivity.
- split; [exact R1|]. split; [exact R2 | exact R3].
- unfold DGgi.AL. exact R4.
- exact DBD.
- intros a [Ha|Ha]; apply DBP; [left; exact Ha | right; split; [exact Hroom | exact Ha]].
- split; [exact J1R|]. split; [exact J2R | exact J3R].
- exact HIAL.
- exact SEED_ok.
- intros i Hi. rewrite EBP. exact (PBUF i Hi).
Qed.
End h.

(* The seed of the arm "the last batch has room", from Deallocate's generic precondition and the view. *)
Theorem FH_c : forall U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> inst_ok inst -> dview B W ly inst mem S p n ->
rev (qc_list (st_qthread S)) = lastb :: initr -> Z.of_nat (length (b_items lastb)) < kBatchSlots ->
qc_bytes (st_qthread S) + req_size n <= kQuarantineCacheMax ->
exists hb1 j1 j2 j3,
0 <= hb1 < 256 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
DGgi.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) lastb j1 j2 j3 regs.
Proof.
intros U ARX rpre fpre inst so bp ly S W regs mem md p n tr lastb initr PRE HBLK HIO DV Hrev Hroom Hqb.
destruct PRE as (_ & _ & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & HPRES & _ & Htp & H10 & H11 & H12 & H13 & H14 & H15 &
  Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & _ & _ & _).
pose proof DV as [_ _ _ (hb1 & Hb1 & Hb1m & W1 & W2) HPR _ HJUNK _ _ _].
destruct (vis_word (w_H W) mem (ly_T ly + t_stats + 24)) as (j1 & J1R & J1 & _).
{ intros i Hi. apply apresent_vis. apply HJUNK. lia. }
destruct (vis_word (w_H W) mem (ly_T ly + t_stats + 32)) as (j2 & J2R & J2 & _).
{ intros i Hi. apply apresent_vis. apply HJUNK. lia. }
destruct (vis_word (w_H W) mem (sptr_addr B ly p)) as (j3 & J3R & J3 & _).
{ intros i Hi. apply apresent_vis. apply HPR. lia. }
exists hb1, j1, j2, j3. split; [exact Hb1|]. split; [exact W1|].
eapply FH_ok; eassumption.
Qed.
End g.
End f.
About FH_c.
