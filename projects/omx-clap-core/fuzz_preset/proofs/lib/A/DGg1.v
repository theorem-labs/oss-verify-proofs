(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGg1.v (a working branch 29b7505aa27, file sha256 2b6258d6474c) onto omx-clap-core/fuzz_preset's asan image (unstripped fuzz_preset.asan, sha256 f0d2e8d40c7e; pin d83eb25dbf0d); module paths changed; its 24 image addresses moved by code-verified function pairs (12 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 1 code pcs the tool read as sizes, by the internal file funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction, and 5 pcs named in comments; 12 hand maps (the internal file agreloc-resolve-A.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); 2 model labels (YG00 mcheck / spin tags) kept; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: relocated from the old pin A (pinned fuzz_preset.asan d83eb25dbf0d, twin f0d2e8d40c7e; this file at 3d44582d342f) to A' (#102 pin 1be0f53d96cb, twin bff8519bbe3e) by the relocation route of record, frozen alreloc ced0368250cb6538 (a working branch b85bfdee67c4), --assume-source, --resolve the internal file resolve-102.txt (4 lines name this file); 29 numerals changed. *)
(* Modified by Theorem Labs, 2026-10-30: a Theorem Labs lane's MP delta to proofs/cgif/cgif_file_fuzzer/lib/DGg1.v (84ee52cd012 -> a working branch 5ad50e61fc6a, file sha256 5842e5fc5f09) applied at A' by the 3-way merge of record (the internal file p2merge.sh: base = the 84ee52cd012 text relocated cgif -> A', theirs = the 5ad50e61fc6a text relocated the same way, ours = this file): the call rules take the call memory MP first, as lib/Reusable/MnEnq.v now does. 0 conflicts; the added lines equal the source delta's; no numeral in the delta. *)
(* Modified by Theorem Labs, 2026-10-30: the cf layer's dv_zone bound change (proofs/cgif/cgif_file_fuzzer/lib/DGg1.v at 8e0ff8e049b4 -> 002b8cc32f7e, the request bound `1 <= nn < 2 ^ 28` -> `<= 2 ^ 28`) applied at A' by the 3-way merge of record (the internal file p2merge.sh), as round 6h did for the B' copies; 0 conflicts; no numeral in the delta. *)
(* The seed of the frame-generic Deallocate walk, arms mid and drain (DGgm.free_hyps), from the generic precondition
   DeallocG.dealloc_pre and the interface view DGif0.dview.

   The actual registers at Deallocate's entry are [regs]; the walk's environment is DGgm.E0 over the virtual register
   file [dregs regs pa inst bp so] (x10 = the block address, x11 = this, x12 = the trace buffer, x13 = the stack object).
   The region-by-region scripts are the released YFg1 ones (REG0_ok, PAIRS_ok, FACTS_ok, SEED_ok, FH_ok); the facts that
   came from the allocator model now come from dview (the constant cells, the instance words, the header, the block's
   zone, the presence of the written cells) and from the layout (layout_ok, img_cover).

   [to_enq] is the walk shared by the mid and drain arms, over the interface DGif0.DIface: from Deallocate's entry
   through DGgd.segB, StackDepotPut (di_depot), the model's depot answer and the chunk's change, and DGgf.segCm1 to
   Put's call of QuarantineCache::Enqueue (0x36a74, DGfw.SS_E), where the memory is DGif0.dmem_m. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YP0j.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YN3v YI04.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YK04 YA0i YA0n YA0o YA0p YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YG00 YG0a YG01 YG04 YG03 YG0f YG0v YG0n YG0d YG0s YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1v AB1q AB1t AF0l AF0m AF0x AFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AB1w AE3d AFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AGImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import DGbase DGgm.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import AImgA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require Import ADIfaceA.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.A Require DGfv DGfw DGgd DGgf AFew AFeu.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YM05.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Ltac ceil := try (let H := fresh "CR" in let H2 := fresh "CR" in pose proof (proj1 (@YG0f.ASAN_CEIL_range _)) as H; pose proof H as H2; unfold YG0f.ASAN_CEIL in H2).
Local Set Warnings "-abstract-large-number".
Local Set Warnings "-notation-for-abbreviation".
Open Scope Z_scope.
Set Printing Depth 100. Set Printing Width 200.
Section f. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* A word of eight present bytes.                                                                                   *)
Lemma aview_vis_byte : forall H mem a, aview tfibsegs H mem a <> None ->
exists b, aview tfibsegs H mem a = Some b /\ 0 <= b < 256 /\ mbyte tfibsegs (mrestrict H mem) a = Some (Z_to_bv 8 b).
Proof.
intros H mem a Hv. destruct (aview tfibsegs H mem a) as [b|] eqn:E; [|exfalso; exact (Hv eq_refl)].
exists b. split; [reflexivity|]. pose proof E as E'. apply aview_some in E as (b8 & Hb & <-).
pose proof (bv_unsigned_in_range 8 b8) as R. change (bv_modulus 8) with 256 in R. split; [lia|]. exact (aview_byte _ _ _ _ E').
Qed.
Lemma pres_word : forall H mem a, (forall i, 0 <= i < 8 -> apresent H mem (a + i)) ->
exists w, 0 <= w < 2 ^ 64 /\ val_mem tfibsegs (mrestrict H mem) a 8 w.
Proof.
intros H mem a Hp.
assert (Hv : forall i, 0 <= i < 8 -> aview tfibsegs H mem (a + i) <> None).
{ intros i Hi. destruct (apresent_mbyte H mem (a + i) (Hp i Hi)) as [b Hb]. unfold aview. rewrite Hb. discriminate. }
destruct (aview_vis_byte H mem (a + 0) (Hv 0 ltac:(lia))) as (b0 & E0 & R0 & M0).
destruct (aview_vis_byte H mem (a + 1) (Hv 1 ltac:(lia))) as (b1 & E1 & R1 & M1).
destruct (aview_vis_byte H mem (a + 2) (Hv 2 ltac:(lia))) as (b2 & E2 & R2 & M2).
destruct (aview_vis_byte H mem (a + 3) (Hv 3 ltac:(lia))) as (b3 & E3 & R3 & M3).
destruct (aview_vis_byte H mem (a + 4) (Hv 4 ltac:(lia))) as (b4 & E4 & R4 & M4).
destruct (aview_vis_byte H mem (a + 5) (Hv 5 ltac:(lia))) as (b5 & E5 & R5 & M5).
destruct (aview_vis_byte H mem (a + 6) (Hv 6 ltac:(lia))) as (b6 & E6 & R6 & M6).
destruct (aview_vis_byte H mem (a + 7) (Hv 7 ltac:(lia))) as (b7 & E7 & R7 & M7).
set (w := b0 + 256 * (b1 + 256 * (b2 + 256 * (b3 + 256 * (b4 + 256 * (b5 + 256 * (b6 + 256 * b7))))))).
exists w. split; [subst w; lia|].
assert (LB : forall k, (k < 8)%nat -> YO0f.le_byte w 8 k = nth k [b0; b1; b2; b3; b4; b5; b6; b7] 0).
{ intros k Hk. unfold YO0f.le_byte. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64). rewrite (Z.mod_small w (2 ^ 64)) by (subst w; lia).
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ];
[ change (2 ^ (8 * 0)) with 1 | change (2 ^ (8 * 1)) with 256 | change (2 ^ (8 * 2)) with 65536 | change (2 ^ (8 * 3)) with 16777216
| change (2 ^ (8 * 4)) with 4294967296 | change (2 ^ (8 * 5)) with 1099511627776 | change (2 ^ (8 * 6)) with 281474976710656
| change (2 ^ (8 * 7)) with 72057594037927936 ]; subst w; Z.div_mod_to_equations; nia. }
intros k Hk. rewrite (LB k Hk). rewrite Z.add_0_r in M0.
destruct k as [|[|[|[|[|[|[|[|k]]]]]]]]; [| | | | | | | |lia]; cbn [nth Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite ?Z.add_0_r; assumption.
Qed.
(* A byte of a value in memory is writable when it is off the image. *)
Lemma val_mem_writable : forall (m : word -> option byte) a (w : nat) v o, val_mem tfibsegs m a w v -> a <= o < a + Z.of_nat w -> off_img o ->
writable_at tfibsegs m o.
Proof.
intros m a w v o Hv Ho Hoff. pose proof (Hv (Z.to_nat (o - a)) ltac:(lia)) as M.
replace (a + Z.of_nat (Z.to_nat (o - a))) with o in M by lia. exact (mbyte_off_writable _ _ _ Hoff M).
Qed.

Section g.
Variable B : asyms.
Hypothesis TS : TfibSyms B.

Section h.
Variables (W : world tfibsegs) (ly : alayout) (S : astate) (regs : bvmap 5 word) (mem : word -> option byte).
Variables (inst so bp : Z) (p : sptr) (n : Z) (tr : list Z) (hb1 j1 j2 j3 : Z).
Local Notation pa := (sptr_addr B ly p).
Local Notation nn := (req_size n).
Local Notation sp0 := (bv_unsigned (getr regs 2)).
Local Notation regs0 := (dregs regs (sptr_addr B ly p) inst bp so).
Local Notation m0 := (mrestrict (w_H W) mem).
Local Notation T := (ly_T ly).
Local Notation SB := (ly_space ly).
Local Notation q := (st_qthread S).
Local Notation E0 := (DGgm.E0 ly regs0 tr pa nn hb1 q j1 j2 j3).
Local Notation LENv := (DGgm.LENv tr).
Local Notation IMv := (DGgm.IMv pa).
Local Notation HWv := (DGgm.HWv hb1).
Local Notation SPv := (DGgm.SPv pa).
Local Notation N8v := (DGgm.N8v nn).
Local Notation CNT8v := (DGgm.CNT8v nn).
Local Notation QBFv := (DGgm.QBFv nn q).
(* The interface view and the instance. *)
Hypothesis DV : dview B W ly inst mem S p n.
Hypothesis HIO : inst_ok inst.
(* The facts of DeallocG.dealloc_pre the seed reads. *)
Hypothesis Hra : YK0s.ret_ok (getr regs 1).
Hypothesis Hra4096 : 4096 <= raZ regs.
Hypothesis Hal : spZ regs mod 16 = 0.
Hypothesis Hlo : ly_stk_lo ly + DFSTACK_G <= spZ regs.
Hypothesis Hbot : ly_bot ly < spZ regs.
Hypothesis Hhi : spZ regs <= ly_stk_hi ly.
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
Hypothesis PSO : val_mem tfibsegs (mrestrict (w_H W) mem) so 8 bp.
Hypothesis PLEN : val_mem tfibsegs (mrestrict (w_H W) mem) (so + 8) 8 (Z.of_nat (length tr)).
Hypothesis PBUF : forall i, (i < length tr)%nat -> val_mem tfibsegs (mrestrict (w_H W) mem) (bp + 8 * Z.of_nat i) 8 (nth i tr 0).
(* The chunk header's second byte (dview's dv_hdr) and the words at T + t_stats + 24 / + 32 and at the block. *)
Hypothesis Hhb : 0 <= hb1 < 256.
Hypothesis Hhbm : Z.land hb1 127 = 17.
Hypothesis HW1 : val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1).
Hypothesis HW2 : val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 12) 4 (req_size n).
Hypothesis HJ1R : 0 <= j1 < 2 ^ 64.
Hypothesis HJ1 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_stats + 24) 8 j1.
Hypothesis HJ2R : 0 <= j2 < 2 ^ 64.
Hypothesis HJ2 : val_mem tfibsegs (mrestrict (w_H W) mem) (ly_T ly + t_stats + 32) 8 j2.
Hypothesis HJ3R : 0 <= j3 < 2 ^ 64.
Hypothesis HJ3 : val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p) 8 j3.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The fields of the view.                                                                                          *)
Lemma vN : dview_n B W ly inst mem. Proof. destruct DV as [X _ _ _ _ _ _ _ _ _]. exact X. Qed.
Lemma vLY : layout_ok ly. Proof. destruct vN as [X _ _ _ _ _ _]. exact X. Qed.
Lemma vIMG : img_cover ly. Proof. destruct vN as [_ X _ _ _ _ _]. exact X. Qed.
Lemma vTSD : ly_tsd ly = TFIB_TSD. Proof. destruct vN as [_ _ X _ _ _ _]. exact X. Qed.
Lemma vCONST : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly). Proof. destruct vN as [_ _ _ X _ _ _]. exact X. Qed.
Lemma vINST : val_mem tfibsegs m0 (inst + 0x318) 8 0x10000000 /\ val_mem tfibsegs m0 (inst + 0x328) 8 0x100000.
Proof. destruct vN as [_ _ _ _ X _ _]. exact X. Qed.
Lemma vIAL : DGgm.IAL_POST W mem. Proof. destruct vN as [_ _ _ _ _ X _]. exact X. Qed.
Lemma vUNW : val_mem tfibsegs m0 (T + t_unwinding) 1 0. Proof. destruct vN as [_ _ _ _ _ _ X]. exact X. Qed.
Lemma vPRES : forall a, pa - 16 <= a < pa + 8 -> apresent (w_H W) mem a. Proof. destruct DV as [_ _ _ _ X _ _ _ _ _]. exact X. Qed.
Lemma vSHPRES : forall a, dshadow pa nn a -> apresent (w_H W) mem a. Proof. destruct DV as [_ _ _ _ _ X _ _ _ _]. exact X. Qed.
Lemma vZONE : zone3 (pa - 16) (N8v + 16) /\ DGgm.PSTATIC ly pa nn /\ pa mod 16 = 0 /\ 1 <= nn <= 2 ^ 28.
Proof. destruct DV as [_ _ _ _ _ _ _ X _ _]. exact X. Qed.
Lemma vQB : 0 <= qc_bytes q <= kQuarantineCacheMax. Proof. destruct DV as [_ _ _ _ _ _ _ _ X _]. exact X. Qed.
Lemma cell_lit : forall a (w : nat) x, cell_lookup (Tfib_const ly) (ANum a) = Some (ACell (ANum a) w (AV (ANum x))) -> val_mem tfibsegs m0 a w x.
Proof.
intros a w x E. apply (cell_holds_val_mem B ly (w_H W) mem (ANum a) w (ANum x)).
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) vCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.
Lemma cell_sym : forall e (w : nat) e', cell_lookup (Tfib_const ly) e = Some (ACell e w (AV e')) -> val_mem tfibsegs m0 (aeval B ly e) w (aeval B ly e').
Proof.
intros e w e' E. apply (cell_holds_val_mem B ly (w_H W) mem e w e').
apply (proj1 (Forall_forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly)) vCONST).
rewrite (ts_const B TS ly). exact (cell_lookup_In _ _ _ E).
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The virtual register file and the environment.                                                                   *)
Lemma G1 : getr regs0 1 = getr regs 1. Proof. apply dregs_other; vm_compute; discriminate. Qed.
Lemma G2 : getr regs0 2 = getr regs 2. Proof. apply dregs_other; vm_compute; discriminate. Qed.
Lemma G4 : getr regs0 4 = getr regs 4. Proof. apply dregs_other; vm_compute; discriminate. Qed.
Lemma G10 : getr regs0 10 = w64 pa. Proof. exact (dregs_10 regs pa inst bp so). Qed.
Lemma G11 : getr regs0 11 = w64 inst. Proof. exact (dregs_11 regs pa inst bp so). Qed.
Lemma G12 : getr regs0 12 = w64 bp. Proof. exact (dregs_12 regs pa inst bp so). Qed.
Lemma G13 : getr regs0 13 = w64 so. Proof. exact (dregs_13 regs pa inst bp so). Qed.
Lemma Hr4 : getr regs 4 = w64 TFIB_TP. Proof. rewrite Htp, (ts_tp B TS). reflexivity. Qed.
Lemma E2' : ew E0 2 = getr regs 2. Proof. rewrite <- G2. apply DGgm.E2. Qed.
Lemma E10' : ew E0 10 = w64 pa. Proof. rewrite <- G10. apply DGgm.E10. Qed.
Lemma E11' : ew E0 11 = w64 inst. Proof. rewrite <- G11. apply DGgm.E11. Qed.
Lemma E12' : ew E0 12 = w64 bp. Proof. rewrite <- G12. apply DGgm.E12. Qed.
Lemma E13' : ew E0 13 = w64 so. Proof. rewrite <- G13. apply DGgm.E13. Qed.
Lemma EaT' : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC' : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaTOP' : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The layout (DGgm.LYB / LYD over the view) and the block.                                                         *)
Lemma LYB :
zone3 T kThreadObjSize /\ T + kThreadObjSize <= ASAN_CEIL /\ kHighMemBeg <= ly_prim ly /\ ly_prim ly <= SB /\
SB + kSpaceSize + 4096 <= ly_prim ly + kPrimResvSize /\ ly_prim ly + kPrimResvSize <= ASAN_CEIL /\
zone3 (ly_C ly) 256 /\ ly_C ly + 256 <= ASAN_CEIL /\ zone3 (ly_NB ly) kNodesBlockSize /\ ly_NB ly + kNodesBlockSize <= ASAN_CEIL /\
zone3 (ly_SB ly) kStoreBlockSize /\ ly_SB ly + kStoreBlockSize <= ASAN_CEIL /\
ly_stk_lo ly <= ly_bot ly /\ ly_bot ly < ly_top ly /\ ly_top ly <= ly_stk_hi ly /\ ly_stk_hi ly <= kHighMemEnd /\ kHighMemBeg <= ly_stk_lo ly.
Proof.
pose proof vLY as LY. pose proof vIMG as IMG.
pose proof (lo_high ly LY) as IP. pose proof (lo_app ly LY) as HA. pose proof (lo_disj ly LY) as HD.
pose proof (lo_space_in ly LY) as HSP. pose proof (lo_top ly LY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof (Forall_nth_f _ _ 2 _ HA eq_refl) as IT. pose proof (Forall_nth_f _ _ 6 _ HA eq_refl) as IC.
pose proof (Forall_nth_f _ _ 4 _ HA eq_refl) as INB. pose proof (Forall_nth_f _ _ 5 _ HA eq_refl) as ISB.
cbn beta in IT, IC, INB, ISB. cbn [fst snd] in IT, IC, INB, ISB.
pose proof (zone3_intro ly (ly_T ly) kThreadObjSize IMG ltac:(clear_all; unfold kThreadObjSize; lia) IT (pairwise_ij_f _ _ 2 6 _ _ HD eq_refl eq_refl)) as ZT.
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
Lemma LYD :
let P := (ly_prim ly, kPrimResvSize) in let Tt := (ly_T ly, kThreadObjSize) in let NB := (ly_NB ly, kNodesBlockSize) in
let SBb := (ly_SB ly, kStoreBlockSize) in let C := (ly_C ly, 256) in let STK := (ly_stk_lo ly, ly_stk_hi ly - ly_stk_lo ly) in
(zdisjoint P Tt /\ zdisjoint P NB /\ zdisjoint P SBb /\ zdisjoint P C /\ zdisjoint P STK) /\
(zdisjoint Tt NB /\ zdisjoint Tt SBb /\ zdisjoint Tt C /\ zdisjoint Tt STK) /\
(zdisjoint NB SBb /\ zdisjoint NB C /\ zdisjoint NB STK) /\ (zdisjoint SBb C /\ zdisjoint SBb STK) /\ zdisjoint C STK.
Proof.
pose proof (lo_disj ly vLY) as HD. unfold static_extents, owned_extents in HD. cbn [pairwise app] in HD.
destruct HD as (DP & DQ & DT & DF & DNB & DSB & DC & _).
apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PT DP]. apply Forall_cons_iff in DP as [_ DP].
apply Forall_cons_iff in DP as [PNB DP]. apply Forall_cons_iff in DP as [PSB DP]. apply Forall_cons_iff in DP as [PC DP]. apply Forall_cons_iff in DP as [_ DP]. apply Forall_cons_iff in DP as [PSTK _].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TNB DT]. apply Forall_cons_iff in DT as [TSB DT]. apply Forall_cons_iff in DT as [TC DT].
apply Forall_cons_iff in DT as [_ DT]. apply Forall_cons_iff in DT as [TSTK _].
apply Forall_cons_iff in DNB as [NBSB DNB]. apply Forall_cons_iff in DNB as [NBC DNB]. apply Forall_cons_iff in DNB as [_ DNB]. apply Forall_cons_iff in DNB as [NBSTK _].
apply Forall_cons_iff in DSB as [SBC DSB]. apply Forall_cons_iff in DSB as [_ DSB]. apply Forall_cons_iff in DSB as [SBSTK _]. apply Forall_cons_iff in DC as [_ DC]. apply Forall_cons_iff in DC as [CSTK _].
cbn zeta. repeat split; assumption.
Qed.
Lemma N8_ge : 8 <= N8v /\ nn <= N8v < nn + 8.
Proof.
pose proof vZONE as (_ & _ & _ & HNN). unfold DGgm.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)). lia.
Qed.
(* The block [pa - 16, pa + N8v) avoids the stack, the thread object and the context object (dview's PSTATIC). *)
Lemma P_ivs : (pa + 8 <= ly_stk_lo ly \/ ly_stk_hi ly <= pa - 16) /\ (pa + 8 <= T \/ T + kThreadObjSize <= pa - 16) /\
(pa + 8 <= ly_C ly \/ ly_C ly + 256 <= pa - 16).
Proof.
pose proof vZONE as (_ & PS & _). pose proof N8_ge as [N8a _]. pose proof (lo_top ly vLY) as (T1 & T2 & _).
assert (G : forall lo hi, lo < hi -> (forall a, pa - 16 <= a < pa + N8v -> ~ (lo <= a < hi)) -> pa + 8 <= lo \/ hi <= pa - 16).
{ intros lo hi Hlh Hn. destruct (Z_lt_le_dec lo (pa + 8)); [|left; lia]. destruct (Z_lt_le_dec (pa - 16) hi); [|right; lia]. exfalso.
destruct (Z_lt_le_dec lo (pa - 16)).
- apply (Hn (pa - 16)); lia.
- apply (Hn lo); lia. }
split; [|split]; (apply G; [unfold kThreadObjSize; lia|]); intros a Ha; pose proof (PS a Ha) as X; cbv zeta in X; tauto.
Qed.
Lemma p_facts : 4096 + 16 <= pa /\ pa + N8v <= ASAN_CEIL /\ pa mod 16 = 0 /\ pa mod 8 = 0 /\ 8 <= N8v /\ nn <= N8v < nn + 8 /\ N8v mod 8 = 0 /\
1 <= LENv <= 30 /\ 0 <= IMv - 0xac0c0 <= 8 * 0x7fff /\ IMv mod 8 = 0 /\ SHADOW_OFF + 514 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ SPv mod 2 = 0 /\
CNT8v = (nn + 7) / 8.
Proof.
pose proof vZONE as (ZP & _ & P16 & HNN). destruct ZP as (Z1 & Z2 & _).
pose proof N8_ge as [N8a N8b].
pose proof P16 as P16'. apply Z.mod_divide in P16' as [c Hc]; [|lia].
assert (P8 : pa mod 8 = 0) by (rewrite Hc; replace (c * 16) with ((2 * c) * 8) by lia; apply Z_mod_mult).
assert (D8 : pa / 8 = 2 * c) by (rewrite Hc; replace (c * 16) with ((2 * c) * 8) by lia; apply Z_div_mult; lia).
assert (DN : N8v / 8 = (nn + 7) / 8) by (unfold DGgm.N8v; apply Z_div_mult; lia).
assert (N88 : N8v mod 8 = 0) by (unfold DGgm.N8v; apply Z_mod_mult).
assert (D32 : 0 <= pa / 2 ^ 32 <= 32767).
{ change (2 ^ 32) with 4294967296. split; [apply Z.div_pos; lia|].
pose proof (Z.div_le_mono pa 140737479966720 4294967296 ltac:(lia) ltac:(clear - Z2 N8a; ceil; unfold ASAN_CEIL in *; lia)) as X.
change (140737479966720 / 4294967296) with 32767 in X. exact X. }
assert (IM8 : (0xac0c0 + 8 * (pa / 2 ^ 32)) mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (88088 + pa / 2 ^ 32); lia).
assert (SP2 : (SHADOW_OFF + pa / 8) mod 2 = 0) by (rewrite D8; unfold SHADOW_OFF; apply Z.mod_divide; [lia|]; exists (1073725440 + c); lia).
assert (SPU : SHADOW_OFF + pa / 8 + N8v / 8 <= kHighMemBeg).
{ rewrite D8, DN. unfold DGgm.N8v in Z2. clear - Z2 Hc. ceil. unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg in *. lia. }
unfold DGgm.LENv, DGgm.IMv, DGgm.SPv, DGgm.CNT8v.
pose proof Htrlen as TL.
repeat split; first [assumption | lia].
Qed.
Lemma QB_facts : 0 <= qc_bytes q /\ QBFv <= DGgm.QBMAX /\ 1 <= nn <= 2 ^ 28.
Proof.
pose proof vQB as [Q1 Q2]. pose proof vZONE as (_ & _ & _ & HNN).
unfold DGgm.QBFv, DGgm.QBMAX. split; [lia|]. split; [|lia].
destruct (need_new_batch q); unfold kBatchBytes; lia.
Qed.
Lemma SO_range : 0 <= so /\ so + 16 < 2 ^ 64 /\ 0 <= bp /\ bp + 8 * 30 < 2 ^ 64.
Proof.
pose proof (lo_top ly vLY) as (_ & _ & _ & T4 & _). pose proof (u64_range (getr regs 2)).
unfold spZ in Hso1, Hbp1. unfold kHighMemEnd in T4. lia.
Qed.
Lemma INST_range : 0 <= inst /\ inst + 0xe60 < 2 ^ 64.
Proof. destruct HIO as (I1 & I2 & _). lia. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of DGgm.REG0 hold at the entry.                                                                      *)
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
Local Ltac offw := first [ lia
| apply (zone3_off_img _ _ _ (proj1 LYB)); unfold kThreadObjSize, t_qc, t_unwinding, t_stats, t_cache in *; lia
| apply (zone3_off_img _ _ _ (proj1 vZONE)); pose proof N8_ge; unfold DGgm.N8v in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) DGgm.REG0.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hSP1 & hSP2 & hP2 & hC1 & hC2 & hNB1 & hNB2 & hSB1 & hSB2 & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1, hNB1, hSB1.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (_ & _ & Q8). pose proof Hhb as HBR.
pose proof SO_range as (SR1 & SR2 & BR1 & BR2). pose proof INST_range as (IR1 & IR2).
pose proof HIO as (IO1 & IO2 & IO3). pose proof vINST as HINST. pose proof vTSD as HTSD.
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (S1 : ly_stk_lo ly + DFSTACK <= sp0) by exact Hlo.
assert (S2 : sp0 <= ly_stk_hi ly) by exact Hhi.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kHighShadowBeg, kQuarantineCacheMax, kBatchSlots in
hP1, hP2, hT1, hT2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, L4, L5, hSP1, hSP2, P1, P2, P11, P12.
unfold DGgm.REG0, DGgm.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8.
cbn [map combine seq length Z.of_nat Pos.of_succ_nat Pos.succ fst snd Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aHW, aN, aINST, aSO, aBP, aLEN.
(* the stack object at aSO: the buffer pointer and the trace length *)
apply Forall_cons.
{ reg_intro. rewrite E13'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom so 0 8 12%nat 0 bp); [rewrite Z.sub_0_r; exact E12' | lia | rewrite Z.add_0_r; exact PSO | r8 | cbn; lia].
- apply (chunk_atom so 8 8 36%nat 0 (Z.of_nat (length tr))); [rewrite Z.sub_0_r; reflexivity | lia | exact PLEN | r8 | cbn; lia]. }
(* the scratch window below the entry sp *)
apply Forall_cons.
{ apply (region_ok_stack tfibsegs E0 m0 2 sp0 (- DFSTACK)); [rewrite E2'; reflexivity | unfold DFSTACK in *; lia | lia |].
intros a Ha. apply apresent_writable; [unfold TFIB_IMG_END, DFSTACK in *; lia | apply HPRES; unfold spZ, DFSTACK_G; unfold DFSTACK in Ha; lia]. }
(* the two empty slots *)
do 2 (apply Forall_cons; [reg_intro; rewrite E2'; split; [lia|]; split; [lia|]; split; [intros o Ho; lia | apply Forall_nil] |]).
do 11 (apply Forall_cons; [lit_region|]).
apply Forall_cons. { reg_intro. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 40%nat 0 SHADOW_OFF); [reflexivity | unfold SHADOW_OFF; lia | | unfold SHADOW_OFF; cbn; lia | cbn; lia].
rewrite Z.add_0_l. apply cell_lit. vm_compute. reflexivity. }
do 11 (apply Forall_cons; [lit_region|]).
(* the instance's quarantine fields at aINST + 0x318 / + 0x328 *)
apply Forall_cons. { reg_intro. rewrite E11'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact (proj1 HINST) | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. rewrite E11'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit_at; [exact (proj2 HINST) | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (6151920 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC'; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 6288024 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite EaC'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_C ly + 8) with (aeval B ly (AC 8)) by reflexivity. apply (cell_sym (AC 8) 4 (ANum 0)). vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 32%nat 0 T); [rewrite EaT'; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_C ly + 152) with (aeval B ly (AC 152)) by reflexivity. replace T with (aeval B ly (AT 0)) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite EaT'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split; [intros o Ho; lia|].
apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]]]].
- apply (chunk_atom _ _ 8 33%nat 0 (ly_C ly)); [rewrite EaC'; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 0) with (aeval B ly (AT 0)) by (cbn; lia). replace (ly_C ly) with (aeval B ly (AC 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat 0 (ly_top ly)); [rewrite EaTOP'; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
replace (ly_T ly + 8) with (aeval B ly (AT 8)) by (cbn; lia). replace (ly_top ly) with (aeval B ly (ATop 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
- apply (chunk_atom _ _ 8 35%nat (- kStackSpan) (ly_top ly - kStackSpan)); [rewrite EaTOP'; unfold w64; f_equal; lia | unfold kStackSpan; lia | | unfold kStackSpan; cbn; lia | cbn; lia].
replace (ly_T ly + 16) with (aeval B ly (AT 16)) by (cbn; lia). replace (ly_top ly - kStackSpan) with (aeval B ly (ATop (- kStackSpan))) by (cbn; lia).
apply cell_sym. vm_compute. reflexivity.
- apply chunk_lit_at; [| cbn; lia | cbn; lia]. replace (ly_T ly + 40) with (aeval B ly (AT 40)) by (cbn; lia). apply (cell_sym (AT 40) 1 (ANum 0)). vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. rewrite EaT'. unfold w64. rewrite unsigned_lit_small by lia. unfold t_unwinding.
pose proof vUNW as U. unfold t_unwinding in U.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ _ U); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil]. apply chunk_lit_at; [exact U | cbn; lia | cbn; lia]. }
apply Forall_cons. { reg_intro. rewrite EaT'. unfold w64. rewrite unsigned_lit_small by lia. pose proof HJ1 as J1. pose proof HJ2 as J2. unfold t_stats in *.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o 2832); [apply (val_mem_writable _ _ _ _ _ J1) | apply (val_mem_writable _ _ _ _ _ J2)]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 8 51%nat 0 j1); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J1 | lia] | r8 | cbn; lia].
- apply (chunk_atom _ _ 8 52%nat 0 j2); [rewrite Z.sub_0_r; reflexivity | lia | eapply val_mem_addr; [exact J2 | lia] | r8 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite E10'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. destruct (Z_lt_le_dec o (-12)); [apply (val_mem_writable _ _ _ _ _ HW1) | apply (val_mem_writable _ _ _ _ _ HW2)]; cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
- apply (chunk_atom _ _ 4 38%nat 0 HWv); [rewrite Z.sub_0_r; reflexivity | unfold DGgm.HWv; lia | replace (pa + -16) with (pa - 16) by lia; exact HW1 | unfold DGgm.HWv; r4 | cbn; lia].
- apply (chunk_atom _ _ 4 39%nat 0 nn); [rewrite Z.sub_0_r; reflexivity | lia | replace (pa + -12) with (pa - 12) by lia; exact HW2 | r4 | cbn; lia]. }
apply Forall_cons. {   reg_intro. rewrite E10'. unfold w64. rewrite unsigned_lit_small by lia.
split; [lia|]. split; [lia|]. split.
{ intros o Ho. apply (val_mem_writable _ _ _ _ _ HJ3); cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; unfold TFIB_IMG_END; offw. }
apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom _ _ 8 53%nat 0 j3); [rewrite Z.sub_0_r; reflexivity | lia | rewrite Z.add_0_r; exact HJ3 | r8 | cbn; lia]. }
apply Forall_nil.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions are pairwise disjoint.                                                                               *)
Lemma PAIRS_ok : pairwise_disjoint E0 DGgm.REG0.
Proof.
pose proof LYB as (hT1 & hT2 & _ & _ & _ & _ & hC1 & hC2 & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
pose proof vZONE as (ZP & _). unfold zone3 in ZP.
pose proof LYD as (_ & (_ & _ & DTC & DTS) & _ & _ & DCS). unfold zdisjoint in DTC, DTS, DCS. cbn [fst snd] in DTC, DTS, DCS.
pose proof P_ivs as (DPS & DPT & DPC).
pose proof SO_range as (SR1 & SR2 & _). pose proof INST_range as (IR1 & IR2). pose proof HIO as (IO1 & IO2 & _).
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (S1 : ly_stk_lo ly + DFSTACK <= sp0) by exact Hlo.
assert (S2 : sp0 <= ly_stk_hi ly) by exact Hhi.
assert (SO1 : sp0 <= so) by exact Hso1.
apply pairwise_disjoint_of_extents. unfold DGgm.REG0, DGgm.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aHW, aN, aINST, aSO, aBP, aLEN.
rewrite E2', E10', E11', E13', EaT', EaC'. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, DFSTACK in *.
rewrite !unsigned_lit_small by lia.
clear - S1 S2 L4 L5 Usp SO1 Hso2 IO1 IO2 hT1 hT2 hC1 hC2 ZP P1 P2 P5 DTC DTS DCS DPS DPT DPC CR CR0.
unfold TFIB_TP, TFIB_TSD, t_qc, t_unwinding, t_stats in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1, ZP.
repeat split;
first [ clear DTC DTS DCS DPS DPT DPC hT1 hC1 ZP; lia
| clear - hT1 CR0 IO1 IO2; lia
| clear - hC1 CR0 IO1 IO2; lia
| clear - ZP P5 CR0 IO1 IO2; lia
| clear - hC1 hC2 hT1 hT2 DTC; lia
| clear - hC1 hC2 S1 S2 L4 L5 Usp SO1 Hso2 DCS; lia
| clear - hT1 hT2 S1 S2 L4 L5 Usp SO1 Hso2 DTS; lia
| clear - hC1 hC2 ZP P5 DPC; lia
| clear - hT1 hT2 ZP P5 DPT; lia
| clear - S1 S2 L4 L5 Usp SO1 Hso2 ZP P5 DPS; lia ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of DGgm.FFG: the frame atoms, then DGgm.FFM without its sp fact.                                       *)
Lemma FACTS_ok : facts_ok E0 DGgm.FFG.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hSP1 & hSP2 & hP2 & hC1 & hC2 & hNB1 & hNB2 & hSB1 & hSB2 & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1, hNB1, hSB1.
pose proof (lo_top ly vLY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (Qa & Qb & Q8). pose proof Hhb as HBR.
pose proof (lo_space_al ly vLY) as SAL. pose proof (lo_T_al ly vLY) as TAL. pose proof (lo_C_al ly vLY) as CAL. unfold page_aligned in TAL, T3.
pose proof HIO as (IO1 & IO2 & IO3). pose proof SO_range as (SR1 & SR2 & BR1 & BR2).
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (S1 : ly_stk_lo ly + DFSTACK <= sp0) by exact Hlo.
assert (S2 : sp0 <= ly_stk_hi ly) by exact Hhi.
assert (SO1 : sp0 <= so) by exact Hso1. assert (BP1 : sp0 <= bp) by exact Hbp1.
assert (Hal' : sp0 mod 16 = 0) by exact Hal.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kBatchSlots, kHighShadowBeg, kQuarantineCacheMax, DFSTACK in
hP1, hP2, hT1, hT2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, hSP1, hSP2, L4, L5, S1, S2, T2, T4, T7, P1, P2, P11, P12.
assert (E2'' : ew E0 2 = w64 sp0) by (rewrite E2'; unfold w64; symmetry; apply Z_to_bv_bv_unsigned).
assert (AF : forall k X lo hi al, ew E0 k = w64 X -> 0 <= X < 2 ^ 64 -> lo <= X <= hi -> X mod 2 ^ al = 0 -> 0 <= al <= 64 -> afact_ok E0 k (mkAF lo hi al)).
{ clear. intros k X lo hi al HE HX HB HM HA. unfold afact_ok. cbn [af_lo af_hi af_al2]. rewrite HE. unfold w64. rewrite unsigned_lit_small by exact HX. repeat split; lia. }
unfold facts_ok, DGgm.FFG, frame_facts. cbn [f_atoms f_conds f_alias DGgm.FFM tl app atoms_ok conds_ok alias_ok].
split; [|split; exact I].
unfold aSB, aSHB, aC, aT, aTOP, aLEN, aIM, aHW, aN, aSP, aN8, aCNT8, aQB, aJ1, aJ2, aJ3, aINST, aSO, aBP.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, DFSTACK.
(* the frame atoms: the entry sp, the instance, the stack object, the buffer *)
split. { apply (AF 2%nat sp0); [exact E2''| | | |]. all: clear - CR0 Usp S1 S2 T4 T7 Hal'; first [lia | change (2 ^ 4) with 16; exact Hal']. }
split. { apply (AF 11%nat inst); [exact E11'| | | |]. all: clear - IO1 IO2 IO3; first [lia | change (2 ^ 3) with 8; exact IO3]. }
split. { apply (AF 13%nat so); [exact E13'| | | |]. all: clear - Usp S1 S2 T4 T7 SO1 Hso2 Hso3 SR1 SR2; first [lia | change (2 ^ 3) with 8; exact Hso3]. }
split. { apply (AF 12%nat bp); [exact E12'| | | |]. all: clear - Usp S1 S2 T4 T7 BP1 Hbp2 Hbp3 BR1 BR2; first [lia | change (2 ^ 3) with 8; exact Hbp3]. }
(* the released facts *)
split. { apply (AF 10%nat pa); [exact E10'| | | |].
all: clear - CR0 P1 P2 P3 P5; first [lia | change (2 ^ 4) with 16; exact P3 | apply Z.mod_divide in P3 as [c Hc]; [|lia]; lia]. }
split. { apply (AF 32%nat T); [exact EaT'| | | |]. all: clear - CR0 hT1 hT2 TAL; first [lia | exact TAL]. }
split. { apply (AF 33%nat (ly_C ly)); [exact EaC'| | | |]. all: clear - CR0 hC1 hC2 CAL; first [lia | exact CAL]. }
split. { apply (AF 34%nat SB); [reflexivity| | | |]. all: clear - CR0 hSP1 hSP2 hP1 hP2 SAL; first [lia | exact SAL]. }
split. { apply (AF 35%nat (ly_top ly)); [exact EaTOP'| | | |]. all: clear - CR0 T1 T2 T3 T4 T7; unfold ly_bot, kStackSpan in *; first [lia | exact T3]. }
split. { apply (AF 36%nat LENv); [reflexivity| | | |]. all: clear - CR0 P8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 37%nat IMv); [reflexivity| | | |]. all: clear - CR0 P9 P10; first [lia | change (2 ^ 3) with 8; exact P10]. }
split. { apply (AF 38%nat HWv); [reflexivity| | | |]. all: clear - CR0 HBR; unfold DGgm.HWv; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat nn); [reflexivity| | | |]. all: clear - CR0 Q8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat SHADOW_OFF); [reflexivity| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
split. { apply (AF 41%nat SPv); [reflexivity| | | |]. all: unfold DGgm.SPv, SHADOW_OFF in *; clear - CR0 P1 P2 P5 P11 P12 P13 P14 Q8; first [lia | change (2 ^ 1) with 2; exact P13 | rewrite P14 in P12; pose proof (Z.div_pos (nn + 7) 8); nia]. }
split. { apply (AF 42%nat N8v); [reflexivity| | | |]. all: clear - CR0 P5 P6 P7 Q8; first [lia | change (2 ^ 3) with 8; exact P7 | apply Z.mod_divide in P7 as [c Hc]; [|lia]; lia]. }
split. { apply (AF 43%nat CNT8v); [reflexivity| | | |]. all: clear - CR0 P5 P6 P14 Q8; rewrite ?P14 in *; unfold DGgm.N8v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r | nia]. }
split. { apply (AF 50%nat QBFv); [reflexivity| | | |]. all: clear - CR0 Qa Qb Q8; unfold DGgm.QBFv, DGgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; first [destruct (need_new_batch q); lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 51%nat j1); [reflexivity| | | |]. all: clear - CR0 HJ1R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 52%nat j2); [reflexivity| | | |]. all: clear - CR0 HJ2R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split; [|exact I]. { apply (AF 53%nat j3); [reflexivity| | | |]. all: clear - CR0 HJ3R; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The machine registers at Deallocate's entry are REGS_G over E0.                                                  *)
Local Ltac reg_atom :=
cbn -[Z_to_bv getr];
repeat match goal with |- context [Z.of_nat ?k] => let y := eval cbv in (Z.of_nat k) in change (Z.of_nat k) with y end;
rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; reflexivity.
Local Ltac reg_case :=
match goal with |- _ = sv_denot ?E (sr_get ?sr ?r) => let x := eval vm_compute in (sr_get sr r) in change (sr_get sr r) with x end;
first
[ transitivity (Z_to_bv 64 0); [apply getr_zero | reflexivity]
| transitivity (getr regs0 11); [rewrite G11; exact H10 | reg_atom]
| transitivity (getr regs0 10); [rewrite G10; exact H11 | reg_atom]
| transitivity (getr regs0 13); [rewrite G13; exact H14 | reg_atom]
| transitivity (w64 0); [exact H12 | reflexivity]
| transitivity (w64 0); [exact H13 | reflexivity]
| transitivity (w64 1); [exact H15 | reflexivity]
| transitivity (w64 TFIB_TP); [exact Hr4 | reflexivity]
| match goal with |- getr _ ?r = _ =>
    rewrite <- (dregs_other regs pa inst bp so r) by (vm_compute; discriminate) end; reg_atom ].
Lemma REGS_ok : regs_ok E0 REGS_G regs.
Proof.
apply regs_ok_by_cases. intros r Hr. cbv [all_regs In] in Hr.
repeat (destruct Hr as [<-|Hr]; [reg_case|]).
destruct Hr.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed and the free_hyps record.                                                                               *)
Lemma SEED_ok : st_ok tfibsegs E0 DGgm.SS0 (restrict (w_H W) (mkst regs (w64 A_Deallocate) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold DGgm.SS0, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact REGS_ok|]. split; [|exact FACTS_ok].
split; [vm_compute; reflexivity|]. split; [exact REG0_ok | exact PAIRS_ok].
Qed.
Theorem FH_ok : DGgm.free_hyps W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs.
Proof.
pose proof vZONE as (ZP & PS & PAL & HNN). pose proof SO_range as (SR1 & SR2 & BR1 & BR2). pose proof INST_range as (IR1 & IR2).
constructor.
- exact vLY.
- exact G10.
- rewrite G4. exact Hr4.
- rewrite G1. exact Hra.
- rewrite G1. exact Hra4096.
- rewrite G2. split; [exact Hlo | split; [exact Hbot | exact Hhi]].
- rewrite G2. exact Hal.
- exact Htrlen.
- rewrite G2, G13. unfold w64. rewrite unsigned_lit_small by lia. split; [exact Hso1 | split; [exact Hso2 | exact Hso3]].
- rewrite G2, G12. unfold w64. rewrite unsigned_lit_small by lia. split; [exact Hbp1 | split; [exact Hbp2 | exact Hbp3]].
- rewrite G11. unfold w64. rewrite unsigned_lit_small by lia. exact HIO.
- exact ZP.
- exact vIMG.
- exact PAL.
- exact HNN.
- exact Hhb.
- exact Hhbm.
- exact PS.
- exact vPRES.
- intros a Ha. apply vSHPRES. exact Ha.
- pose proof QB_facts as (Qa & Qb & _). split; [exact Qa | exact Qb].
- split; [exact HJ1R | split; [exact HJ2R | exact HJ3R]].
- exact vIAL.
- exact SEED_ok.
- rewrite G12. unfold w64. rewrite unsigned_lit_small by lia. exact PBUF.
Qed.
End h.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed of the mid / drain arms from the generic precondition and the view.                                     *)
Theorem FH_m : forall U ARX rpre fpre inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> inst_ok inst -> dview B W ly inst mem S p n ->
exists hb1 j1 j2 j3,
0 <= hb1 < 256 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
DGgm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs.
Proof.
intros U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE HBLK HIO DV.
destruct PRE as (_ & _ & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & HPRES & _ & Htp & H10 & H11 & H12 & H13 & H14 & H15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & _ & _ & _).
pose proof DV as [_ _ _ (hb1 & Hhb & Hhbm & HW1 & HW2) PRES _ JUNK _ _ _].
destruct (pres_word (w_H W) mem (ly_T ly + t_stats + 24) ltac:(intros i Hi; apply JUNK; lia)) as (j1 & J1R & J1).
destruct (pres_word (w_H W) mem (ly_T ly + t_stats + 32) ltac:(intros i Hi; apply JUNK; lia)) as (j2 & J2R & J2).
destruct (pres_word (w_H W) mem (sptr_addr B ly p) ltac:(intros i Hi; apply PRES; lia)) as (j3 & J3R & J3).
exists hb1, j1, j2, j3. split; [exact Hhb|]. split; [exact HW1|].
eapply FH_ok; eassumption.
Qed.
End g.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The walk to Put's call of QuarantineCache::Enqueue (arms mid and drain).                                          *)
Ltac numc := ceil; unfold zone3, zone3cases, TFIB_IMG_LO, kLowShadowBeg, kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize,
kPrimResvSize, kNodesBlockSize, kStoreBlockSize, t_qc, t_cache, t_unwinding, t_stats, DFSTACK, TFIB_IMG_END, DEP_STK, SHADOW_OFF,
TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W, TFIB_IAL_FLAG, TFIB_TP, TFIB_TSD in *.
Lemma wvb_self_e : forall md, with_vm_backing (m_vm_lazy md) (m_vm_materialized md) md = md.
Proof. intros [fd [maps lazy mat] io fs proc lim tm]. reflexivity. Qed.
Lemma amreal_ask_depot_e {R} : forall trc s (k : Z -> itree astate R) (Wx : world tfibsegs) c Q,
SRr tfibsegs Wx c (fun W1 c1 => exists z, aok s (KDepot trc) z /\ amreal tfibsegs (k z) W1 c1 Q) ->
amreal tfibsegs (IAsk (KDepot trc) s k) Wx c Q.
Proof. intros trc s k Wx c Q H. exact H. Qed.
Lemma amreal_pure_e {A R} : forall (m : M A) (f : A -> M R) s a s' (W : world tfibsegs) c Q,
m s = IRet (a, s') -> amreal tfibsegs (f a s') W c Q -> amreal tfibsegs (bind m f s) W c Q.
Proof. intros m f s a s' W c Q E H. unfold bind. rewrite E. cbn [ibind]. exact H. Qed.
(* IAL_POST depends only on the internal allocator's zone. *)
Lemma IAL_transfer_m : forall (W : world tfibsegs) (m1 m2 : word -> option byte),
(forall a, DGgm.IZONE a -> m2 (Z_to_bv 64 a) = m1 (Z_to_bv 64 a)) -> DGgm.IAL_POST W m1 -> DGgi.IAL_POST W m2.
Proof.
intros W m1 m2 E I. unfold DGgm.IAL_POST, DGgi.IAL_POST in *. cbv zeta in *. destruct I as (I1 & I2 & I3 & I4 & I5).
assert (V : forall a (w : nat) v, (forall k, (k < w)%nat -> DGgm.IZONE (a + Z.of_nat k)) ->
val_mem tfibsegs (mrestrict (w_H W) m1) a w v -> val_mem tfibsegs (mrestrict (w_H W) m2) a w v).
{ intros a w v Hz Hv. apply (AF0x.val_mem_frame (w_H W) m1 m2 a w v); [intros k Hk; apply E, Hz, Hk | exact Hv]. }
split; [apply V; [intros k Hk; unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I1]|].
split; [apply V; [intros k Hk; unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG in *; lia | exact I2]|].
split; [apply V; [intros k Hk; unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I3]|].
split; [apply V; [intros k Hk; unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IAL_W in *; lia | exact I4]|].
intros a Ha. rewrite (mbyte_mrestrict_same (w_H W) m1 m2 a). 2:{ apply E. unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_W in *. lia. }
exact (I5 a Ha).
Qed.

(* The zones the depot and the seed's frame use, against the seed's windows (over DGgm.free_hyps). *)
Section WKm.
Variables (W : world tfibsegs) (ly : alayout).
Variables (regs0 : bvmap 5 word) (mem0 : word -> option byte) (tr : list Z).
Variables (p nn hb1 : Z) (q : qcache) (j1 j2 j3 : Z).
Variable regsU : bvmap 5 word.
Hypothesis FH : DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU.
Local Notation sp0 := (bv_unsigned (getr regs0 2)).
Local Notation WIN := (DGgm.WIN ly regs0 p).
Local Notation LYBm := (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation LYDm := (DGgm.LYD W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Local Notation DRm := (DGgm.derived_ranges W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH).
Lemma sp_facts_m : ly_stk_lo ly + DFSTACK <= sp0 /\ ly_bot ly < sp0 /\ sp0 <= ly_stk_hi ly /\ kHighMemBeg <= ly_stk_lo ly /\ ly_stk_hi ly <= kHighMemEnd.
Proof.
pose proof (DGgm.fh_Hsp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as (S1 & S2 & S3). pose proof LYBm as LB.
destruct LB as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & L1 & L2). repeat split; assumption.
Qed.
Lemma DZONE_out_m : forall a, DGgm.DZONE ly a ->
~ WIN a /\ ~ DGgm.IZONE a /\ ~ (DGgm.SPv p <= a < DGgm.SPv p + DGgm.CNT8v nn) /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - DFSTACK <= a < sp0).
Proof.
intros a Hd. pose proof LYBm as LB. pose proof DRm as DR. pose proof sp_facts_m as SPF.
pose proof LYDm as (_ & _ & (_ & _ & NBSTK) & (_ & SBSTK) & _). unfold zdisjoint in NBSTK, SBSTK. cbn [fst snd] in NBSTK, SBSTK.
unfold DGgm.DZONE in Hd. destruct Hd as [Hd|[Hd|Hd]].
- split; [apply (DGgm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); unfold TFIB_IMG_LO, TFIB_IMG_END; lia|].
  unfold DGgm.IZONE. clear - Hd DR SPF LB. numc. repeat split; lia.
- split; [apply (DGgm.notWIN_NB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); exact Hd|].
  unfold DGgm.IZONE. clear - Hd DR SPF LB NBSTK. numc. repeat split; lia.
- split; [apply (DGgm.notWIN_SB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); exact Hd|].
  unfold DGgm.IZONE. clear - Hd DR SPF LB SBSTK. numc. repeat split; lia.
Qed.
Lemma CZONE_out_m : forall a, CZONE ly a -> ~ WIN a.
Proof.
intros a Hc. pose proof LYBm as LB.
unfold CZONE in Hc. destruct Hc as [Hc|[Hc|[Hc|[Hc|[Hc|Hc]]]]].
- apply (DGgm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END. lia.
- apply (DGgm.notWIN_shb W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold kLowShadowBeg, kHighMemBeg. lia.
- apply (DGgm.notWIN_Thead W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
- apply (DGgm.notWIN_C W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
- apply (DGgm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). unfold TFIB_IMG_LO, TFIB_IMG_END, TFIB_TSD in *. lia.
- apply (DGgm.notWIN_D W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH). lia.
Qed.
Lemma IZONE_out_m : forall a, DGgm.IZONE a ->
~ WIN a /\ ~ DGgm.DZONE ly a /\ ~ (DGgm.SPv p <= a < DGgm.SPv p + DGgm.CNT8v nn) /\ 0 <= a < 2 ^ 64 /\ ~ (sp0 - 48 - DEP_STK <= a < sp0 - 48).
Proof.
intros a Hz. pose proof LYBm as LB. pose proof DRm as DR. pose proof sp_facts_m as SPF.
split; [apply (DGgm.notWIN_img W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH); unfold DGgm.IZONE, TFIB_IAL_LO, TFIB_IAL_HI, TFIB_IAL_FLAG, TFIB_IMG_LO, TFIB_IMG_END in *; lia|].
unfold DGgm.IZONE, DGgm.DZONE in *. clear - Hz DR SPF LB. numc. repeat split; lia.
Qed.
(* The memory at Put's call of Enqueue (DGgf.at_ENQ), composed with the depot's and the seed's frames. *)
Lemma dmem_m_ok : forall (DP : (word -> option byte) -> Prop) (msm mem4 mem' : word -> option byte),
DGgm.MEQI W ly regs0 mem0 p msm ->
(forall x : word, ~ (sp0 - 48 - DEP_STK <= bv_unsigned x < sp0 - 48) -> ~ DGgm.DZONE ly (bv_unsigned x) -> mem4 x = msm x) ->
(forall a, apresent (w_H W) msm a -> apresent (w_H W) mem4 a) ->
DP mem4 ->
DGgf.EQS ly regs0 p nn mem4 mem' ->
(forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W) mem' a) ->
(forall a, DGgm.WINT ly a \/ DGgm.WINB p a -> apresent (w_H W) mem' a) ->
val_mem tfibsegs (mrestrict (w_H W) mem') (p - 16) 4 (3 + 256 * hb1) ->
val_mem tfibsegs (mrestrict (w_H W) mem') (p - 12) 4 nn ->
val_mem tfibsegs (mrestrict (w_H W) mem') (ly_T ly + t_unwinding) 1 0 ->
dmem_m W ly sp0 mem0 p nn hb1 DP mem'.
Proof.
intros DP msm mem4 mem' [MQ IALm] Hfr4 Hpr4 HDP [EQ4 SH] PRS PRW V1 V2 V3.
assert (W2D : forall a, DGgm.WIN2 ly regs0 p a -> dwin_m ly sp0 p a).
{ intros a Hw. cbv beta zeta delta [DGgm.WIN2] in Hw. unfold dwin_m.
  destruct Hw as [Hw|[Hw|[Hw|Hw]]]; [left; exact Hw | exfalso; lia | right; left; exact Hw | right; right; exact Hw]. }
assert (WD : forall a, WIN a -> dwin_m ly sp0 p a).
{ intros a Hw. cbv beta zeta delta [DGgm.WIN] in Hw. unfold dwin_m. exact Hw. }
unfold dmem_m. split.
{ exists mem4. split; [exact HDP|]. split.
  - intros a Hz Hp. destruct (DZONE_out_m a Hz) as (NW & NI & NS & Ra & NST). apply Hpr4.
    apply (apresent_same (w_H W) mem0 msm a); [|exact Hp]. apply MQ; rewrite unsigned_lit_small by exact Ra; assumption.
  - intros x Hz. destruct (DZONE_out_m _ Hz) as (NW & NI & NS & Ra & NST).
    apply EQ4; [intros Hw; apply NW; apply DGgm.WIN2_WIN; exact Hw | exact NS]. }
split.
{ intros x Hw Hz Hi Hs. rewrite (EQ4 x); [| intros X; apply Hw; apply W2D; exact X | exact Hs].
  pose proof sp_facts_m as SPF.
  rewrite (Hfr4 x); [| intros X; apply Hw; left; unfold DEP_STK, DFSTACK, DGbaseC.DFSTACK in *; lia | exact Hz].
  apply MQ; [intros X; apply Hw; apply WD; exact X | exact Hi]. }
split.
{ apply (IAL_transfer_m W msm mem'); [|exact IALm]. intros a Hz. destruct (IZONE_out_m a Hz) as (NW & ND & NS & Ra & NST).
  rewrite (EQ4 (Z_to_bv 64 a)); rewrite ?unsigned_lit_small by exact Ra.
  2:{ intros X. apply NW. apply DGgm.WIN2_WIN. exact X. }
  2:{ exact NS. }
  apply Hfr4; rewrite unsigned_lit_small by exact Ra; assumption. }
split. { intros x Hs. apply SH. exact Hs. }
split; [exact PRS|]. split; [exact PRW|]. split; [exact V1|]. split; [exact V2 | exact V3].
Qed.
End WKm.

Section e.
Local Open Scope am_scope.
Variable B : asyms.
Variable U : list Z -> astate -> Prop.
Variable ft : sptr -> list Z -> M unit.
Variables (ARX ARXr : Z -> alayout -> astate -> world tfibsegs -> (word -> option byte) -> Model -> Prop).
Variable AOX : alayout -> astate -> Z -> Prop.
Variable rpre : astate -> Z -> Prop.
Variable lpost : astate -> Prop.
Variable fpre : alayout -> astate -> world tfibsegs -> (word -> option byte) -> sptr -> Z -> Prop.
Variable dpost : Z -> alayout -> astate -> world tfibsegs -> list Z -> Z -> (word -> option byte) -> Prop.
Variable dbody : astate -> M unit.
Variable L24 : Z.
Variable QB : astate -> Prop.
Variable DRq : astate -> list chunk -> list Z -> Prop.
Variable MP : (word -> option byte) -> Prop.
Hypothesis IF : DIface B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP.
Hypothesis TS : TfibSyms B.
Local Notation Fshape := (di_shape B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fview := (di_view B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdepot := (di_depot B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).
Local Notation Fdaok := (di_dpost_aok B U ft ARX ARXr AOX rpre lpost fpre dpost dbody L24 QB DRq MP IF).

(* From Deallocate's entry to Put's call of QuarantineCache::Enqueue: DGgd.segB, StackDepotPut, the model's depot
   answer and the chunk's change, DGgf.segCm1; the memory at the call is dmem_m. *)
Lemma to_enq : forall inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 (Q : unit * astate -> world tfibsegs -> config -> Prop),
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr -> In (p, n) (blocks S) ->
find_user (st_chunks S) p = Some k -> ck_state k = CAllocated ->
0 <= hb1 < 256 -> val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) ->
DGgm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs ->
(forall z (msE : machine_state) mat E5, aok (dtick S) (KDepot tr) z ->
  msE = mkst (ms_regs msE) (w64 0x36a74) (ms_mem msE) (seg_rom tfibsegs) ->
  (forall k0, (k0 < aHAVf)%nat ->
    ew E5 k0 = ew (DGgm.E0 ly (dregs regs (sptr_addr B ly p) inst bp so) tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3) k0) ->
  st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) ->
  dmem_m W ly (bv_unsigned (getr regs 2)) mem (sptr_addr B ly p) (req_size n) hb1 (dpost inst ly S W tr z) (ms_mem msE) ->
  amreal tfibsegs ((enqueue (qk k) ;; dmd dbody) (qx S k z tr)) W (mkCfg msE (with_vm_backing (m_vm_lazy md) mat md)) Q) ->
amreal tfibsegs (ft p tr S) W (cfg_at tfibsegs 0x322a4 regs mem md) Q.
Proof using IF TS.
intros inst so bp ly S W regs mem md p n tr k hb1 j1 j2 j3 Q PRE HBLK Hf Hst Hhb1 Hhdr FH HC.
destruct PRE as (HARX & HRP & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & Hpres & Hgp & Htp & Hr10 & Hr11 & Hr12 & Hr13 & Hr14 & Hr15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & Htr & Hp0 & HFP).
pose proof (dv_nonnull B W ly inst mem S p n (Fview inst ly S W mem md p n HARX HRP HFP HBLK)) as PNN.
rewrite (Fshape p n tr S k PNN HRP HBLK Hf Hst).
set (pa := sptr_addr B ly p) in *. set (nn := req_size n) in *. set (q := st_qthread S) in *.
set (regs0 := dregs regs pa inst bp so) in *.
unfold spZ, raZ in *.
assert (R2 : getr regs0 2%bv = getr regs 2%bv) by (unfold regs0; apply dregs_other; vm_compute; discriminate).
pose proof (sp_facts_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as SPF. rewrite R2 in SPF. unfold DFSTACK in SPF.
assert (Usp : 0 <= bv_unsigned (getr regs 2) < 2 ^ 64) by apply u64_range.
assert (BP0 : bv_unsigned (getr regs0 12) = bp).
{ unfold regs0. rewrite dregs_12. unfold w64. apply unsigned_lit_small. clear - SPF Usp Hbp1 Hbp2. unfold kHighMemEnd, kHighMemBeg in *. lia. }
pose proof (DGgm.LYB W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as LB.
pose proof (DGgm.derived_ranges W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as DR.
pose proof (DGgm.N8_ge W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH) as [N8a N8b].
pose proof (DGgm.fh_Hp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as ZP.
pose proof (DGgm.fh_Hp10 _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hp10.
pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn.
unfold depot_put. cbn [bind askz ibind]. apply amreal_ask_depot_e.
unfold cfg_at. rewrite <- (wvb_self_e md) at 1.
eapply SRr_bind; [exact (DGgd.segB W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs (m_vm_materialized md) FH)|].
intros W1 c1 _ (-> & msD & mat1 & E3 & -> & HshD & HEn3 & HS & MEQD & TRQ & PRESD).
rreg HS (1%bv : bv 5) Q1. rreg HS (2%bv : bv 5) Q2.
rewrite (HEn3 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr pa nn hb1 q j1 j2 j3) in Q2.
assert (SPD : bv_unsigned (getr (ms_regs msD) 2) = bv_unsigned (getr regs0 2) - 48).
{ rewrite Q2. unfold w64. rewrite unsigned_lit_small; [reflexivity|]. rewrite R2. clear - SPF Usp. numc. lia. }
rewrite HshD. eapply SRr_bind.
{ apply (Fdepot inst ly S W mem md tr (ms_regs msD) (ms_mem msD) (with_vm_backing (m_vm_lazy md) mat1 md) bp HARX Htr).
  - intros x Hx. apply (proj1 MEQD).
    + destruct Hx as [Hd|[Hc _]]; [exact (proj1 (DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd)) |
      exact (CZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hc)].
    + destruct Hx as [Hd|[_ Hi]]; [exact (proj1 (proj2 (DZONE_out_m W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH _ Hd))) | exact Hi].
  - rreg HS (10%bv : bv 5) R. rewrite R, (HEn3 12%nat ltac:(cbv; lia)), (DGgm.E12 ly regs0 tr pa nn hb1 q j1 j2 j3).
    unfold regs0. rewrite dregs_12. reflexivity.
  - rreg HS (11%bv : bv 5) R. rewrite R, (HEn3 36%nat ltac:(cbv; lia)), (DGgm.EaLEN ly regs0 tr pa nn hb1 q j1 j2 j3). reflexivity.
  - rreg HS (3%bv : bv 5) R. rewrite R, (HEn3 3%nat ltac:(cbv; lia)), (DGgm.Er ly regs0 tr pa nn hb1 q j1 j2 j3 3 3%bv eq_refl).
    unfold regs0. rewrite dregs_other by (vm_compute; discriminate). exact Hgp.
  - rreg HS (4%bv : bv 5) R. rewrite R. reflexivity.
  - rreg HS (1%bv : bv 5) R. rewrite R. apply YK0s.ret_ok_even. reflexivity.
  - intros i Hi. pose proof (TRQ i Hi) as TQ. rewrite BP0 in TQ. exact TQ.
  - exact Hbp3.
  - clear - SPF Hbp1. lia.
  - exact Hbp2.
  - right. rewrite SPD, R2. lia.
  - rewrite SPD, R2. replace (bv_unsigned (getr regs 2) - 48) with (bv_unsigned (getr regs 2) + (-3) * 16) by lia.
    rewrite Z_mod_plus_full. exact Hal.
  - rewrite SPD, R2. clear - SPF. unfold DEP_STK, YFl0C.DEP_STK in *. lia.
  - rewrite SPD, R2. lia.
  - intros a Ha. rewrite SPD in Ha. apply PRESD. unfold DEP_STK, YFl0C.DEP_STK, DFSTACK in *. lia. }
intros W2 c2 _ (-> & z & regs4 & mem4 & mat4 & -> & HP4 & Hfr4 & Hpr4 & DP4). srr_norm_model.
rewrite SPD in Hfr4.
pose proof (Fdaok _ _ _ _ _ _ _ DP4) as AOK.
rewrite Q1. eapply SRr_bind.
{ apply (DGgf.segCm1 W ly regs0 mem md tr pa nn hb1 q j1 j2 j3 regs FH msD E3 regs4 mem4 mat4).
  split; [exact HshD|]. split; [exact HEn3|]. split; [exact HS|]. split; [exact HP4|]. split; [exact Hfr4|].
  split; [exact Hpr4|]. split; [exact MEQD | exact PRESD]. }
intros W3 c3 _ (-> & msE & matE & E5 & -> & HshE & HEn5 & HS5 & EQE & PRES5).
apply SRr_ret. exists z. split; [exact AOK|].
assert (BT : bv_unsigned (ew E5 32) = ly_T ly).
{ rewrite (HEn5 32%nat ltac:(cbv; lia)), (DGgm.EaT ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64. apply unsigned_lit_small.
  destruct LB as (LB1 & LB2 & _). clear - LB1 LB2. numc. lia. }
assert (B10 : bv_unsigned (ew E5 10) = pa).
{ rewrite (HEn5 10%nat ltac:(cbv; lia)), (DGgm.E10 ly regs0 tr pa nn hb1 q j1 j2 j3), Hp10. unfold w64. apply unsigned_lit_small.
  clear - DR N8a. numc. lia. }
assert (R38 : rho_of E5 38%nat = 2 + 256 * hb1).
{ unfold rho_of. rewrite (HEn5 38%nat ltac:(cbv; lia)), (DGgm.EaHW ly regs0 tr pa nn hb1 q j1 j2 j3). unfold w64, DGgm.HWv.
  apply unsigned_lit_small. lia. }
assert (T1V : zev (rho_of E5) T1term = 3 + 256 * hb1) by (apply T1_val; [exact Hhb1 | exact R38]).
assert (OT : forall a, ly_T ly <= a < ly_T ly + kThreadObjSize -> off_img a) by (intros a Ha; exact (zone3_off_img _ _ a (proj1 LB) Ha)).
assert (OP : forall a, pa - 16 <= a < pa + 8 -> off_img a) by (intros a Ha; apply (zone3_off_img _ _ a ZP); lia).
assert (DM : dmem_m W ly (bv_unsigned (getr regs0 2)) mem pa nn hb1 (dpost inst ly S W tr z) (ms_mem msE)).
{ apply (dmem_m_ok W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs FH (dpost inst ly S W tr z) (ms_mem msD) mem4 (ms_mem msE)
    MEQD Hfr4 Hpr4 DP4 EQE PRES5).
  - intros a [[Ha|Ha]|[Ha|Ha]].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 34 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_unwinding in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_unwinding in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 35 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BT; clear - Ha; unfold t_stats in *; lia
      | apply OT; clear - Ha; unfold kThreadObjSize, t_stats in *; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 36 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
    + eapply (st_ok_window_apresent_off (w_H W) E5 _ _ 37 _ a HS5); [reflexivity
      | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite B10; clear - Ha; lia
      | apply OP; clear - Ha; lia].
  - memv HS5 36%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia | apply DGgf.denot_by_zev; [reflexivity | lia | exact T1V] | lia].
  - memv HS5 36%nat 1%nat; [cbn [base_val YP09.r_base]; rewrite B10; lia
    | cbn [sv_denot]; rewrite (HEn5 39%nat ltac:(cbv; lia)), (DGgm.EaN ly regs0 tr pa nn hb1 q j1 j2 j3); unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
    | lia].
  - memv HS5 34%nat 0%nat; [cbn [base_val YP09.r_base]; rewrite BT; unfold t_unwinding; lia | reflexivity | lia]. }
rewrite R2 in DM.
pose proof AOK as AOK0.
destruct AOK as [-> | [-> _]].
- cbn [Z.eqb ret ibind]. eapply amreal_pure_e; [reflexivity|]. exact (HC 0 msE matE E5 AOK0 HshE HEn5 HS5 DM).
- cbn [Z.eqb bind get ret ibind].
  lazymatch goal with |- context [mcheck ?b1 14] => destruct b1 end; cbn [mcheck ret ibind]; [|exact I].
  lazymatch goal with |- context [mcheck ?b2 13] => destruct b2 end; cbn [mcheck ret put ibind]; [|exact I].
  eapply amreal_pure_e; [reflexivity|]. exact (HC 1 msE matE E5 AOK0 HshE HEn5 HS5 DM).
Qed.
End e.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Put after Enqueue returns (0x36a68; the stack offsets of the released YFg2 / YFfz scripts moved by 2128: Put's sp
   is the entry sp - 80, Enqueue's scratch the QSTACK bytes below it).  The kept regions of DGfw.SS_E are Put's frame
   above Enqueue's scratch and QuarantineChunk's frame; the thread cache's byte count (T + t_qc + 24) is added so
   that Put's test of it resolves.                                                                                 *)
Definition tm_r0 : YP09.region := Eval vm_compute in nth 0 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition tm_r2 : YP09.region := Eval vm_compute in nth 2 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []).
Definition tm_r0t : YP09.region := Eval vm_compute in trim_lo tm_r0 (-80).
Definition RS_TM : smem := [tm_r0t; tm_r2].
Lemma SSE_mem_tm : ss_mem DGfw.SS_E = tm_r0 :: nth 1 (ss_mem DGfw.SS_E) (YP09.mkRegion None 0 0 0 0 []) :: tm_r2 :: skipn 3 (ss_mem DGfw.SS_E).
Proof. vm_compute. reflexivity. Qed.
Lemma RS_TM_sub : submem RS_TM (ss_mem DGfw.SS_E).
Proof.
rewrite SSE_mem_tm. unfold RS_TM.
apply submem_keep; [change tm_r0t with (trim_lo tm_r0 (-80)); apply subregion_trim_lo|].
apply submem_drop. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
Definition SS_TM : sstate := Eval vm_compute in ss_after_call DGfw.SS_E RS_TM 112 223848.
Definition R_QBT : YP09.region :=
YP09.mkRegion (Some 32%nat) (t_qc + 24) (t_qc + 32) 0 0 [YP09.mkChunk (t_qc + 24) (CVal 8 (SOff 50%nat 0))].
Lemma pres_wle : forall (W W5 : world tfibsegs) (m m' : word -> option byte) a,
wle W W5 -> m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) -> apresent (w_H W) m a -> apresent (w_H W5) m' a.
Proof.
intros W W5 m m' a HW E [Hh [b Hb]]. split.
- destruct (w_H W5 (Z_to_bv 64 a)) eqn:H5; [|reflexivity]. rewrite (HW _ H5) in Hh. discriminate.
- exists b. rewrite E. exact Hb.
Qed.
(* A region whose bytes are unchanged and present in the old world is kept in a smaller world. *)
Lemma kept_raw : forall (E : env) (W W5 : world tfibsegs) (m m' : word -> option byte) r, wle W W5 ->
(forall a, base_val E (YP09.r_base r) + YP09.r_lo r <= a < base_val E (YP09.r_base r) + YP09.r_hi r ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) /\ apresent (w_H W) m a) ->
(forall a, base_val E (YP09.r_base r) + YP09.r_wlo r <= a < base_val E (YP09.r_base r) + YP09.r_whi r ->
  m' (Z_to_bv 64 a) = m (Z_to_bv 64 a) /\ apresent (w_H W) m a /\ TFIB_IMG_END <= a < 2 ^ 64) ->
region_kept tfibsegs E (mrestrict (w_H W) m) (mrestrict (w_H W5) m') r.
Proof.
intros E W W5 m m' r HW Hext Hwin. split.
- intros a Ha. destruct (Hext a Ha) as [Eq P]. pose proof (pres_wle W W5 m m' a HW Eq P) as P5.
  destruct P as [Hh _]. destruct P5 as [Hh5 _]. unfold mbyte, mrestrict. rewrite Hh, Hh5, Eq. reflexivity.
- intros a Ha _. destruct (Hwin a Ha) as (Eq & P & Hr). apply apresent_writable; [exact Hr|]. exact (pres_wle W W5 m m' a HW Eq P).
Qed.
Ltac cs_case_t HS HEn Htp :=
lazymatch goal with |- getr _ ?kb = _ => let RR := fresh "RR" in rreg HS kb RR; rewrite RR end;
first [ rewrite HEn by (cbv; lia); first [ refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity | symmetry; refine (DGgm.Er _ _ _ _ _ _ _ _ _ _ _ _ _); reflexivity ]
| rewrite Htp; reflexivity | symmetry; rewrite Htp; reflexivity ].

(* ---------------------------------------------------------------------------------------------------------------- *)
(* Put's tail, arm drain (released YFfz.TAILD's machine part, the stack offsets moved by 2128): [to_drain] runs from
   Enqueue's return (0x36a68) through Put's test of the thread cache's byte count (taken: the cache is over its
   bound) to Put's call of Quarantine::Drain (A_Drain = 0x341cc, return pc 0x369a0), at the symbolic state SS_DC;
   [after_drain] runs from Drain's return to Put's ret.                                                            *)
Definition SS_DC : sstate := Eval vm_compute in DGfv.xrun (DGfw.xtake (DGfv.xrun (DGfv.xadd R_QBT SS_TM))).
Lemma SDC_mem : ss_mem SS_DC = R_QBT :: RS_TM.
Proof. vm_compute. reflexivity. Qed.
Lemma RS_DR_sub : submem RS_TM (ss_mem SS_DC).
Proof.
rewrite SDC_mem. apply submem_drop. unfold RS_TM.
apply submem_keep; [apply subregion_refl|]. apply submem_keep; [apply subregion_refl|]. apply submem_nil.
Qed.
Definition SS_DR : sstate := Eval vm_compute in ss_after_call SS_DC RS_TM 128 223648.
Lemma to_drain : forall (W W5 : world tfibsegs) ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU,
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
forall msE E5 regs' mem' md',
(forall k0, (k0 < aHAVf)%nat -> ew E5 k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0) ->
st_ok tfibsegs E5 DGfw.SS_E (restrict (w_H W) msE) ->
(forall a, bv_unsigned (getr regs0 2) - DFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W) (ms_mem msE) a) ->
wle W W5 ->
regs_preserved (ms_regs msE) regs' ->
(forall x : word, bv_unsigned (getr regs0 2) - DFSTACK <= bv_unsigned x < bv_unsigned (getr regs0 2) ->
  ~ (bv_unsigned (getr regs0 2) - 80 - AFew.QSTACK <= bv_unsigned x < bv_unsigned (getr regs0 2) - 80) -> mem' x = ms_mem msE x) ->
(forall a, bv_unsigned (getr regs0 2) - 80 - AFew.QSTACK <= a < bv_unsigned (getr regs0 2) - 80 -> apresent (w_H W5) mem' a) ->
val_mem tfibsegs (mrestrict (w_H W5) mem') (ly_T ly + t_qc + 24) 8 (DGgm.QBFv nn q) ->
kQuarantineCacheMax < DGgm.QBFv nn q ->
SRr tfibsegs W5 (cfg_at tfibsegs 0x36a68 regs' mem' md')
  (fun W'' c' => W'' = W5 /\ exists regsD memD matD EnD,
    c' = cfg_at tfibsegs 0x341cc regsD memD (with_vm_backing (m_vm_lazy md') matD md') /\
    (forall k0, (k0 < aHAVf)%nat -> ew EnD k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0) /\
    st_ok tfibsegs EnD SS_DC (restrict (w_H W5) (mkst regsD (w64 0x341cc) memD (seg_rom tfibsegs))) /\
    getr regsD 1 = w64 0x369a0 /\ YK0s.ret_ok (getr regsD 1) /\ 4096 <= raZ regsD /\
    spZ regsD = bv_unsigned (getr regs0 2) - 80 /\ spZ regsD mod 16 = 0 /\
    getr regsD 3 = getr regs0 3 /\ getr regsD 4 = getr regs0 4 /\
    getr regsD 10 = w64 (bv_unsigned (getr regs0 11) + o_quar) /\
    getr regsD 11 = w64 (ly_T ly + t_qc) /\ getr regsD 12 = w64 (ly_T ly + t_cache) /\
    (forall a, spZ regsD - AFeu.DSTACK <= a < spZ regsD -> apresent (w_H W5) memD a) /\
    (forall a, bv_unsigned (getr regs0 2) - DFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W5) memD a) /\
    (forall x : word, ~ (bv_unsigned (getr regs0 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs0 2)) -> memD x = mem' x) /\
    (forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) memD a <> None)).
Proof.
intros W W5 ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH msE E5 regs' mem' md' HEn5 HS PRESE HWle HP FRraw PRS RV HQBF.
pose proof Hwx_tfa as Hwx.
pose proof (DGgm.LYB W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as LB.
pose proof (sp_facts_m W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as SPF.
pose proof (DGgm.stack_ivs W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as (IT & _).
pose proof (DGgm.fh_Htp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Htp.
pose proof (DGgm.fh_Hsp_al _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hal.
pose proof (DGgm.fh_Hqb _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as [QB0 QBM].
pose proof (DGgm.fh_Hnn _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hnn.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
unfold DGgm.AL in Hal.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (QBP : 0 <= DGgm.QBFv nn q) by (unfold DGgm.QBFv; destruct (need_new_batch q); unfold kBatchBytes; lia).
assert (QBU : DGgm.QBFv nn q < 2 ^ 64) by (clear - QBM; unfold DGgm.QBMAX, kQuarantineCacheMax, kBatchBytes in *; lia).
assert (TR : 4096 <= ly_T ly /\ ly_T ly + kThreadObjSize <= ASAN_CEIL) by (destruct LB as ((T1 & T2 & _) & _); split; assumption).
assert (BV2 : bv_unsigned (ew E5 2) = sp0) by (rewrite (HEn5 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); reflexivity).
assert (EXT : forall a, sp0 - 80 <= a < sp0 ->
  mem' (Z_to_bv 64 a) = ms_mem msE (Z_to_bv 64 a) /\ apresent (w_H W) (ms_mem msE) a /\ TFIB_IMG_END <= a < 2 ^ 64).
{ intros a Ha. split; [apply FRraw; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - Ha; unfold DFSTACK; lia|].
  split; [apply PRESE; clear - Ha; unfold DFSTACK; lia | clear - Ha SPF Usp; numc; lia]. }
pose proof (st_ok_after_call tfibsegs 112 E5 DGfw.SS_E (restrict (w_H W) msE) regs' (mrestrict (w_H W5) mem') RS_TM 223848
  HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) RS_TM_sub ltac:(vm_compute; reflexivity) HP) as HS1.
cbn [ms_mem restrict] in HS1.
assert (KEPT : Forall (region_kept tfibsegs E5 (mrestrict (w_H W) (ms_mem msE)) (mrestrict (w_H W5) mem')) RS_TM).
{ unfold RS_TM. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (kept_raw E5 W W5 (ms_mem msE) mem' _ HWle); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi tm_r0t]; rewrite BV2;
    intros a Ha; [destruct (EXT a ltac:(clear - Ha; lia)) as (X1 & X2 & _); split; assumption | apply EXT; clear - Ha; lia].
  - apply (kept_raw E5 W W5 (ms_mem msE) mem' _ HWle); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi tm_r2]; rewrite BV2;
    intros a Ha; [destruct (EXT a ltac:(clear - Ha; lia)) as (X1 & X2 & _); split; assumption | apply EXT; clear - Ha; lia]. }
specialize (HS1 KEPT). clear KEPT.
change (ss_after_call DGfw.SS_E RS_TM 112 223848) with SS_TM in HS1.
set (En6 := havoc E5 112 (map (getr regs') CLOB)) in HS1.
assert (HEn6 : forall k0, (k0 < aHAVf)%nat -> ew En6 k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0)
  by (intros k0 Hk0; subst En6; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEn5; exact Hk0).
assert (BW2 : bv_unsigned (ew En6 2) = sp0) by (rewrite (HEn6 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); reflexivity).
assert (BW32 : bv_unsigned (ew En6 32) = ly_T ly).
{ rewrite (HEn6 32%nat ltac:(cbv; lia)), (DGgm.EaT ly regs0 tr p nn hb1 q j1 j2 j3). unfold w64. apply unsigned_lit_small.
  clear - TR. ceil. unfold ASAN_CEIL, kThreadObjSize in *. lia. }
apply (st_ok_add_region _ _ _ R_QBT) in HS1;
[ | reflexivity
| unfold R_QBT, YP09.region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val ms_mem];
  rewrite BW32;
  split; [clear - TR; unfold t_qc; lia|];
  split; [clear - TR; ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc in *; lia|];
  split; [intros o Ho; lia|];
  apply Forall_cons; [|apply Forall_nil];
  eapply (chunk_ok_val tfibsegs En6 _ _ _ 8 (SOff 50%nat 0) (DGgm.QBFv nn q));
  [ cbn [sv_denot]; rewrite (HEn6 50%nat ltac:(cbv; lia)), (DGgm.EaQBF ly regs0 tr p nn hb1 q j1 j2 j3);
    unfold w64; rewrite Zbv_add_unsigned; f_equal; lia
  | change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); clear - QBP QBU; lia
  | cbn; lia
  | change (N.to_nat 8) with 8%nat; eapply val_mem_addr; [exact RV | unfold t_qc; lia] ]
| unfold R_QBT; cbn [all_disjoint ss_mem SS_TM]; unfold extent_disjoint;
  cbn [YP09.r_base YP09.r_lo YP09.r_hi base_val];
  rewrite BW2, BW32;
  clear - TR SPF IT Usp; ceil; unfold ASAN_CEIL, kThreadObjSize, t_qc, DFSTACK, kHighMemBeg, kHighMemEnd in *;
  repeat split; lia ].
cbn [ss_pc ss_regs ss_mem ss_resv ss_facts] in HS1.
rewrite <- (restrict_mkst_fx (w_H W5)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at at 1. rewrite <- (wvb_self_e md') at 1. change (w64 0x36a68) with (Z_to_bv 64 223848).
srr_run_sh tfibtbl_rtF_ok HS.
rename HF into HF0. clear HFr.
srr_branch_sh tfibtbl_rtF_ok HS.
2:{ exfalso. match goal with H : branch_taken _ _ _ = false |- _ => rewrite branch_ltu_U in H; apply Z.ltb_ge in H; revert H end.
  rewrite !U_zev by reflexivity. cbn [zev zalu_raw]. unfold rho_of.
  rewrite (HEn6 50%nat ltac:(cbv; lia)), (DGgm.EaQBF ly regs0 tr p nn hb1 q j1 j2 j3), Z.add_0_r.
  unfold w64. rewrite unsigned_lit_small by (clear - QBP QBU; lia).
  rewrite !zcanon_id by (clear - QBP QBU; unfold kQuarantineCacheMax, M64 in *; lia).
  clear - HQBF. unfold kQuarantineCacheMax in *. lia. }
unfold YP06.add_cond in HS; cbn [ss_pc ss_regs ss_mem ss_resv ss_facts f_atoms f_conds f_alias] in HS.
srr_run_sh tfibtbl_rtF_ok HS. rename HF into HF1. clear HFr.
lazymatch type of HS with st_ok _ _ _ (restrict _ ?msx) => rename msx into msC end.
lazymatch goal with |- SRr _ _ (mkCfg _ (with_vm_backing _ ?mx _)) _ => rename mx into matC end.
pose proof (st_ok_restrict_mkst tfibsegs (w_H W5) En6 _ _ HS eq_refl) as HshC; cbn [ss_pc] in HshC.
assert (FR1 : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msC x = mem' x).
{ intros x Hx. rewrite (HF1 x); [apply (HF0 x)|].
  all: intros Hw; destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg);
  lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end;
  cbn [In] in Hin;
  repeat (destruct Hin as [Hin|Hin];
  [ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg;
    rewrite ?BW2, ?BW32 in Hrg; clear - Hx Hrg; lia |]);
  destruct Hin. }
clear HF1 HF0.
assert (PRES' : forall a, sp0 - DFSTACK <= a < sp0 - 80 -> apresent (w_H W5) mem' a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80 - AFew.QSTACK)) as [L|L]; [|apply PRS; clear - L Ha; lia].
  apply (pres_wle W W5 (ms_mem msE) mem' a HWle); [|apply PRESE; clear - Ha; lia].
  apply FRraw; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - L Ha; lia. }
assert (PRESC : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W5) (ms_mem msC) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
  - apply (apresent_same (w_H W5) mem');
    [ apply FR1; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - L1; lia
    | apply PRES'; clear - Ha L1; lia ].
  - eapply (st_ok_window_apresent (w_H W5) En6 _ _ 1 _ a HS);
    [ reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BW2; clear - L1 L2; lia
    | clear - Ha SPF Usp; numc; lia ].
  - eapply (st_ok_window_apresent (w_H W5) En6 _ _ 2 _ a HS);
    [ reflexivity | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite BW2; clear - L2 Ha; lia
    | clear - Ha SPF Usp; numc; lia ]. }
assert (VISC : forall a, aview tfibsegs (w_H W5) mem' a <> None -> aview tfibsegs (w_H W5) (ms_mem msC) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W5 x) eqn:Hx; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msC x); discriminate|].
  destruct (ms_mem msC x) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem' x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  destruct (Z_lt_le_dec a' (sp0 - 80)) as [C1|C1]; [|destruct (Z_lt_le_dec a' sp0) as [C2|C2]].
  - rewrite (FR1 x ltac:(clear - C1; lia)) in E'. congruence.
  - destruct (PRESC a' ltac:(clear - C1 C2; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
  - rewrite (FR1 x ltac:(clear - C2; lia)) in E'. congruence. }
rreg HS (1%bv : bv 5) C1. rreg HS (2%bv : bv 5) C2. rreg HS (3%bv : bv 5) C3. rreg HS (4%bv : bv 5) C4.
rreg HS (10%bv : bv 5) C10. rreg HS (11%bv : bv 5) C11. rreg HS (12%bv : bv 5) C12.
assert (SPD : spZ (ms_regs msC) = sp0 - 80).
{ unfold spZ. rewrite C2, BW2. rewrite unsigned_lit_small by (clear - SPF Usp; numc; lia). lia. }
pose proof HS as HSc. rewrite HshC in HSc.
apply SRr_ret. split; [reflexivity|].
exists (ms_regs msC), (ms_mem msC), matC, En6.
split. { rewrite HshC at 1. reflexivity. }
split; [exact HEn6|]. split; [exact HSc|].
split; [exact C1|].
split; [rewrite C1; apply YK0s.ret_ok_even; reflexivity|].
split; [unfold raZ; rewrite C1; rewrite unsigned_lit_small by lia; lia|].
split; [exact SPD|].
split; [rewrite SPD; replace (sp0 - 80) with (sp0 + (-5) * 16) by lia; rewrite Z_mod_plus_full; exact Hal|].
split; [rewrite C3, (HEn6 3%nat ltac:(cbv; lia)); exact (DGgm.Er ly regs0 tr p nn hb1 q j1 j2 j3 3 3%bv eq_refl)|].
split; [rewrite C4, Htp; reflexivity|].
split; [rewrite C10, (HEn6 11%nat ltac:(cbv; lia)), (DGgm.E11 ly regs0 tr p nn hb1 q j1 j2 j3); reflexivity|].
split; [rewrite C11, BW32; reflexivity|].
split; [rewrite C12, BW32; reflexivity|].
split; [rewrite SPD; intros a Ha; apply PRESC; clear - Ha; unfold AFeu.DSTACK, DFSTACK in *; lia|].
split; [exact PRESC|]. split; [exact FR1 | exact VISC].
Qed.

Lemma after_drain : forall (W W5 W6 : world tfibsegs) ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU,
DGgm.free_hyps W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU ->
forall EnD regsD memD regs6 mem6 md6,
(forall k0, (k0 < aHAVf)%nat -> ew EnD k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0) ->
st_ok tfibsegs EnD SS_DC (restrict (w_H W5) (mkst regsD (w64 0x341cc) memD (seg_rom tfibsegs))) ->
(forall a, bv_unsigned (getr regs0 2) - DFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W5) memD a) ->
wle W5 W6 ->
regs_preserved regsD regs6 ->
(forall x : word, bv_unsigned (getr regs0 2) - DFSTACK <= bv_unsigned x < bv_unsigned (getr regs0 2) ->
  ~ (bv_unsigned (getr regs0 2) - 80 - AFeu.DSTACK <= bv_unsigned x < bv_unsigned (getr regs0 2) - 80) -> mem6 x = memD x) ->
(forall a, bv_unsigned (getr regs0 2) - 80 - AFeu.DSTACK <= a < bv_unsigned (getr regs0 2) - 80 -> apresent (w_H W6) mem6 a) ->
SRr tfibsegs W6 (cfg_at tfibsegs 0x369a0 regs6 mem6 md6)
  (fun W'' c' => W'' = W6 /\ exists regs'' mem'' mat'',
    c' = mkCfg (mkst regs'' (getr regs0 1) mem'' (seg_rom tfibsegs)) (with_vm_backing (m_vm_lazy md6) mat'' md6) /\
    (forall r : bv 5, In r CALLEE_SAVED -> getr regs'' r = getr regs0 r) /\
    (forall x : word, ~ (bv_unsigned (getr regs0 2) - 80 <= bv_unsigned x < bv_unsigned (getr regs0 2)) -> mem'' x = mem6 x) /\
    (forall a, bv_unsigned (getr regs0 2) - DFSTACK <= a < bv_unsigned (getr regs0 2) -> apresent (w_H W6) mem'' a) /\
    (forall a, aview tfibsegs (w_H W6) mem6 a <> None -> aview tfibsegs (w_H W6) mem'' a <> None)).
Proof.
intros W W5 W6 ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH EnD regsD memD regs6 mem6 md6 HEnD HS PRESD HWle HP6 FR6 PRS6.
pose proof Hwx_tfa as Hwx.
pose proof (sp_facts_m W ly regs0 mem0 tr p nn hb1 q j1 j2 j3 regsU FH) as SPF.
pose proof (DGgm.fh_Hra _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Hra.
pose proof (DGgm.fh_Htp _ _ _ _ _ _ _ _ _ _ _ _ _ FH) as Htp.
set (sp0 := bv_unsigned (getr regs0 2)) in *.
assert (Usp : 0 <= sp0 < 2 ^ 64) by (unfold sp0; apply u64_range).
assert (BD2 : bv_unsigned (ew EnD 2) = sp0) by (rewrite (HEnD 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); reflexivity).
assert (EXT : forall a, sp0 - 80 <= a < sp0 ->
  mem6 (Z_to_bv 64 a) = memD (Z_to_bv 64 a) /\ apresent (w_H W5) memD a /\ TFIB_IMG_END <= a < 2 ^ 64).
{ intros a Ha. split; [apply FR6; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - Ha; unfold DFSTACK; lia|].
  split; [apply PRESD; clear - Ha; unfold DFSTACK; lia | clear - Ha SPF Usp; numc; lia]. }
pose proof (st_ok_after_call tfibsegs 128 EnD SS_DC (restrict (w_H W5) (mkst regsD (w64 0x341cc) memD (seg_rom tfibsegs))) regs6
  (mrestrict (w_H W6) mem6) RS_TM 223648
  HS eq_refl ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
  ltac:(vm_compute; reflexivity) RS_DR_sub ltac:(vm_compute; reflexivity) HP6) as HS1.
assert (KEPT : Forall (region_kept tfibsegs EnD (mrestrict (w_H W5) memD) (mrestrict (w_H W6) mem6)) RS_TM).
{ unfold RS_TM. apply Forall_cons; [|apply Forall_cons; [|apply Forall_nil]].
  - apply (kept_raw EnD W5 W6 memD mem6 _ HWle); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi tm_r0t]; rewrite BD2;
    intros a Ha; [destruct (EXT a ltac:(clear - Ha; lia)) as (X1 & X2 & _); split; assumption | apply EXT; clear - Ha; lia].
  - apply (kept_raw EnD W5 W6 memD mem6 _ HWle); cbn [base_val YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi tm_r2]; rewrite BD2;
    intros a Ha; [destruct (EXT a ltac:(clear - Ha; lia)) as (X1 & X2 & _); split; assumption | apply EXT; clear - Ha; lia]. }
specialize (HS1 KEPT). clear KEPT.
change (ss_after_call SS_DC RS_TM 128 223648) with SS_DR in HS1.
set (En7 := havoc EnD 128 (map (getr regs6) CLOB)) in HS1.
assert (HEn7 : forall k0, (k0 < aHAVf)%nat -> ew En7 k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0)
  by (intros k0 Hk0; subst En7; unfold aHAVf in Hk0; rewrite ew_havoc_old by lia; apply HEnD; exact Hk0).
assert (BW7 : bv_unsigned (ew En7 2) = sp0) by (rewrite (HEn7 2%nat ltac:(cbv; lia)), (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); reflexivity).
rewrite <- (restrict_mkst_fx (w_H W6)) in HS1. clear HS. rename HS1 into HS.
unfold cfg_at. rewrite <- (wvb_self_e md6) at 1. change (w64 0x369a0) with (Z_to_bv 64 223648).
srr_run_sh tfibtbl_rtF_ok HS.
lazymatch type of HS with st_ok _ ?E _ (restrict _ ?msx) => set (En8 := E) in HS; rename msx into msR end.
assert (HEn8 : forall k0, (k0 < aHAVf)%nat -> ew En8 k0 = ew (DGgm.E0 ly regs0 tr p nn hb1 q j1 j2 j3) k0)
  by (intros k0 Hk0; subst En8; unfold aHAVf in Hk0; rewrite ?ew_havoc_old by lia; apply HEn7; exact Hk0).
assert (FRT : forall x : word, ~ (sp0 - 80 <= bv_unsigned x < sp0) -> ms_mem msR x = mem6 x).
{ intros x Hx. apply HF. intros Hw. destruct (in_wrange_windows _ _ _ Hw) as (b & lo & hi & Hin & Hrg).
  lazymatch type of Hin with In _ (windows ?rs) => let ws := eval vm_compute in (windows rs) in change (windows rs) with ws in Hin end.
  cbn [In] in Hin.
  repeat (destruct Hin as [Hin|Hin];
  [ injection Hin as <- <- <-; cbn [fst snd base_val] in Hrg; rewrite ?BW7 in Hrg; clear - Hx Hrg; lia |]).
  destruct Hin. }
assert (PRES6 : forall a, sp0 - DFSTACK <= a < sp0 - 80 -> apresent (w_H W6) mem6 a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80 - AFeu.DSTACK)) as [L|L]; [|apply PRS6; clear - L Ha; lia].
  apply (pres_wle W5 W6 memD mem6 a HWle); [|apply PRESD; clear - Ha; lia].
  apply FR6; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - L Ha; lia. }
assert (PRESR : forall a, sp0 - DFSTACK <= a < sp0 -> apresent (w_H W6) (ms_mem msR) a).
{ intros a Ha. destruct (Z_lt_le_dec a (sp0 - 80)) as [L1|L1]; [|destruct (Z_lt_le_dec a (sp0 - 48)) as [L2|L2]].
  - apply (apresent_same (w_H W6) mem6);
    [ apply FRT; rewrite unsigned_lit_small by (clear - Ha SPF Usp; numc; lia); clear - L1; lia
    | apply PRES6; clear - Ha L1; lia ].
  - eapply (st_ok_window_apresent (w_H W6) En8 _ _ 0 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)),
      (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); fold sp0; clear - L1 L2; lia
    | clear - Ha SPF Usp; numc; lia ].
  - eapply (st_ok_window_apresent (w_H W6) En8 _ _ 1 _ a HS);
    [ reflexivity
    | cbn [base_val YP09.r_base YP09.r_wlo YP09.r_whi]; rewrite (HEn8 2%nat ltac:(cbv; lia)),
      (DGgm.E2 ly regs0 tr p nn hb1 q j1 j2 j3); fold sp0; clear - L2 Ha; lia
    | clear - Ha SPF Usp; numc; lia ]. }
assert (VIS : forall a, aview tfibsegs (w_H W6) mem6 a <> None -> aview tfibsegs (w_H W6) (ms_mem msR) a <> None).
{ intros a Hv HN. unfold aview, mbyte, mrestrict in Hv, HN. set (x := Z_to_bv 64 a) in *.
  destruct (w_H W6 x) eqn:Hx; [exact (Hv HN)|].
  destruct (seg_rom tfibsegs x) eqn:ROM; [destruct (ms_mem msR x); discriminate|].
  destruct (ms_mem msR x) as [|] eqn:E'; [discriminate|]. clear HN.
  destruct (mem6 x) as [b0|] eqn:EE0; [clear Hv | exact (Hv eq_refl)].
  set (a' := bv_unsigned x). assert (Ha' : 0 <= a' < 2 ^ 64) by (subst a'; apply u64_range).
  assert (Ex : Z_to_bv 64 a' = x) by (subst a'; apply Z_to_bv_bv_unsigned).
  destruct (Z_lt_le_dec a' (sp0 - 80)) as [C1|C1]; [|destruct (Z_lt_le_dec a' sp0) as [C2|C2]].
  - rewrite (FRT x ltac:(clear - C1; lia)) in E'. congruence.
  - destruct (PRESR a' ltac:(clear - C1 C2; unfold DFSTACK; lia)) as [_ [bb Hb]]. rewrite Ex in Hb. congruence.
  - rewrite (FRT x ltac:(clear - C2; lia)) in E'. congruence. }
eapply (SRr_ret_at tfibsegs tfibtbl_rtF tfibtbl_rtF_ok Hwx W6 En8); [exact HS | reflexivity | vm_compute; reflexivity |].
intros mat'.
rreg HS (1%bv : bv 5) Q1f.
rewrite (HEn8 1%nat ltac:(cbv; lia)), (DGgm.E1 ly regs0 tr p nn hb1 q j1 j2 j3) in Q1f.
split; [reflexivity|]. rewrite ?wvb_collapse. exists (ms_regs msR), (ms_mem msR), mat'.
split.
{ rewrite Q1f. unfold YK0s.ret_ok in Hra. rewrite Hra. reflexivity. }
split.
{ intros r Hr. cbv [CALLEE_SAVED In] in Hr.
  repeat (destruct Hr as [<-|Hr]; [cs_case_t HS HEn8 Htp|]). destruct Hr. }
split; [exact FRT|]. split; [exact PRESR | exact VIS].
Qed.
End f.
About FH_m.
About to_enq.
About to_drain.
About after_drain.
