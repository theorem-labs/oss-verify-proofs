(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10-31: from proofs/plugin-hostd/fuzz_reply/lib/B/DGbig1.v (commit 4d286b2e618d, file sha256 cc1c3474eb42) onto omx-clap-core/fuzz_preset's ASan+UBSan image B' (fuzz_preset.asan-ubsan, pin d663f82d7f48, twin c90d4fa54d43); module paths changed; reply's image-instance names mapped to preset's B' instance (AGif2reply / AImg_reply -> AGif2cgif / AImg_cgif) and its row names to preset's (Reply* -> Preset*, *reply -> *preset); its 9 image numerals moved by symbol from fuzz_reply.asan-ubsan (pin 10ffb5f9202a) to B' (port_addr_check 3d2eee813cce predictions; object addresses written in decimal, jump-table offsets and list indices by the same stage map), 0 list indices re-picked, and 2 addresses named in comments; facts preset already states are cited, not restated; comment references to people and refs dropped; no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: from proofs/cgif/cgif_file_fuzzer/lib/DGbig1.v (commit 8b4ae5e9984e, the Deallocate big arm, closed at cgif; file sha256 05ddf3cad77d) onto plugin-hostd/fuzz_reply's asan image (unstripped fuzz_reply.asan, sha256 d751b179ea49; pin 42c58610e125); module paths changed; its 9 image addresses moved by code-verified function pairs (4 port_addr_check e55e1b52a8a0 MAPS predictions, each code one re-derived by the internal file funcpair.py; 0 code pcs the tool read as sizes, by the internal file funcpair.py); 1 data addresses the tool read as sizes, by the same value MAPS prediction; 6 hand maps (the internal file resolve-all.tsv, each with its evidence: pinned image bytes, YImgTop, the unit AF twin); no other numeral changed. *)
(* Modified by Theorem Labs, 2026-10: then from plugin-hostd/fuzz_reply lib/A (commit 29bcc0b4b8f) to image B (fuzz_reply.asan-ubsan, pin 10ffb5f9202a, unstripped twin 3389287e1d61) by alreloc 56664a20986eb62e, same unit A -> B. *)
(* Theorem Labs, 2026-10 (the Deallocate big-block arm): DGg1.v copied through section g (sections f, g, h), the seed
   of the walk of a block above the quarantine's max_size (DGbigm.free_hyps, kQuarantineMax < nn), from the generic
   precondition DeallocG.dealloc_pre and the big view DGbigIF.dview_big.

   The actual registers at Deallocate's entry are [regs]; the walk's environment is DGbigm.E0 over the virtual register
   file [dregs regs pa inst bp so] (x10 = the block address, x11 = this, x12 = the trace buffer, x13 = the stack object).
   The region-by-region scripts are DGg1's (REG0_ok, PAIRS_ok, FACTS_ok, SEED_ok, FH_ok, FH_m). What differs from DGg1:
   - the view is dview_big: vZONE states the big range (kQuarantineMax < nn /\ nn + 15 <= 2 ^ 30); there is no shadow
     presence (DGg1's vSHPRES: only the enqueue side poisons the block's shadow, and free_hyps has no fh_Hsh_pres);
   - REG0_ok proves the tail's absolute cell TFIB_INST + 0x20 = SB (atom aSB) from the image constant cell
     `c8 (AInst o_space) (ASp 0)` (cgif YF0m.v) through cell_sym (SB_cell);
   - PAIRS_ok: that cell lies in the range inst_ok allows for the instance object. INST_NE shows that the instance's
     quarantine words (inst + 0x318 = 0x10000000, inst + 0x328 = 0x100000) are not at it, because SB >= kHighMemBeg;
   - FACTS_ok: the atoms aN / aN8 / aCNT8 range over the big blocks, and atom aQB is the thread cache's byte count
     qc_bytes q (dview_big's dvb_qb).
   DGg1's walk to Put's call of QuarantineCache::Enqueue (to_enq) is not copied: the big arm does not take it.
   Nothing here is a function's proof (rule 24). *)
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
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1v YB1q YB1t YF0l YF0m YF0x YFl0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YO0a.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import YB1w YE3d YFeq.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif0cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DeallocG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGbase DGbigm. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import DGif0.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import AGif2cgif. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require Import ImgBaseDG. From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.AU Require Import DGif0cgif.
From OSSVerify.Proofs.omx_clap_core.fuzz_preset.lib.Reusable Require DGbigIF.
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
(* Eight bytes in memory hold at most one value in [0, 2 ^ 64). *)
Lemma val_mem8_det : forall (m : word -> option byte) a v v', val_mem tfibsegs m a 8 v -> val_mem tfibsegs m a 8 v' ->
0 <= v < 2 ^ 64 -> 0 <= v' < 2 ^ 64 -> v = v'.
Proof.
intros m a v v' H H' R R'.
assert (E : forall k, (k < 8)%nat -> Z.shiftr v (8 * Z.of_nat k) mod 256 = Z.shiftr v' (8 * Z.of_nat k) mod 256).
{ intros k Hk. pose proof (H k Hk) as Bk. rewrite (H' k Hk) in Bk.
rewrite (YI04.le_byte_small v 8 k R Hk), (YI04.le_byte_small v' 8 k R' Hk) in Bk.
apply (f_equal (option_map (@bv_unsigned 8))) in Bk. cbn [option_map] in Bk. rewrite !Z_to_bv_unsigned in Bk.
unfold bv_wrap in Bk. change (bv_modulus 8) with 256 in Bk. injection Bk as Bk. symmetry. exact Bk. }
apply Z.bits_inj'. intros i Hi.
destruct (Z_lt_le_dec i 64) as [Hl|Hl].
- assert (Hk : (Z.to_nat (i / 8) < 8)%nat) by lia.
  pose proof (E _ Hk) as Ek. rewrite Z2Nat.id in Ek by (apply Z.div_pos; lia).
  apply (f_equal (fun z => Z.testbit z (i mod 8))) in Ek. cbv beta in Ek.
  pose proof (Z.mod_pos_bound i 8 ltac:(lia)) as Hm.
  change 256 with (2 ^ 8) in Ek. rewrite !Z.mod_pow2_bits_low in Ek by lia.
  rewrite !Z.shiftr_spec in Ek by lia.
  replace (i mod 8 + 8 * (i / 8)) with i in Ek by (pose proof (Z.div_mod i 8 ltac:(lia)); lia).
  exact Ek.
- rewrite <- (Z.mod_small v (2 ^ 64) R), <- (Z.mod_small v' (2 ^ 64) R').
  rewrite !Z.mod_pow2_bits_high by lia. reflexivity.
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
Local Notation E0 := (DGbigm.E0 ly regs0 tr pa nn hb1 q j1 j2 j3).
Local Notation LENv := (DGbigm.LENv tr).
Local Notation IMv := (DGbigm.IMv pa).
Local Notation HWv := (DGbigm.HWv hb1).
Local Notation SPv := (DGbigm.SPv pa).
Local Notation N8v := (DGbigm.N8v nn).
Local Notation CNT8v := (DGbigm.CNT8v nn).
Local Notation QBv := (DGbigm.QBv q).
(* The big view and the instance. *)
Hypothesis DV : DGbigIF.dview_big B W ly inst mem S p n.
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
(* The chunk header's second byte (dview_big's dvb_hdr) and the words at T + t_stats + 24 / + 32 and at the block. *)
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
(* dview_big's fields: dvb_n, dvb_nonnull, dvb_chunk, dvb_hdr, dvb_pres, dvb_junk, dvb_zone, dvb_qb. *)
Lemma vN : dview_n B W ly inst mem. Proof. destruct DV as [X _ _ _ _ _ _ _]. exact X. Qed.
Lemma vLY : layout_ok ly. Proof. destruct vN as [X _ _ _ _ _ _]. exact X. Qed.
Lemma vIMG : img_cover ly. Proof. destruct vN as [_ X _ _ _ _ _]. exact X. Qed.
Lemma vTSD : ly_tsd ly = TFIB_TSD. Proof. destruct vN as [_ _ X _ _ _ _]. exact X. Qed.
Lemma vCONST : Forall (cell_holds B ly (aview tfibsegs (w_H W) mem)) (as_const B ly). Proof. destruct vN as [_ _ _ X _ _ _]. exact X. Qed.
Lemma vINST : val_mem tfibsegs m0 (inst + 0x318) 8 0x10000000 /\ val_mem tfibsegs m0 (inst + 0x328) 8 0x100000.
Proof. destruct vN as [_ _ _ _ X _ _]. exact X. Qed.
Lemma vIAL : DGbigm.IAL_POST W mem. Proof. destruct vN as [_ _ _ _ _ X _]. exact X. Qed.
Lemma vUNW : val_mem tfibsegs m0 (T + t_unwinding) 1 0. Proof. destruct vN as [_ _ _ _ _ _ X]. exact X. Qed.
Lemma vPRES : forall a, pa - 16 <= a < pa + 8 -> apresent (w_H W) mem a. Proof. destruct DV as [_ _ _ _ X _ _ _]. exact X. Qed.
Lemma vZONE : zone3 (pa - 16) (N8v + 16) /\ DGbigm.PSTATIC ly pa nn /\ pa mod 16 = 0 /\ kQuarantineMax < nn /\ nn + 15 <= 2 ^ 30.
Proof. destruct DV as [_ _ _ _ _ _ X _]. exact X. Qed.
Lemma vQB : 0 <= qc_bytes q <= kQuarantineCacheMax. Proof. destruct DV as [_ _ _ _ _ _ _ X]. exact X. Qed.
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
Lemma E2' : ew E0 2 = getr regs 2. Proof. rewrite <- G2. apply DGbigm.E2. Qed.
Lemma E10' : ew E0 10 = w64 pa. Proof. rewrite <- G10. apply DGbigm.E10. Qed.
Lemma E11' : ew E0 11 = w64 inst. Proof. rewrite <- G11. apply DGbigm.E11. Qed.
Lemma E12' : ew E0 12 = w64 bp. Proof. rewrite <- G12. apply DGbigm.E12. Qed.
Lemma E13' : ew E0 13 = w64 so. Proof. rewrite <- G13. apply DGbigm.E13. Qed.
Lemma EaT' : ew E0 32 = w64 T. Proof. reflexivity. Qed.
Lemma EaC' : ew E0 33 = w64 (ly_C ly). Proof. reflexivity. Qed.
Lemma EaTOP' : ew E0 35 = w64 (ly_top ly). Proof. reflexivity. Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The layout (DGbigm.LYB / LYD over the view) and the block.                                                       *)
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
pose proof vZONE as (_ & _ & _ & HNN). unfold kQuarantineMax in HNN. unfold DGbigm.N8v.
pose proof (Z.div_mod (nn + 7) 8 ltac:(lia)). pose proof (Z.mod_pos_bound (nn + 7) 8 ltac:(lia)). lia.
Qed.
(* The block [pa - 16, pa + N8v) avoids the stack, the thread object and the context object (dview_big's PSTATIC). *)
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
1 <= LENv <= 30 /\ 0 <= IMv - 0xac900 <= 8 * 0x7fff /\ IMv mod 8 = 0 /\ SHADOW_OFF + 514 <= SPv /\ SPv + CNT8v <= kHighMemBeg /\ SPv mod 2 = 0 /\
CNT8v = (nn + 7) / 8.
Proof.
pose proof vZONE as (ZP & _ & P16 & HNN). destruct ZP as (Z1 & Z2 & _).
pose proof N8_ge as [N8a N8b].
pose proof P16 as P16'. apply Z.mod_divide in P16' as [c Hc]; [|lia].
assert (P8 : pa mod 8 = 0) by (rewrite Hc; replace (c * 16) with ((2 * c) * 8) by lia; apply Z_mod_mult).
assert (D8 : pa / 8 = 2 * c) by (rewrite Hc; replace (c * 16) with ((2 * c) * 8) by lia; apply Z_div_mult; lia).
assert (DN : N8v / 8 = (nn + 7) / 8) by (unfold DGbigm.N8v; apply Z_div_mult; lia).
assert (N88 : N8v mod 8 = 0) by (unfold DGbigm.N8v; apply Z_mod_mult).
assert (D32 : 0 <= pa / 2 ^ 32 <= 32767).
{ change (2 ^ 32) with 4294967296. split; [apply Z.div_pos; lia|].
pose proof (Z.div_le_mono pa 140737479966720 4294967296 ltac:(lia) ltac:(clear - Z2 N8a; ceil; unfold ASAN_CEIL in *; lia)) as X.
change (140737479966720 / 4294967296) with 32767 in X. exact X. }
assert (IM8 : (0xac900 + 8 * (pa / 2 ^ 32)) mod 8 = 0) by (apply Z.mod_divide; [lia|]; exists (88352 + pa / 2 ^ 32); lia).
assert (SP2 : (SHADOW_OFF + pa / 8) mod 2 = 0) by (rewrite D8; unfold SHADOW_OFF; apply Z.mod_divide; [lia|]; exists (1073725440 + c); lia).
assert (SPU : SHADOW_OFF + pa / 8 + N8v / 8 <= kHighMemBeg).
{ rewrite D8, DN. unfold DGbigm.N8v in Z2. clear - Z2 Hc. ceil. unfold ASAN_CEIL, SHADOW_OFF, kHighMemBeg in *. lia. }
unfold DGbigm.LENv, DGbigm.IMv, DGbigm.SPv, DGbigm.CNT8v.
pose proof Htrlen as TL.
repeat split; first [assumption | lia].
Qed.
(* The thread cache's byte count (atom aQB, dvb_qb) and the big range of the block's size (dvb_zone). *)
Lemma QB_facts : 0 <= QBv <= kQuarantineCacheMax /\ (2 ^ 28 < nn /\ nn + 15 <= 2 ^ 30).
Proof.
pose proof vZONE as (_ & _ & _ & HNN). unfold kQuarantineMax in HNN.
split; [exact vQB | lia].
Qed.
Lemma SO_range : 0 <= so /\ so + 16 < 2 ^ 64 /\ 0 <= bp /\ bp + 8 * 30 < 2 ^ 64.
Proof.
pose proof (lo_top ly vLY) as (_ & _ & _ & T4 & _). pose proof (u64_range (getr regs 2)).
unfold spZ in Hso1, Hbp1. unfold kHighMemEnd in T4. lia.
Qed.
Lemma INST_range : 0 <= inst /\ inst + 0xe60 < 2 ^ 64.
Proof. destruct HIO as (I1 & I2 & _). lia. Qed.
(* The instance's primary-space base, the tail's absolute cell TFIB_INST + 0x20 (the image constant cell
   `c8 (AInst o_space) (ASp 0)`). *)
Lemma SB_cell : val_mem tfibsegs m0 (TFIB_INST + 0x20) 8 SB.
Proof.
replace (TFIB_INST + 0x20) with (aeval B ly (AInst o_space)) by (cbn; rewrite (ts_inst B TS); reflexivity).
replace SB with (aeval B ly (ASp 0)) by (cbn; lia). apply cell_sym. vm_compute. reflexivity.
Qed.
(* inst_ok lets the instance's quarantine words inst + 0x318 / + 0x328 fall on that cell (inst = 0xa7da0 / 0xa7d90).
   They hold 0x10000000 / 0x100000 (vINST), and the cell holds SB >= kHighMemBeg: so the instance is elsewhere. *)
Lemma INST_NE : inst <> 0xa7da0 /\ inst <> 0xa7d90.
Proof.
pose proof SB_cell as C. pose proof vINST as (I1 & I2).
pose proof LYB as (_ & _ & hP1 & hSP1 & hSP2 & hP2 & _).
ceil; unfold kHighMemBeg, ASAN_CEIL, kSpaceSize, kPrimResvSize in hP1, hP2, hSP1, hSP2.
assert (R : 0 <= SB < 2 ^ 64) by lia.
split; intros E; rewrite E in I1, I2.
- replace (0xa7da0 + 0x318) with (TFIB_INST + 0x20) in I1 by (unfold TFIB_INST; lia).
  pose proof (val_mem8_det _ _ _ _ C I1 R ltac:(lia)) as X. lia.
- replace (0xa7d90 + 0x328) with (TFIB_INST + 0x20) in I2 by (unfold TFIB_INST; lia).
  pose proof (val_mem8_det _ _ _ _ C I2 R ltac:(lia)) as X. lia.
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The regions of DGbigm.REG0 hold at the entry.                                                                    *)
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
| apply (zone3_off_img _ _ _ (proj1 vZONE)); pose proof N8_ge; unfold DGbigm.N8v in *; lia ].
Local Ltac reg_intro := unfold region_ok; cbn [YP09.r_base YP09.r_lo YP09.r_hi YP09.r_wlo YP09.r_whi YP09.r_chunks base_val].
Local Ltac r8 := change (2 ^ (8 * Z.of_N 8)) with (2 ^ 64); lia.
Local Ltac r4 := change (2 ^ (8 * Z.of_N 4)) with (2 ^ 32); lia.
Local Ltac lit_region :=
reg_intro; split; [lia|]; split; [lia|]; split; [intros o Ho; lia|];
repeat (apply Forall_cons; [apply chunk_lit; [apply cell_lit; vm_compute; reflexivity | cbn; lia | cbn; lia] |]); apply Forall_nil.
Lemma REG0_ok : Forall (region_ok tfibsegs E0 m0) DGbigm.REG0.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hSP1 & hSP2 & hP2 & hC1 & hC2 & hNB1 & hNB2 & hSB1 & hSB2 & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1, hNB1, hSB1.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (_ & Q8). pose proof Hhb as HBR.
pose proof SO_range as (SR1 & SR2 & BR1 & BR2). pose proof INST_range as (IR1 & IR2).
pose proof HIO as (IO1 & IO2 & IO3). pose proof vINST as HINST. pose proof vTSD as HTSD.
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (S1 : ly_stk_lo ly + DFSTACK <= sp0) by exact Hlo.
assert (S2 : sp0 <= ly_stk_hi ly) by exact Hhi.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kBatchBytes, kHighShadowBeg, kQuarantineCacheMax, kBatchSlots in
hP1, hP2, hT1, hT2, hNB1, hNB2, hSB1, hSB2, hC1, hC2, L4, L5, hSP1, hSP2, P1, P2, P11, P12.
unfold DGbigm.REG0, DGbigm.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8.
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
(* the instance's primary-space base at TFIB_INST + 0x20 (atom aSB): the image constant cell *)
apply Forall_cons. { reg_intro. unfold TFIB_INST. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 34%nat 0 SB); [rewrite Z.sub_0_r; reflexivity | lia | | cbn; lia | cbn; lia].
eapply val_mem_addr; [exact SB_cell | unfold TFIB_INST; lia]. }
apply Forall_cons. { reg_intro. unfold TFIB_TP. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply chunk_lit; [| unfold TFIB_TSD; cbn; lia | cbn; lia].
replace (6154032 - 88) with (aeval B ly (ATp (-88))) by (cbn; rewrite (ts_tp B TS); reflexivity).
replace TFIB_TSD with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; unfold TFIB_TSD; lia). apply cell_sym. vm_compute. reflexivity. }
apply Forall_cons. { reg_intro. unfold TFIB_TSD. split; [lia|]. split; [lia|]. split; [intros o Ho; lia|]. apply Forall_cons; [|apply Forall_nil].
apply (chunk_atom 0 _ 8 33%nat 0 (ly_C ly)); [rewrite EaC'; unfold w64; f_equal; lia | lia | | cbn; lia | cbn; lia].
rewrite Z.add_0_l. replace 6290136 with (aeval B ly (ATsd 0)) by (cbn; rewrite HTSD; reflexivity).
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
- apply (chunk_atom _ _ 4 38%nat 0 HWv); [rewrite Z.sub_0_r; reflexivity | unfold DGbigm.HWv; lia | replace (pa + -16) with (pa - 16) by lia; exact HW1 | unfold DGbigm.HWv; r4 | cbn; lia].
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
Lemma PAIRS_ok : pairwise_disjoint E0 DGbigm.REG0.
Proof.
pose proof LYB as (hT1 & hT2 & _ & _ & _ & _ & hC1 & hC2 & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1.
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & _).
pose proof vZONE as (ZP & _). unfold zone3 in ZP.
pose proof LYD as (_ & (_ & _ & DTC & DTS) & _ & _ & DCS). unfold zdisjoint in DTC, DTS, DCS. cbn [fst snd] in DTC, DTS, DCS.
pose proof P_ivs as (DPS & DPT & DPC).
pose proof SO_range as (SR1 & SR2 & _). pose proof INST_range as (IR1 & IR2). pose proof HIO as (IO1 & IO2 & IO3).
pose proof INST_NE as (NE1 & NE2).
assert (Usp : 0 <= sp0 < 2 ^ 64) by apply u64_range.
assert (S1 : ly_stk_lo ly + DFSTACK <= sp0) by exact Hlo.
assert (S2 : sp0 <= ly_stk_hi ly) by exact Hhi.
assert (SO1 : sp0 <= so) by exact Hso1.
apply pairwise_disjoint_of_extents. unfold DGbigm.REG0, DGbigm.TAILG, R_soG, R_scrG, R_slotG, ilit8, flit1, flit4, flit8, flits8, fatom8, extent_of_region.
cbn [map YP09.r_base YP09.r_lo YP09.r_hi base_val length Z.of_nat Pos.of_succ_nat Pos.succ Z.mul Z.add Pos.mul Pos.add].
unfold aSB, aSHB, aC, aT, aTOP, aJ1, aJ2, aJ3, aHW, aN, aINST, aSO, aBP, aLEN.
rewrite E2', E10', E11', E13', EaT', EaC'. unfold w64.
ceil; unfold kHighMemBeg, kHighMemEnd, ASAN_CEIL, kThreadObjSize, kSpaceSize, kPrimResvSize, kNodesBlockSize, kStoreBlockSize, DFSTACK in *.
rewrite !unsigned_lit_small by lia.
clear - S1 S2 L4 L5 Usp SO1 Hso2 IO1 IO2 IO3 NE1 NE2 hT1 hT2 hC1 hC2 ZP P1 P2 P5 DTC DTS DCS DPS DPT DPC CR CR0.
unfold TFIB_INST, TFIB_TP, TFIB_TSD, t_qc, t_unwinding, t_stats in *. cbn [zpairwise_disjoint zall_disjoint]. unfold zdisj. cbn [fst snd].
unfold zone3cases, TFIB_IMG_LO, TFIB_IMG_END, kLowShadowBeg, kHighMemBeg, ASAN_CEIL in hT1, hC1, ZP.
(* the last case: the instance's quarantine words against the primary-space base cell (INST_NE) *)
repeat split;
first [ clear DTC DTS DCS DPS DPT DPC hT1 hC1 ZP IO3 NE1 NE2; lia
| clear - hT1 CR0 IO1 IO2; lia
| clear - hC1 CR0 IO1 IO2; lia
| clear - ZP P5 CR0 IO1 IO2; lia
| clear - hC1 hC2 hT1 hT2 DTC; lia
| clear - hC1 hC2 S1 S2 L4 L5 Usp SO1 Hso2 DCS; lia
| clear - hT1 hT2 S1 S2 L4 L5 Usp SO1 Hso2 DTS; lia
| clear - hC1 hC2 ZP P5 DPC; lia
| clear - hT1 hT2 ZP P5 DPT; lia
| clear - S1 S2 L4 L5 Usp SO1 Hso2 ZP P5 DPS; lia
| clear - IO1 IO2 IO3 NE1 NE2; lia ].
Qed.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The facts of DGbigm.FFG: the frame atoms, then DGbigm.FFM without its sp fact.                                   *)
Lemma FACTS_ok : facts_ok E0 DGbigm.FFG.
Proof.
pose proof LYB as (hT1 & hT2 & hP1 & hSP1 & hSP2 & hP2 & hC1 & hC2 & hNB1 & hNB2 & hSB1 & hSB2 & L1 & L2 & L3 & L4 & L5).
unfold zone3 in hT1, hC1, hNB1, hSB1.
pose proof (lo_top ly vLY) as (T1 & T2 & T3 & T4 & T5 & T6 & T7).
pose proof p_facts as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & P11 & P12 & P13 & P14).
pose proof QB_facts as (QB & Q8). pose proof Hhb as HBR.
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
unfold facts_ok, DGbigm.FFG, frame_facts. cbn [f_atoms f_conds f_alias DGbigm.FFM tl app atoms_ok conds_ok alias_ok].
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
split. { apply (AF 38%nat HWv); [reflexivity| | | |]. all: clear - CR0 HBR; unfold DGbigm.HWv; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 39%nat nn); [reflexivity| | | |]. all: clear - CR0 Q8; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
split. { apply (AF 40%nat SHADOW_OFF); [reflexivity| | | |]. all: clear; unfold SHADOW_OFF; first [lia | reflexivity]. }
split. { apply (AF 41%nat SPv); [reflexivity| | | |]. all: unfold DGbigm.SPv, SHADOW_OFF in *; clear - CR0 P1 P2 P5 P11 P12 P13 P14 Q8; first [lia | change (2 ^ 1) with 2; exact P13 | rewrite P14 in P12; pose proof (Z.div_pos (nn + 7) 8); nia]. }
split. { apply (AF 42%nat N8v); [reflexivity| | | |]. all: clear - CR0 P5 P6 P7 Q8; first [lia | change (2 ^ 3) with 8; exact P7 | apply Z.mod_divide in P7 as [c Hc]; [|lia]; lia]. }
split. { apply (AF 43%nat CNT8v); [reflexivity| | | |]. all: clear - CR0 P5 P6 P14 Q8; rewrite ?P14 in *; unfold DGbigm.N8v in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r | nia]. }
split. { apply (AF 50%nat QBv); [reflexivity| | | |]. all: clear - CR0 QB; unfold DGbigm.QBv, kQuarantineCacheMax in *; first [lia | change (2 ^ 0) with 1; apply Z.mod_1_r]. }
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
Lemma SEED_ok : st_ok tfibsegs E0 DGbigm.SS0 (restrict (w_H W) (mkst regs (w64 A_Deallocate) mem (seg_rom tfibsegs))).
Proof.
rewrite restrict_mkst_fx. unfold DGbigm.SS0, w64, st_ok.
cbn [ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_regs ms_mem mkst ss_pc ss_regs ss_mem ss_resv ss_facts resv_denot].
repeat (split; [reflexivity|]). split; [exact REGS_ok|]. split; [|exact FACTS_ok].
split; [vm_compute; reflexivity|]. split; [exact REG0_ok | exact PAIRS_ok].
Qed.
Theorem FH_ok : DGbigm.free_hyps W ly regs0 mem tr pa nn hb1 q j1 j2 j3 regs.
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
- exact vQB.
- split; [exact HJ1R | split; [exact HJ2R | exact HJ3R]].
- exact vIAL.
- exact SEED_ok.
- rewrite G12. unfold w64. rewrite unsigned_lit_small by lia. exact PBUF.
Qed.
End h.

(* ---------------------------------------------------------------------------------------------------------------- *)
(* The seed of the big-block arm from the generic precondition and the big view.                                   *)
Theorem FH_m : forall U ARX rpre fpre inst so bp ly S W regs mem md p n tr,
DeallocG.dealloc_pre tfibsegs B U ARX rpre fpre 1 inst so bp ly S W regs mem md p n tr ->
In (p, n) (blocks S) -> inst_ok inst -> DGbigIF.dview_big B W ly inst mem S p n ->
exists hb1 j1 j2 j3,
0 <= hb1 < 256 /\ val_mem tfibsegs (mrestrict (w_H W) mem) (sptr_addr B ly p - 16) 4 (2 + 256 * hb1) /\
DGbigm.free_hyps W ly (dregs regs (sptr_addr B ly p) inst bp so) mem tr (sptr_addr B ly p) (req_size n) hb1 (st_qthread S) j1 j2 j3 regs.
Proof.
intros U ARX rpre fpre inst so bp ly S W regs mem md p n tr PRE HBLK HIO DV.
destruct PRE as (_ & _ & Hra & Hra4096 & Hal & Hlo & Hbot & Hhi & HPRES & _ & Htp & H10 & H11 & H12 & H13 & H14 & H15 &
Hso1 & Hso2 & Hso3 & Hbp1 & Hbp2 & Hbp3 & Htrlen & PSO & PLEN & PBUF & _ & _ & _).
pose proof DV as [_ _ _ (hb1 & Hhb & Hhbm & HW1 & HW2) PRES JUNK _ _].
destruct (pres_word (w_H W) mem (ly_T ly + t_stats + 24) ltac:(intros i Hi; apply JUNK; lia)) as (j1 & J1R & J1).
destruct (pres_word (w_H W) mem (ly_T ly + t_stats + 32) ltac:(intros i Hi; apply JUNK; lia)) as (j2 & J2R & J2).
destruct (pres_word (w_H W) mem (sptr_addr B ly p) ltac:(intros i Hi; apply PRES; lia)) as (j3 & J3R & J3).
exists hb1, j1, j2, j3. split; [exact Hhb|]. split; [exact HW1|].
eapply FH_ok; eassumption.
Qed.
End g.
End f.
About FH_ok.
About FH_m.
