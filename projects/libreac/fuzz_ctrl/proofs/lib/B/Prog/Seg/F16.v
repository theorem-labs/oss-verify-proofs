(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libpcap/fuzz_pcap/lib/E2/Lib/Tac.v; 978 of its 1011 lines of code are new or changed and 2109 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/B/Prog/Seg/A4.v, with its module paths and module names changed; 3124 of its 3235 lines of code are new or changed and 900 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_ctrl/lib/A/Prog/Seg/F4.v, with its module paths, module names and numbers changed; 1366 of its 1577 lines of code are new or changed and 3024 lines of the source are left out. *)
(* Segment F16 of fuzz_ctrl LLVMFuzzerTestOneInput (asan-ubsan, image B), libreac v1.9.0: the cut-to-cut range
   0x823d8 .. 0x82464 (v1.8: 0x82370 .. 0x823e0; the cut names Inv_B823d8_at / Inv_B82464_at are still the v1.8
   ones).  Four calls, all Section hypotheses: HRSC (lib/B/Prog/record_sum_closes_c.v; it writes only its 16 stack
   bytes), HJB (lib/B/Prog/joined_byte_c.v, a Theorem Labs lane's contract; called twice, it writes only its 16 stack bytes;
   the assembly discharges it with joined_byte.v's joined_byte_holds) and HING (lib/B/Prog/reac_identity_ingest_c.v;
   it writes only its 32 stack bytes and the 38 identity bytes [id, id + 38)).
     0x823d8 ld a0,120(s1)      a0 := [A+120] = fragb fr + 15 (FLI / FLV)
     0x823dc jal 83614          record_sum_closes(a0, a1), a1 = pll + 5 (set at 0x823d4 in F15b; carried)
     0x823e0 beqz a0,82fa4      the turn closes a record, so the record's 15-offset window sums to 0 mod 128
                                (sum_closes, from fg_close's recsum conjunct); the callee returns 1: not taken
     0x823e4 ld a0,168(s1)      a0 := [A+168] = fr + 2880, the local `first` (FLI)
     0x823e8 lw a0,0(a0)        a0 := first->have = 1 (FSj: FI with frag_ok and fg_keep) ...
     0x823ec beqz a0,82fa4      ... not taken
     0x823f0-0x823f4            s5 := the u16 at [A+288] = fr + 256, the parser's address cell = fg_addr
     0x823f8-0x82410            a2 := 9, s6 := a0 := fr + 2880, s11 := s8 (k), s8 := s9 (sum flag),
                                s9 := a1 := [A+312] = Phi + 18 (FM: the block pointer of a long frame)
     0x82414 jal 836ac          joined_byte(first, blk, 9) = SlotModel.joined_byte (FSj's n / body, FTURN's
                                frame bytes: joined_byte_model)
     0x82418-0x82434            s7 := a0 << 8, a2 := 10, a0 := s6, s6 := 1, a1 := s9, s9 := s8, s8 := s11,
                                s11 := -8 (s6 / s8 / s9 / s11 hold their frame-loop values again)
     0x82438 jal 836ac          joined_byte(first, blk, 10)
     0x8243c-0x82440            a0 := s7 | a0 = joined_addr = fg_addr (joined_close): bne a0,s5 not taken
     0x82444-0x8245c            a1 := the u16 at fr + 256, a2 := [[A+304]] = [fr+272] = fragb fr + 19,
                                a3 := [[A+296]] = [fr+304] = pll (FLV), a0 := [A+176] = fr + 2688
     0x82460 jal 87e0c          reac_identity_ingest(id, fg_addr, fragb fr + 19, pll); the run lands at 0x82464
   The three branches to 0x82fa4 are the error path; each is shown not taken.  There is no instrumented check in
   the range.

   The whole segment writes W = [sp - 32, sp) (the callees' stack bytes; the ingest frame is the largest) and
   [fr + 2688, fr + 2726).  FRA moves across W by Tac_slot.sl_fr_cl (AH / stklo per frame arm: the allocator law
   a_laws_store on the real arm, Tac_fs.a_fs_ok_store_AH on the side arm) and sl_fra_move, ENT by Tac_slot.ent_store
   / ent_mat, ro_agree because both intervals of W start at or above GT, and the carried facts by their placement
   against W.  No callee contract asks for mem_inv, and no cut carries it.

   Cuts.  Both are the official cuts of lib/B/Prog/SlotInv.v: the entry Inv_B823d8_at (0x823d8, F15b's exit: the
   F17 entry facts with rec_inv and the two compares under t_8819, the record-sum, first-fragment / address and
   ingest argument blocks, a1 = pll + 5, the closed record, the address cell, the identity record, FTURN, RECF and
   FS9) and the exit Inv_B82464_at (0x82464, F17's entry: the same F17 entry facts after the ingest, FTURN, the
   records of turn j + 1 (RECS) and FS9).  The placements the exit asks for (the window of `first`, Phi and the
   record pointer against it and against the wrapper_bcmp scratch) are carried by the entry cut. *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Fpu Sem.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT AsanRTInv AsanRTFacts PContract MemNorm AsanLift.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import KindBGlue.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec Require StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require record_sum_closes_c reac_identity_ingest_c.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog Require joined_byte_c joined_byte.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcModel RcFrag RcFragLib RcRec RcIdentModel.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcIdentLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Import Tac_slot.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.Seg Require Tac_fs.
(* The Lib engine (evt, MS, step) comes last, as in Seg/F13.v: both callee contracts speak Lib.Exec.evt. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Cells Step Tac Bytes ZBridge.
Import ListNotations.
(* Later imports shadow image B's getr (the one rg / FRA use); make it the default again. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Reusable.YK11.
Open Scope Z_scope.

Module AC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Contract.
Module AF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.FrameAPI.
Module LMS := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.MState.
Module LFr := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Frame.
Module LMem := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Mem.
Module LSt := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Step.
Module LCl := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib.Cells.
Module RSC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.record_sum_closes_c.
Module IGC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.reac_identity_ingest_c.
Module JBC := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.joined_byte_c.
Module JB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Prog.joined_byte.
Module SF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.Spec.StrFun.
Module BZB := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B.BzBridge.

(* ===== Engine and memory helpers ===== *)

(* Carried byte facts in the `ov_read_bytes _ _ _ n = Some bs` form the engine's `step` consumes. *)
Lemma f16_rd1 : forall m a b, bytes_at rsegs m a [b] -> ov_read_bytes rsegs m (LMem.wa a) 1 = Some [b].
Proof.
  intros m a b H.
  pose proof (LMem.bytes_at_ov_read rsegs m a [b] 0 1 H ltac:(cbn; lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r in HH. cbn [firstn skipn] in HH. exact HH.
Qed.
Lemma f16_rd2 : forall m a bs, bytes_at rsegs m a bs -> length bs = 2%nat ->
  ov_read_bytes rsegs m (LMem.wa a) 2 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (LMem.bytes_at_ov_read rsegs m a bs 0 2 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f16_rd8 : forall m a bs, bytes_at rsegs m a bs -> length bs = 8%nat ->
  ov_read_bytes rsegs m (LMem.wa a) 8 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (LMem.bytes_at_ov_read rsegs m a bs 0 8 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.
Lemma f16_rd4 : forall m a bs, bytes_at rsegs m a bs -> length bs = 4%nat ->
  ov_read_bytes rsegs m (LMem.wa a) 4 = Some bs.
Proof.
  intros m a bs H Hl.
  pose proof (LMem.bytes_at_ov_read rsegs m a bs 0 4 H ltac:(lia)) as HH.
  change (Z.of_nat 0) with 0%Z in HH. rewrite Z.add_0_r, skipn_O, firstn_all2 in HH by lia. exact HH.
Qed.

(* Byte and 16-bit arithmetic of the address compare 0x82418 / 0x8243c-0x82440. *)
Lemma f16_zxb8 : forall v, 0 <= v < 256 -> zxb (Z_to_bv 8 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zxb. f_equal. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus; cbn; lia.
Qed.
(* `slli a1,a1,8 ; or a0,a1,a0` on two byte values. *)
Lemma f16_or8 : forall lo hi, 0 <= lo < 256 -> 0 <= hi < 256 ->
  Z_to_bv 64 (Z.lor (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 hi)) 8)))
                    (bv_unsigned (Z_to_bv 64 lo)))
  = Z_to_bv 64 (lo + 256 * hi).
Proof.
  intros lo hi Hlo Hhi.
  rewrite (LMS.unsigned_lit hi) by lia. rewrite (LMS.unsigned_lit lo) by lia.
  rewrite (LMS.unsigned_lit (Z.shiftl hi 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  rewrite Z.lor_comm, lor_shiftl8_add by lia. reflexivity.
Qed.
(* `slli a0,a0,48 ; srli a1,a0,48` keeps a 16-bit value. *)
Lemma f16_sh48 : forall v, 0 <= v < 65536 ->
  Z_to_bv 64 (Z.shiftr (bv_unsigned (Z_to_bv 64 (Z.shiftl (bv_unsigned (Z_to_bv 64 v)) 48))) 48)
  = Z_to_bv 64 v.
Proof.
  intros v Hv. rewrite (LMS.unsigned_lit v) by lia.
  rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (LMS.unsigned_lit (v * 2 ^ 48)) by (change (2 ^ 48) with 281474976710656; lia).
  rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul by (vm_compute; discriminate). reflexivity.
Qed.
Lemma f16_zx16 : forall v, 0 <= v < 65536 -> zx16 (Z_to_bv 64 v) = Z_to_bv 64 v.
Proof.
  intros v Hv. unfold zx16. rewrite (LMS.unsigned_lit v) by lia.
  rewrite Z.mod_small by (change (2 ^ 16) with 65536; lia). reflexivity.
Qed.

(* outside / disjointness of the two-interval write set W = [(lo1,hi1); (lo2,hi2)]. *)
Lemma f16_out2 : forall lo1 hi1 lo2 hi2 x,
  (x < lo1 \/ hi1 <= x) -> (x < lo2 \/ hi2 <= x) -> LFr.outside [(lo1, hi1); (lo2, hi2)] x.
Proof. intros lo1 hi1 lo2 hi2 x H1 H2. cbn. split; [lia | split; [lia | exact I]]. Qed.
Lemma f16_not_out2 : forall lo1 hi1 lo2 hi2 x,
  ~ LFr.outside [(lo1, hi1); (lo2, hi2)] x -> (lo1 <= x < hi1) \/ (lo2 <= x < hi2).
Proof.
  intros lo1 hi1 lo2 hi2 x H.
  destruct (Z_lt_le_dec x lo1) as [H1|H1].
  - destruct (Z_lt_le_dec x lo2) as [H3|H3].
    + exfalso. apply H. apply f16_out2; lia.
    + destruct (Z_lt_le_dec x hi2) as [H4|H4]; [right; lia|].
      exfalso. apply H. apply f16_out2; lia.
  - destruct (Z_lt_le_dec x hi1) as [H2|H2]; [left; lia|].
    destruct (Z_lt_le_dec x lo2) as [H3|H3].
    + exfalso. apply H. apply f16_out2; lia.
    + destruct (Z_lt_le_dec x hi2) as [H4|H4]; [right; lia|].
      exfalso. apply H. apply f16_out2; lia.
Qed.
Lemma f16_out_dec : forall (W : list (Z * Z)) x, LFr.outside W x \/ ~ LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x; [left; exact I|].
  destruct (Z.le_gt_cases lo x) as [H1|H1].
  - destruct (Z.le_gt_cases hi x) as [H2|H2].
    + destruct (IH x) as [Ho|Hno]; [left; split; [lia|exact Ho] | right; intros [_ Ho]; exact (Hno Ho)].
    + right. intros [Hc _]. apply Hc. lia.
  - destruct (IH x) as [Ho|Hno]; [left; split; [lia|exact Ho] | right; intros [_ Ho]; exact (Hno Ho)].
Qed.
(* Every interval of W starts at or above GT, so W misses the runtime's cells (all in the image). *)
Lemma f16_dj_GT : forall (W : list (Z * Z)) a n,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> a + n <= AC.GT -> disjoint_from W a n.
Proof.
  intros W a n H Hn. induction W as [|[lo hi] W IH]; cbn; [exact I|].
  split.
  - left. pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH. intros lo' hi' Hin. apply (H lo' hi'). right. exact Hin.
Qed.
Lemma f16_rtdj_GT : forall (W : list (Z * Z)),
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> AsanRTInv.rt_disjoint W.
Proof.
  intros W H. unfold AsanRTInv.rt_disjoint, RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF,
    RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ, RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG,
    RT_AGLOB, RT_AGLOB_LEN, AC.GT in *.
  repeat split; apply (f16_dj_GT W); solve [ exact H | unfold AC.GT; lia ].
Qed.
(* A non-app address is outside an all-app write set. *)
Lemma f16_out_not_app : forall (W : list (Z * Z)) x, all_app W -> ~ app_mem x -> LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x HA Hn; [exact I|].
  destruct HA as [Ha HA].
  split; [intro Hr; apply Hn; apply Ha; lia | apply IH; [exact HA | exact Hn]].
Qed.
(* Every read-only byte is a byte of a loaded segment, and every loaded segment ends below GT
   (Tac_slot.img_tops_true), so a write set whose intervals all start at or above GT keeps ro_agree. *)
Lemma f16_ro_lt_GT : forall x, LMem.ro_addr rsegs x = true -> bv_unsigned x < AC.GT.
Proof.
  intros x H. unfold LMem.ro_addr in H.
  destruct (find_segment rsegs (bv_unsigned x) 1) as [s|] eqn:E; [|discriminate H].
  destruct (BZB.find_segment_below rsegs AC.GT (bv_unsigned x) 1 s img_tops_true E ltac:(lia))
    as [L|L]; [exact L | lia].
Qed.
Lemma f16_out_GT : forall (W : list (Z * Z)) x,
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> x < AC.GT -> LFr.outside W x.
Proof.
  induction W as [|[lo hi] W IH]; cbn; intros x H Hx; [exact I|].
  split.
  - pose proof (H lo hi ltac:(left; reflexivity)). lia.
  - apply IH; [intros lo' hi' Hin; apply (H lo' hi'); right; exact Hin | exact Hx].
Qed.
Lemma f16_ro_keep : forall (W : list (Z * Z)) m m',
  (forall lo hi, In (lo, hi) W -> AC.GT <= lo) -> LFr.munch W m m' ->
  ro_agree rsegs m -> ro_agree rsegs m'.
Proof.
  intros W m m' HGT MU Hro a Ha.
  pose proof (Hro a Ha) as H. unfold LMem.mrd in H |- *.
  rewrite (MU a (f16_out_GT W (bv_unsigned a) HGT (f16_ro_lt_GT a Ha))). exact H.
Qed.

(* The runtime cells the callees read (CELL_K, GOT_CELL_K) and the shadow map are outside the callees' stack
   bytes [sp - k, sp) and outside the identity record (application memory at or above GT). *)
Lemma f16_rt_out1 : forall sp x k, HIGHMEM_BEG <= sp - k -> 0 <= k ->
  (GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x) ->
  LFr.outside [(sp - k, sp)] x.
Proof.
  intros sp x k Hsp Hk Hx. cbn. split; [|exact I].
  unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia.
Qed.
Lemma f16_rt_out2 : forall sp fr x, HIGHMEM_BEG <= sp - 32 -> AC.GT <= fr ->
  (forall a, fr <= a < fr + 3136 -> app_mem a) ->
  (GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x) ->
  LFr.outside [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)] x.
Proof.
  intros sp fr x Hsp Hfr Happ Hx.
  assert (Hs : ~ (sp - 32 <= x < sp)).
  { unfold GOT_CELL_K, CELL_K, in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG in *. lia. }
  assert (Hi : ~ (fr + 2688 <= x < fr + 2688 + 38)).
  { destruct Hx as [Hx|[Hx|Hx]].
    - unfold GOT_CELL_K, AC.GT in *. lia.
    - unfold CELL_K, AC.GT in *. lia.
    - intro Hin. exact (app_not_shadow x (Happ x ltac:(lia)) Hx). }
  cbn. split; [exact Hs | split; [exact Hi | exact I]].
Qed.
(* The 392 shadow bytes of the frame base are all shadow addresses (392 * 8 = 3136 frame bytes). *)
Lemma f16_frame_shadow : forall fr x, (forall a, fr <= a < fr + 3136 -> app_mem a) ->
  Sfr fr <= x < Sfr fr + 392 -> in_shadow x.
Proof.
  intros fr x Happ Hx.
  assert (Hdiv : (fr + 8 * (x - Sfr fr)) / 8 = fr / 8 + (x - Sfr fr)).
  { replace (8 * (x - Sfr fr)) with ((x - Sfr fr) * 8) by lia. rewrite Z.div_add by lia. reflexivity. }
  assert (Hinfr : fr <= fr + 8 * (x - Sfr fr) < fr + 3136) by lia.
  pose proof (shadow_of_app (fr + 8 * (x - Sfr fr)) (Happ _ Hinfr)) as His.
  replace (shadow_addr (fr + 8 * (x - Sfr fr))) with x in His; [exact His|].
  unfold shadow_addr. rewrite Hdiv. unfold Sfr, shadow_addr. lia.
Qed.
(* A byte inside a carried byte range is present. *)
Lemma f16_present : forall m A bs q, bytes_at rsegs m A bs -> A <= q < A + Z.of_nat (length bs) ->
  exists b, LMem.mrd rsegs m (LMem.wa q) = Some b.
Proof.
  intros m A bs q (Ha & Hl & H) Hq.
  assert (Hk : (Z.to_nat (q - A) < length bs)%nat) by lia.
  pose proof (H (Z.to_nat (q - A)) Hk) as HH.
  replace (A + Z.of_nat (Z.to_nat (q - A))) with q in HH by lia.
  destruct (nth_error bs (Z.to_nat (q - A))) as [b|] eqn:Eb.
  - exists b. exact HH.
  - apply nth_error_None in Eb. lia.
Qed.
(* The 38 identity bytes of the ingest post, as a byte range. *)
Lemma f16_lrw38 : forall m a bs, LSt.rw_cells rsegs m a [LCl.CB 38 bs] -> bytes_at rsegs m a bs.
Proof. intros m a bs [[_ H] _]. cbn [LCl.cells_bytes LCl.cbytes] in H. rewrite app_nil_r in H. exact H. Qed.

(* stk across a run: outside the write set by munch, inside it by the caller's presence facts. *)
Lemma f16_stk_tr : forall W m m' lo hi,
  LFr.stk rsegs m lo hi -> LFr.munch W m m' -> LFr.wmono rsegs m m' ->
  (forall x, lo <= x < hi -> LFr.outside W x \/ (exists b, LMem.mrd rsegs m' (LMem.wa x) = Some b)) ->
  LFr.stk rsegs m' lo hi.
Proof.
  intros W m m' lo hi (H1 & H2 & H) MU WM HK.
  split; [exact H1|]. split; [exact H2|].
  intros a Ha. destruct (H a Ha) as (Hw & b & Hb).
  split; [exact (WM (LMem.wa a) Hw)|].
  destruct (HK a Ha) as [Ho|Hp].
  - exists b. unfold LMem.mrd in *. rewrite (MU (LMem.wa a)); [exact Hb|].
    unfold LMem.wa. rewrite LMS.unsigned_lit by lia. exact Ho.
  - exact Hp.
Qed.

Lemma f16_bsl_len_le : forall bs k n, (length (bsl bs k n) <= Z.to_nat n)%nat.
Proof. intros bs k n. unfold bsl. rewrite length_firstn. apply Nat.le_min_l. Qed.

(* The record invariant of SlotInv across a write set that misses Phi, the spills A+288..A+320, the record
   pointer's u16 and the shadow map. *)
Lemma f16_rec_inv_keep : forall g j phi A kp m m' W,
  rec_inv g j phi A kp m -> LFr.munch W m m' ->
  (forall x, phi <= x < phi + 50 -> LFr.outside W x) ->
  (forall x, A + 248 <= x < A + 320 -> LFr.outside W x) ->
  (forall x, in_shadow x -> LFr.outside W x) ->
  (forall x, kp + 20 <= x < kp + 22 -> LFr.outside W x) ->
  rec_inv g j phi A kp m'.
Proof.
  intros g j phi A kp m m' W (Hp0 & Hp50 & Hfl & Htk & Hpap & H312 & H18 & H34 &
     field16 & v14 & v15 & v16 & v17 & H248 & Hf16 & Hkpub & Hkp0 & Hb14 & Hb15 & Hb16 & Hb17 &
     Rv14 & Rv15 & Rv16 & Rv17 & Hs14 & Hs15 & Hs16 & Hs17 & Heq1 & Heq2)
    MU OWphi OWspill OWsh OWkp.
  assert (SH : forall t, 14 <= t <= 17 -> LFr.outside W (Z.shiftr (phi + t) 3 + ASAN_K)).
  { intros t Ht. apply OWsh.
    rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    pose proof (shadow_of_app (phi + t) (Hpap (phi + t) ltac:(lia))) as His.
    unfold shadow_addr, ASAN_K in *. exact His. }
  unfold rec_inv.
  split; [exact Hp0|]. split; [exact Hp50|]. split; [exact Hfl|]. split; [exact Htk|]. split; [exact Hpap|].
  split; [unfold q64 in *; eapply fl_bytes; [exact H312 | exact MU | rewrite LMem.length_le8; intros x Hx; apply OWspill; lia]|].
  split; [eapply fl_bytes; [exact H18 | exact MU | intros x Hx; apply OWphi; unfold t_blk in Hx;
            pose proof (f16_bsl_len_le (t_g (g_in g) j) 18 32) as BL; change (Z.to_nat 32) with 32%nat in BL; lia]|].
  split; [eapply fl_bytes; [exact H34 | exact MU | intros x Hx; apply OWphi;
            pose proof (f16_bsl_len_le (t_g (g_in g) j) 34 6) as BL; change (Z.to_nat 6) with 6%nat in BL; lia]|].
  exists field16, v14, v15, v16, v17.
  split; [unfold q64 in *; eapply fl_bytes; [exact H248 | exact MU | rewrite LMem.length_le8; intros x Hx; apply OWspill; lia]|].
  split; [unfold u16 in *; eapply fl_bytes; [exact Hf16 | exact MU | rewrite LMem.length_le2; intros x Hx; apply OWkp; lia]|].
  split; [exact Hkpub|]. split; [exact Hkp0|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb14 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb15 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb16 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hb17 | exact MU | cbn [length]; intros x Hx; apply OWphi; lia]|].
  split; [exact Rv14|]. split; [exact Rv15|]. split; [exact Rv16|]. split; [exact Rv17|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs14 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 14) 3 + ASAN_K) by lia; apply (SH 14); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs15 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 15) 3 + ASAN_K) by lia; apply (SH 15); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs16 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 16) 3 + ASAN_K) by lia; apply (SH 16); lia]|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hs17 | exact MU | cbn [length]; intros x Hx;
            replace x with (Z.shiftr (phi + 17) 3 + ASAN_K) by lia; apply (SH 17); lia]|].
  split; [exact Heq1|]. exact Heq2.
Qed.

(* Z_to_bv 64 is injective on [0, 2^64). *)
Lemma f16_bv_inj : forall x y, 0 <= x < 2 ^ 64 -> 0 <= y < 2 ^ 64 -> Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !LMS.unsigned_lit in E by lia. exact E.
Qed.
(* and on [-440, 2^64) x [0, 2^64 - 448]: a spill base read off a spill fact is the cut's base (the save area
   of this function is 448 bytes, so a spill offset is at most 440). *)
Lemma f16_bv_inj_spill : forall x y, -440 <= x < 2 ^ 64 -> 0 <= y <= 2 ^ 64 - 448 ->
  Z_to_bv 64 x = Z_to_bv 64 y -> x = y.
Proof.
  intros x y Hx Hy E. apply (f_equal (bv_unsigned (n:=64))) in E.
  rewrite !LMS.unsigned_lit_wrap in E. rewrite (Z.mod_small y) in E by lia.
  destruct (Z_lt_le_dec x 0) as [Hn|Hp].
  - assert (Em : x mod 2 ^ 64 = x + 2 ^ 64).
    { rewrite <- (Z.mod_add x 1 (2 ^ 64)) by lia. rewrite Z.mod_small by lia. lia. }
    lia.
  - rewrite Z.mod_small in E by lia. exact E.
Qed.

(* The register-reading helpers live under the FP state of the cuts (getr and rg both take it). *)
Section FX.
Context {fx : FPState}.

(* A spill cell read at the cut's own spill base A (pinned by register 9). *)
Lemma f16_spill_q64 : forall regs m off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  q64 m (A + off) v.
Proof.
  intros regs m off v A (A' & HA' & Hq) HA HA0 HA1 Hoff.
  pose proof (LMem.bytes_at_bound rsegs m _ _ Hq) as Hb. rewrite LMem.length_le8 in Hb.
  assert (EA : A' = A).
  { apply f16_bv_inj_spill; [lia | lia |].
    unfold rg in *. transitivity (getr regs 9); [symmetry; exact HA' | exact HA]. }
  subst A'. exact Hq.
Qed.
(* A spill survives a register change that keeps s1 and a write that misses its 8 bytes. *)
Lemma f16_spill_keep : forall regs regs' m m' W off v A,
  spill regs m off v -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 -> 0 <= off <= 440 ->
  getr regs' 9 = getr regs 9 -> LFr.munch W m m' ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  spill regs' m' off v.
Proof.
  intros regs regs' m m' W off v A Hs HA HA0 HA1 Hoff E9 MU HO.
  pose proof (f16_spill_q64 regs m off v A Hs HA HA0 HA1 Hoff) as Hq.
  exists A. split; [unfold rg in *; rewrite E9; exact HA|].
  unfold q64 in *. eapply fl_bytes; [exact Hq | exact MU |].
  rewrite LMem.length_le8. intros x Hx. apply HO. cbn in Hx. lia.
Qed.

Ltac f16_sk HX H9 E9 MU HO :=
  eapply f16_spill_keep; [exact HX | exact H9 | lia | lia | lia | exact E9 | exact MU | exact HO].

(* The frame-loop bundles across the run: s1 and the cut registers are kept, and the run's writes miss the spill
   area [A, A + 448) and the our[] bytes [fr + 2624, fr + 2630). FLI's our[] addressability stays because the
   write set is app memory (sl_addr_keep), and its frame-body stk because a frame byte the run writes is present
   afterwards (f16_stk_tr). *)
Lemma f16_fli_keep : forall g fr regs regs' m m' W A,
  FLI g fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 -> LFr.munch W m m' ->
  LFr.wmono rsegs m m' -> all_app W ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  (forall x, 0 <= x < AC.GT -> LFr.outside W x) ->
  (forall x, fr <= x < fr + 3136 -> LFr.outside W x \/ (exists b, LMem.mrd rsegs m' (LMem.wa x) = Some b)) ->
  FLI g fr regs' m'.
Proof.
  intros g fr regs regs' m m' W A H H9 HA0 HA1 E9 E27 MU WM HAW HO Hlow Hrd. unfold FLI in H |- *.
  destruct H as (H27 & H).
  split; [unfold rg in *; rewrite E27; exact H27|].
  repeat (let X := fresh "X" in destruct H as (X & H); split; [f16_sk X H9 E9 MU HO|]).
  destruct H as (Had & Hstk & (Hrad1 & Hrad2 & Hrad3) & (Hknt1 & Hknt2) & S168 & S88).
  split; [exact (sl_addr_keep m m' W (fr + 2624) 6 Had MU HAW)|].
  split; [exact (f16_stk_tr W m m' fr (fr + 3136) Hstk MU WM Hrd)|].
  (* RAD: the three frame records stay marked usable (the write set is app memory) *)
  split; [split; [exact (sl_addr_keep m m' W (fr + 2688) 38 Hrad1 MU HAW)|
                  split; [exact (sl_addr_keep m m' W (fragb fr) 72 Hrad2 MU HAW)
                         | exact (sl_addr_keep m m' W (fr + 2880) 40 Hrad3 MU HAW)]]|].
  (* KNT: the kind-name table is image memory below GT, which the write set misses *)
  split.
  { split.
    - assert (HKL : length KNC.kind_name_bytes = 112%nat) by reflexivity.
      eapply fl_bytes; [exact Hknt1 | exact MU |].
      rewrite HKL. intros x Hx. apply Hlow. unfold KNC.KIND_NAME, AC.GT in *. lia.
    - exact (sl_addr_keep m m' W KNC.KIND_NAME 112 Hknt2 MU HAW). }
  split; [f16_sk S168 H9 E9 MU HO | f16_sk S88 H9 E9 MU HO].
Qed.
Lemma f16_lk_keep : forall g fr j regs regs' m m' W A,
  LK g fr j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 27 = getr regs 27 -> LFr.munch W m m' ->
  LFr.wmono rsegs m m' -> all_app W ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  (forall x, fr + 2624 <= x < fr + 2630 -> LFr.outside W x) ->
  (forall x, 0 <= x < AC.GT -> LFr.outside W x) ->
  (forall x, fr <= x < fr + 3136 -> LFr.outside W x \/ (exists b, LMem.mrd rsegs m' (LMem.wa x) = Some b)) ->
  LK g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W A (Hj & H240 & HOUR & HFLI) H9 HA0 HA1 E9 E27 MU WM HAW HO HOo Hlow Hrd.
  split; [exact Hj|].
  split; [f16_sk H240 H9 E9 MU HO|].
  split.
  { unfold OURb in *. eapply fl_bytes; [exact HOUR | exact MU |].
    rewrite OUR_length. intros x Hx. apply HOo. cbn in Hx. lia. }
  exact (f16_fli_keep g fr regs regs' m m' W A HFLI H9 HA0 HA1 E9 E27 MU WM HAW HO Hlow Hrd).
Qed.
(* FM (v1.9.0): the fill flag [A+184], k = s8, s6 = 1, the sum flag s9 and the block [A+312]. *)
Lemma f16_fm_keep : forall g j phi fr regs regs' m m' W A,
  FM g j phi fr regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> getr regs' 22 = getr regs 22 -> getr regs' 24 = getr regs 24 ->
  getr regs' 25 = getr regs 25 -> LFr.munch W m m' ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  FM g j phi fr regs' m'.
Proof.
  intros g j phi fr regs regs' m m' W A (H184 & H24 & H22 & H25 & H312) H9 HA0 HA1 E9 E22 E24 E25 MU HO.
  split; [f16_sk H184 H9 E9 MU HO|].
  split; [unfold rg in *; rewrite E24; exact H24|].
  split; [unfold rg in *; rewrite E22; exact H22|].
  split; [unfold rg in *; rewrite E25; exact H25 | f16_sk H312 H9 E9 MU HO].
Qed.
(* FSj (v1.9.0): the local `first` at fr + 2880 (have, n, the body from fr + 2885, its 40 usable bytes) and FI,
   across a write set of app memory that misses [fr + 2880, fr + 2920); the body is at most 35 bytes long. *)
Lemma f16_fsj_keep : forall g fr j regs regs' m m' W,
  FSj g fr j regs m -> LFr.munch W m m' -> all_app W ->
  (forall x, fr + 2880 <= x < fr + 2920 -> LFr.outside W x) ->
  (length (fs_body (fst_at (g_in g) j)) <= 35)%nat ->
  FSj g fr j regs' m'.
Proof.
  intros g fr j regs regs' m m' W (Hhave & Hn & Hbody & Had & HFI) MU HAW HO HBL.
  split; [unfold u32 in *; eapply fl_bytes; [exact Hhave | exact MU |];
          rewrite LMem.length_le4; intros x Hx; apply HO; lia|].
  split; [unfold b8 in *; eapply fl_bytes; [exact Hn | exact MU |]; cbn [length]; intros x Hx; apply HO; lia|].
  split; [eapply fl_bytes; [exact Hbody | exact MU |]; intros x Hx; apply HO; lia|].
  split; [exact (sl_addr_keep m m' W (fr + 2880) 40 Had MU HAW) | exact HFI].
Qed.
(* FS9 (v1.9.0): the spill [A+248]. *)
Lemma f16_fs9_keep : forall g j regs regs' m m' W A,
  FS9 g j regs m -> rg regs 9 A -> 0 <= A -> A + 448 <= 2 ^ 64 ->
  getr regs' 9 = getr regs 9 -> LFr.munch W m m' ->
  (forall x, A <= x < A + 448 -> LFr.outside W x) ->
  FS9 g j regs' m'.
Proof. intros g j regs regs' m m' W A H H9 HA0 HA1 E9 MU HO. unfold FS9 in *. f16_sk H H9 E9 MU HO. Qed.

(* mkR_of regs is definitionally the explicit 31-slot register map; exposing it lets `step` read a slot we have
   rewritten to a concrete value. *)
Lemma f16_mkR_of_expand : forall regs, Regs6ss.mkR_of regs =
  mkR (getr regs 1) (getr regs 2) (getr regs 3) (getr regs 4) (getr regs 5) (getr regs 6)
  (getr regs 7) (getr regs 8) (getr regs 9) (getr regs 10) (getr regs 11) (getr regs 12)
  (getr regs 13) (getr regs 14) (getr regs 15) (getr regs 16) (getr regs 17) (getr regs 18)
  (getr regs 19) (getr regs 20) (getr regs 21) (getr regs 22) (getr regs 23) (getr regs 24)
  (getr regs 25) (getr regs 26) (getr regs 27) (getr regs 28) (getr regs 29) (getr regs 30) (getr regs 31).
Proof. intros regs. reflexivity. Qed.

End FX.

(* Rewrite a known register slot `getr regs r` to its carried concrete value, from H : rg regs r v. *)
Ltac f16_subst_slot H :=
  let HH := fresh in pose proof H as HH; unfold rg in HH; rewrite HH; clear HH.

(* ===== The fragment model (image-independent; image A's Seg/F16.v and image B's Seg/F15.v) ===== *)

Lemma ba_nth_err_firstn : forall (n i : nat) (l : list byte), (i < n)%nat ->
  nth_error (firstn n l) i = nth_error l i.
Proof.
  induction n as [|n IH]; intros [|i] [|a l] H; cbn; try lia; try reflexivity.
  apply IH. lia.
Qed.
Lemma ba_firstn : forall m a bs n, bytes_at rsegs m a bs -> bytes_at rsegs m a (firstn n bs).
Proof.
  intros m a bs n (H0 & H1 & H2). split; [exact H0|].
  split; [rewrite length_firstn; lia|].
  intros i Hi. rewrite length_firstn in Hi. rewrite ba_nth_err_firstn by lia. apply H2. lia.
Qed.
(* The bytes from offset k of a carried byte range. *)
Lemma ba_skipn : forall m a bs (k : nat), (k <= length bs)%nat ->
  bytes_at rsegs m a bs -> bytes_at rsegs m (a + Z.of_nat k) (skipn k bs).
Proof.
  intros m a bs k Hk HB. rewrite <- (firstn_skipn k bs) in HB.
  apply LMem.bytes_at_app in HB. destruct HB as (_ & HB).
  rewrite length_firstn, Nat.min_l in HB by exact Hk. exact HB.
Qed.
(* One byte of a carried byte range, as a b8 cell with value bat. *)
Lemma ba_b8 : forall m a bs i, bytes_at rsegs m a bs -> 0 <= i -> (Z.to_nat i < length bs)%nat ->
  b8 m (a + i) (bat bs i).
Proof.
  intros m a bs i (H0 & H1 & H2) Hi0 Hi.
  unfold b8, LMem.bytes_at. cbn [length].
  split; [lia|]. split; [lia|].
  intros i' Hi'. destruct i' as [|i']; [|cbn in Hi'; lia]. cbn [nth_error].
  change (Z.of_nat 0) with 0%Z. rewrite Z.add_0_r.
  unfold bat. rewrite stdpp.bitvector.definitions.Z_to_bv_bv_unsigned.
  pose proof (H2 (Z.to_nat i) Hi) as HH. rewrite Z2Nat.id in HH by lia. rewrite HH.
  apply nth_error_nth'. exact Hi.
Qed.
Lemma memcmp_firstn : forall n k (l r : list byte), (n <= k)%nat ->
  SF.memcmp_model (firstn k l) (firstn k r) n = SF.memcmp_model l r n.
Proof.
  induction n as [|n IH]; intros k l r H; cbn [SF.memcmp_model]; [reflexivity|].
  destruct k as [|k]; [lia|].
  destruct l as [|a l]; destruct r as [|b r]; cbn [firstn SF.memcmp_model]; try reflexivity.
  destruct (bv_unsigned a =? bv_unsigned b); [apply IH; lia | reflexivity].
Qed.

Lemma bat_nonneg : forall bs i, 0 <= bat bs i.
Proof. intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))). lia. Qed.
Lemma bat_lt : forall bs i, bat bs i < 256.
Proof.
  intros bs i. unfold bat. pose proof (bv_unsigned_in_range 8 (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
  unfold bv_modulus in *. cbn in *. lia.
Qed.

Lemma ret1_close : forall c, fg_ret c = 1 -> c = FgClose.
Proof. intros c H. destruct c; cbn [fg_ret] in H; try discriminate; reflexivity. Qed.
Lemma trf1_cls : forall inp j, t_rf inp j = 1 ->
  fcls (t_len inp j) (t_FG inp j) (t_g inp j) = FgClose.
Proof. intros inp j H. unfold t_rf, fg_rf in H. apply ret1_close. exact H. Qed.
Lemma cls_close_inv : forall len st g,
  fcls len st g = FgClose -> fg_fr len g = true /\ fg_keep st g = true /\ fg_close st g = true /\ bat g 19 <> 1.
Proof.
  intros len st g H. unfold fcls, fg_class in H.
  destruct (negb (fg_fr len g)) eqn:Efr; [cbn in H; discriminate|].
  destruct (bat g 19 =? 1) eqn:E19; [cbn in H; discriminate|].
  destruct (negb (fg_keep st g)) eqn:Ek; [cbn in H; discriminate|].
  destruct (negb (fg_close st g)) eqn:Ec; [cbn in H; discriminate|].
  apply Bool.negb_false_iff in Efr, Ek, Ec. apply Z.eqb_neq in E19. repeat split; try assumption.
Qed.
Lemma tFGf_close : forall inp j, t_rf inp j = 1 ->
  t_FGf inp j = fg_clear (fg_join (t_FG inp j) (t_g inp j)).
Proof. intros inp j H. unfold t_FGf, fg_st. rewrite (trf1_cls inp j H). reflexivity. Qed.
Lemma frT14 : forall st g, fg_close st g = true -> 14 <= fg_T st g.
Proof. intros st g H. unfold fg_close in H. rewrite !andb_true_iff in H. apply Z.leb_le. tauto. Qed.
Lemma closeT64 : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof. intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H. apply Z.leb_le. tauto. Qed.
Lemma keep_hf : forall st g, fg_keep st g = true -> fg_hf st <> 0.
Proof.
  intros st g H. unfold fg_keep in H. rewrite !andb_true_iff in H. destruct H as ((H & _) & _).
  apply Bool.negb_true_iff, Z.eqb_neq in H. exact H.
Qed.
Lemma fr_n : forall len g, fg_fr len g = true -> 1 <= fg_n g <= 22.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (((((((((((_ & _) & _) & _) & _) & _) & _) & _) & _) & Hlo) & Hhi) & _).
  apply Z.leb_le in Hlo, Hhi. lia.
Qed.
Lemma fr_len50 : forall len g, fg_fr len g = true -> 50 <= len.
Proof.
  intros len g H. unfold fg_fr in H. rewrite !andb_true_iff in H.
  destruct H as (((((((((((H & _) & _) & _) & _) & _) & _) & _) & _) & _) & _) & _).
  apply Z.leb_le in H. lia.
Qed.

Lemma t_g_length : forall inp j, length (t_g inp j) = 50%nat.
Proof. intros inp j. unfold t_g. apply fr50_length. Qed.
Lemma keep_T : forall st g, fg_keep st g = true -> fg_T st g <= 64.
Proof. exact closeT64. Qed.
Lemma rf_first_length : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  length (fg_first st g) = 72%nat.
Proof.
  intros st g HL HG Hn. unfold fg_first, fg_body.
  rewrite !length_app, length_skipn, (rf_bsl_length g 6 6), (rf_bsl_length g 27 (fg_n g)) by lia.
  cbn [length]. lia.
Qed.
Lemma fg_next_length : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat ->
  length (fg_next st g (fg_class f fr pa pp pn len st g)) = 72%nat.
Proof.
  intros f fr pa pp pn len st g HL HG. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact HL|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact HL].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply rf_first_length; [exact HL | exact HG | apply (fr_n len); exact FR].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply rf_clear_length; exact HL].
    destruct (fg_close st g); cbn [negb fg_next]; apply rf_clear_length, rf_fg_join_length;
      solve [exact HL | exact HG | apply (fr_n len); exact FR | apply keep_T; exact KEEP].
Qed.
Lemma t_FG_length : forall inp j, length (t_FG inp j) = 72%nat.
Proof.
  intros inp j. induction j as [|j IH].
  - reflexivity.
  - unfold t_FG in *. rewrite fst_at_S. unfold turn.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_fg]; unfold fg_st, fcls;
      apply (fg_next_length 1 1 1 1 1); solve [exact IH | apply t_g_length].
Qed.
Lemma t_FGf_length : forall inp j, length (t_FGf inp j) = 72%nat.
Proof.
  intros inp j. unfold t_FGf, fg_st, fcls.
  apply (fg_next_length 1 1 1 1 1); [apply t_FG_length | apply t_g_length].
Qed.

(* self-contained nth helpers *)
Lemma nthfn : forall (i n : nat) (l : list byte), (i < n)%nat ->
  nth i (firstn n l) (Z_to_bv 8 0) = nth i l (Z_to_bv 8 0).
Proof.
  intros i n l. revert i l. induction n as [|n IH]; intros i l Hi; [lia|].
  destruct l as [|a l]; cbn [firstn]; [destruct i; reflexivity|].
  destruct i as [|i]; cbn [nth]; [reflexivity|]. apply IH. lia.
Qed.
Lemma nth_sk : forall (m i : nat) (l : list byte), nth i (skipn m l) (Z_to_bv 8 0) = nth (m + i) l (Z_to_bv 8 0).
Proof.
  induction m as [|m IH]; intros i l.
  - reflexivity.
  - destruct l as [|a l].
    + cbn [skipn]. rewrite !nth_overflow by (cbn; lia). reflexivity.
    + cbn [skipn plus nth]. apply IH.
Qed.
Lemma nth_clear_hi : forall (j : nat) (st : list byte), (7 <= j)%nat -> (6 <= length st)%nat ->
  nth j (fg_clear st) (Z_to_bv 8 0) = nth j st (Z_to_bv 8 0).
Proof.
  intros j st Hj HL. unfold fg_clear.
  rewrite app_nth2; rewrite length_firstn; [|rewrite Nat.min_l by lia; lia].
  rewrite Nat.min_l by lia.
  rewrite app_nth2; cbn [length]; [|lia].
  rewrite nth_sk. f_equal. lia.
Qed.
Lemma bat_clear_hi : forall st i, 7 <= i -> (6 <= length st)%nat -> bat (fg_clear st) i = bat st i.
Proof. intros st i Hi HL. unfold bat. f_equal. apply nth_clear_hi; [lia | exact HL]. Qed.
(* skipn 15 commutes with fg_clear *)
Lemma skipn15_clear : forall st : list byte, (6 <= length st)%nat ->
  skipn 15 (fg_clear st) = skipn 15 st.
Proof.
  intros st HL. apply nth_ext with (d := Z_to_bv 8 0) (d' := Z_to_bv 8 0).
  - rewrite !length_skipn. unfold fg_clear. rewrite !length_app, length_firstn, length_skipn. cbn [length].
    rewrite Nat.min_l by lia. lia.
  - intros i Hi. rewrite length_skipn in Hi. rewrite !nth_sk. apply nth_clear_hi; lia.
Qed.
Lemma bat_join_lo : forall st g i, 0 <= i -> i < 8 + fg_lf st -> (Z.to_nat i < length st)%nat ->
  bat (fg_join st g) i = bat st i.
Proof.
  intros st g i H0 Hlf HL. unfold bat, fg_join.
  assert (Hlen : (Z.to_nat i < length (firstn (Z.to_nat (8 + fg_lf st)) st))%nat).
  { rewrite length_firstn. apply Nat.min_glb_lt; [|exact HL]. apply Z2Nat.inj_lt; lia. }
  rewrite app_nth1 by exact Hlen. rewrite nthfn; [reflexivity| apply Z2Nat.inj_lt; lia].
Qed.
(* The joined record's bytes past the FIRST part are the LAST frame's body bytes from frame byte 27 (as
   Seg/F13.v's copy). *)
Lemma bat_join_mid : forall st g i, 8 + fg_lf st <= i -> i < 8 + fg_T st g ->
  0 <= fg_lf st -> (Z.to_nat (8 + fg_lf st) <= length st)%nat -> 27 + fg_n g <= Z.of_nat (length g) ->
  bat (fg_join st g) i = bat g (27 + (i - 8 - fg_lf st)).
Proof.
  intros st g i H1 H2 H0 HL HG. unfold fg_T in H2. unfold bat, fg_join, fg_body, bsl. f_equal.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn, Nat.min_l by exact HL.
  rewrite app_nth1 by (rewrite length_firstn, length_skipn; lia).
  rewrite nthfn by lia. rewrite nth_sk. f_equal. lia.
Qed.
(* A byte of a slice firstn n (skipn k l) is the list's byte k + i. *)
Lemma bat_firstn_skipn : forall (l : list byte) n (k : nat) i, 0 <= i -> i < n ->
  bat (firstn (Z.to_nat n) (skipn k l)) i = bat l (Z.of_nat k + i).
Proof. intros l n k i H0 H1. unfold bat. f_equal. rewrite nthfn by lia. rewrite nth_sk. f_equal. lia. Qed.
(* On a closing turn the record's address bytes 17 / 18 are joined_byte 9 / 10 of the FIRST state FI names. *)
Lemma joined_close : forall st g s, length st = 72%nat -> length g = 50%nat -> frag_ok st -> FI st s ->
  bat st 6 = 1 -> 1 <= fg_n g <= 22 -> 14 <= fg_T st g ->
  bat (fg_join st g) 17 = joined_byte s g 9 /\ bat (fg_join st g) 18 = joined_byte s g 10.
Proof.
  intros st g s HL HG (_ & Hok) HFI H6 Hn HT.
  destruct (HFI H6) as (_ & En & Eb). pose proof (Hok H6) as Hlf.
  assert (K : forall i, 9 <= i <= 10 -> bat (fg_join st g) (8 + i) = joined_byte s g i).
  { intros i Hi. unfold joined_byte. rewrite En, Eb.
    destruct (Z.ltb_spec i (bat st 7)) as [Hlt|Hge].
    - rewrite bat_join_lo by (unfold fg_lf; rewrite ?HL; lia).
      rewrite (bat_firstn_skipn st (bat st 7) 8 i) by lia. reflexivity.
    - rewrite bat_join_mid by (unfold fg_T, fg_lf in *; rewrite ?HL, ?HG; lia).
      unfold fg_lf. f_equal. lia. }
  split; [exact (K 9 ltac:(lia)) | exact (K 10 ltac:(lia))].
Qed.

(* The byte joined_byte reads (JBC.jb_addr) at the calls 0x82414 / 0x82438: first.body[i] (inside the 40 usable
   bytes of `first`) when i < n, else the record buffer byte Phi + 27 + i - n (inside Phi's 50 addressable bytes). *)
Lemma f16_jb_addr : forall m fr phi n i,
  (i = 9 \/ i = 10) -> 0 <= n < 256 ->
  addressable m (fr + 2880) 40 -> addressable m phi 50 ->
  addressable m (JBC.jb_addr (fr + 2880) (phi + 18) n i) 1 /\
  ((fr + 2880 <= JBC.jb_addr (fr + 2880) (phi + 18) n i < fr + 2920) \/
   (phi <= JBC.jb_addr (fr + 2880) (phi + 18) n i < phi + 50)).
Proof.
  intros m fr phi n i Hi Hn Hf Hp. unfold JBC.jb_addr.
  destruct (Z.ltb_spec i n) as [E|E].
  - replace (fr + 2880 + 5 + i) with (fr + 2880 + (5 + i)) by lia.
    split; [apply (addressable_sub m (fr + 2880) 40 (5 + i) 1 Hf); lia | left; lia].
  - replace (phi + 18 + (9 + i - n)) with (phi + (27 + i - n)) by lia.
    split; [apply (addressable_sub m phi 50 (27 + i - n) 1 Hp); lia | right; lia].
Qed.

(* psum helpers and the record sum *)
Lemma psum_bound : forall bs n, psum bs n <= 256 * Z.of_nat n.
Proof.
  intros bs n. induction n as [|n IH]; cbn [psum]; [lia|].
  pose proof (bv_unsigned_in_range 8 (nth n bs (Z_to_bv 8 0))) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.
Lemma psum_ext : forall l1 l2 n, (forall i, (i < n)%nat -> nth i l1 (Z_to_bv 8 0) = nth i l2 (Z_to_bv 8 0)) ->
  psum l1 n = psum l2 n.
Proof.
  intros l1 l2 n. induction n as [|n IH]; intros H; cbn [psum]; [reflexivity|].
  rewrite (IH (fun i Hi => H i (ltac:(lia)))). rewrite (H n ltac:(lia)). reflexivity.
Qed.
Lemma close_recsum : forall st g, fg_close st g = true ->
  recsum (bsl (fg_join st g) 15 (fg_T st g - 8)) = 0.
Proof.
  intros st g H. unfold fg_close in H. rewrite !andb_true_iff in H.
  destruct H as (_ & Hz). apply Z.eqb_eq. exact Hz.
Qed.
(* The record_sum_closes argument: the pll + 5 = fg_T - 8 bytes of the closed record from offset 15 sum to 0
   mod 128 (fg_close's recsum conjunct; fg_clear only touches byte 6). *)
Lemma sum_closes : forall inp j, t_rf inp j = 1 ->
  recsum (firstn (Z.to_nat (fg_T (t_FG inp j) (t_g inp j) - 8)) (skipn 15 (t_FGf inp j))) = 0.
Proof.
  intros inp j Hrf.
  pose proof (trf1_cls inp j Hrf) as Hcls.
  destruct (cls_close_inv _ _ _ Hcls) as (Hfr & Hkeep & Hclose & _).
  pose proof (t_FG_length inp j) as HLst. pose proof (t_g_length inp j) as HLg.
  pose proof (fr_n _ _ Hfr) as Hn. pose proof (closeT64 _ _ Hkeep) as HT64.
  pose proof (rf_fg_join_length _ _ HLst HLg Hn HT64) as HLX.
  rewrite (tFGf_close inp j Hrf). rewrite skipn15_clear by (rewrite HLX; lia).
  pose proof (close_recsum _ _ Hclose) as Hrec. unfold bsl in Hrec.
  change (Z.to_nat 15) with 15%nat in Hrec. exact Hrec.
Qed.

(* The two bytes of a 16-bit value. *)
Lemma f16_split16 : forall v, 0 <= v < 65536 ->
  v mod 256 + 256 * (v / 256) = v /\ 0 <= v mod 256 < 256 /\ 0 <= v / 256 < 256.
Proof.
  intros v Hv. pose proof (Z.div_mod v 256 ltac:(lia)). pose proof (Z.mod_pos_bound v 256 ltac:(lia)).
  split; [lia|]. split; [lia|].
  split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia].
Qed.

(* The high and low byte of 256 * hi + lo. *)
Lemma f16_hi_lo : forall hi lo, 0 <= hi < 256 -> 0 <= lo < 256 ->
  (256 * hi + lo) / 256 = hi /\ (256 * hi + lo) mod 256 = lo.
Proof.
  intros hi lo Hhi Hlo. split.
  - rewrite Z.mul_comm, Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
  - rewrite Z.mul_comm, Z.add_comm, Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

(* The first-fragment record's four fields are bytes (fs0 is zero; a turn copies record bytes). *)
Lemma fst_bounds : forall inp j,
  (fs_have (fst_at inp j) = 0 \/ fs_have (fst_at inp j) = 1) /\ 0 <= fs_n (fst_at inp j) < 256.
Proof.
  intros inp j. induction j as [|j IH].
  - cbn [fst_at]. unfold fs0. cbn [fs_have fs_n]. lia.
  - rewrite fst_at_S. unfold turn. cbv zeta.
    destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_have fs_n].
    + pose proof (bat_nonneg (t_g inp j) 26). pose proof (bat_lt (t_g inp j) 26). lia.
    + exact IH.
Qed.
(* The body of the first-fragment state is its n bytes (an opening frame has 1 <= n <= 22, fg_fr) and at most 23
   bytes long (frame bytes 27 .. 50). *)
Lemma fst_body_n : forall inp j, Z.of_nat (length (fs_body (fst_at inp j))) = fs_n (fst_at inp j).
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)) eqn:EO; cbn [fs_body fs_n]; [|exact IH].
  unfold f_opens in EO. apply andb_prop in EO as [EO _].
  pose proof (fr_n _ _ EO) as Hn. unfold fg_n in Hn.
  rewrite length_firstn, length_skipn, t_g_length. lia.
Qed.
Lemma fst_body_len : forall inp j, (length (fs_body (fst_at inp j)) <= 23)%nat.
Proof.
  intros inp j. induction j as [|j IH]; [cbn; lia|].
  rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_body]; [|exact IH].
  rewrite length_firstn, length_skipn, t_g_length. lia.
Qed.

(* ---- The turn's records as the model keeps them, for the exit cut's RECS bundle. ---- *)

(* Two byte lists read at the same address with the same length are the same list. *)
Lemma ba_det : forall m a bs cs, bytes_at rsegs m a bs -> bytes_at rsegs m a cs ->
  length bs = length cs -> bs = cs.
Proof.
  intros m a bs cs (_ & _ & Hb) (_ & _ & Hc) HL.
  apply nth_error_ext. intros i.
  destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
  - rewrite <- (Hb i Hi), <- (Hc i ltac:(lia)). reflexivity.
  - rewrite (proj2 (nth_error_None bs i) Hi), (proj2 (nth_error_None cs i) ltac:(lia)). reflexivity.
Qed.

(* The fragment record after the call is turn j + 1's record (fs_fg of the next state). *)
Lemma t_FG_S : forall inp j, t_FG inp (S j) = t_FGf inp j.
Proof.
  intros inp j. unfold t_FG, t_FGf. rewrite fst_at_S. unfold turn. cbv zeta.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.
(* On the arm that closes a record the identity record after the ingest is turn j + 1's. *)
Lemma t_ID_S_rf : forall inp j, t_rf inp j = 1 ->
  t_ID inp (S j) = snd (RcIdentModel.ING (t_IDr inp j) (fg_addr (t_FG inp j) (t_g inp j))
                          (f_pl (t_len inp j) (t_FG inp j) (t_g inp j))).
Proof.
  intros inp j H. unfold t_rf, t_FG in H. unfold t_ID, t_IDr, t_FG.
  rewrite fst_at_S. unfold turn, fg_id. cbv zeta. rewrite H, Z.eqb_refl.
  destruct (f_opens (t_len inp j) (t_g inp j)); reflexivity.
Qed.
(* The identity record keeps its 38 bytes through the two ingests of the turn. *)
Lemma t_ID_length : forall inp j, length (t_ID inp j) = 38%nat.
Proof.
  intros inp j. induction j as [|j IH]; [reflexivity|].
  unfold t_ID in *. rewrite fst_at_S. unfold turn. cbv zeta.
  assert (Hr : length (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) = 38%nat).
  { unfold rp_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply RcIdentModel.ING_length; exact IH | exact IH]. }
  assert (Hf : length (fg_id (rp_id (fs_id (fst_at inp j)) (t_len inp j) (t_g inp j)) (t_len inp j)
                         (fs_fg (fst_at inp j)) (t_g inp j)) = 38%nat).
  { unfold fg_id. match goal with |- context [if ?c then _ else _] => destruct c end;
      [apply RcIdentModel.ING_length; exact Hr | exact Hr]. }
  destruct (f_opens (t_len inp j) (t_g inp j)); cbn [fs_id]; exact Hf.
Qed.
Lemma t_IDr_length : forall inp j, length (t_IDr inp j) = 38%nat.
Proof.
  intros inp j. unfold t_IDr, rp_id.
  match goal with |- context [if ?c then _ else _] => destruct c end;
    [apply RcIdentModel.ING_length; apply t_ID_length | apply t_ID_length].
Qed.

(* frag_ok (the record's flag byte and its body length) holds of every turn's record: the zero record has flag 0,
   and each class keeps it - FgFirst writes flag 1 with the body length 1 .. 22 (fg_fr), the other writing
   classes clear the flag. *)
Lemma bat_clear6 : forall x, (6 <= length x)%nat -> bat (fg_clear x) 6 = 0.
Proof.
  intros x Hx. unfold bat, fg_clear. change (Z.to_nat 6) with 6%nat.
  rewrite app_nth2 by (rewrite length_firstn; lia).
  rewrite length_firstn. replace (6 - Init.Nat.min 6 (length x))%nat with 0%nat by lia.
  cbn [app nth]. reflexivity.
Qed.
Lemma fok_clear : forall x, (6 <= length x)%nat -> frag_ok (fg_clear x).
Proof.
  intros x Hx. split; [left; apply bat_clear6; exact Hx|].
  rewrite (bat_clear6 x Hx). intros H. discriminate H.
Qed.
Lemma fok_first : forall st g, length st = 72%nat -> length g = 50%nat -> 1 <= fg_n g <= 22 ->
  frag_ok (fg_first st g).
Proof.
  intros st g HL HG Hn.
  assert (HB : length (bsl g 6 6) = 6%nat) by (rewrite (rf_bsl_length g 6 6) by lia; reflexivity).
  assert (E6 : bat (fg_first st g) 6 = 1).
  { unfold bat, fg_first. change (Z.to_nat 6) with 6%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (6 - 6)%nat with 0%nat by lia. cbn [app nth]. reflexivity. }
  assert (E7 : bat (fg_first st g) 7 = fg_n g).
  { unfold bat, fg_first, fg_n. change (Z.to_nat 7) with 7%nat.
    rewrite app_nth2 by lia. rewrite HB.
    replace (7 - 6)%nat with 1%nat by lia. cbn [app nth]. change (Z.to_nat 26) with 26%nat. reflexivity. }
  split; [right; exact E6|]. rewrite E7. intros _. exact Hn.
Qed.
Lemma fok_next : forall f fr pa pp pn len st g, length st = 72%nat -> length g = 50%nat -> frag_ok st ->
  frag_ok (fg_next st g (fg_class f fr pa pp pn len st g)).
Proof.
  intros f fr pa pp pn len st g HL HG Hok. unfold fg_class.
  destruct ((f =? 0) || (fr =? 0) || (pa =? 0) || (pp =? 0) || (pn =? 0)); [cbn [fg_next]; exact Hok|].
  destruct (fg_fr len g) eqn:FR; cbn [negb]; [|cbn [fg_next]; exact Hok].
  destruct (bat g 19 =? 1).
  - cbn [fg_next]. apply fok_first; [exact HL | exact HG | exact (fr_n len g FR)].
  - destruct (fg_keep st g) eqn:KEEP; cbn [negb]; [|cbn [fg_next]; apply fok_clear; lia].
    destruct (fg_close st g); cbn [negb fg_next]; apply fok_clear;
      rewrite (rf_fg_join_length st g HL HG (fr_n len g FR) (keep_T st g KEEP)); lia.
Qed.
Lemma fok_FG : forall inp j, frag_ok (t_FG inp j).
Proof.
  intros inp j. induction j as [|j IH].
  - assert (E : bat (t_FG inp 0) 6 = 0) by reflexivity.
    split; [left; exact E|]. rewrite E. intros H. discriminate H.
  - rewrite t_FG_S. unfold t_FGf, fg_st, fcls.
    apply (fok_next 1 1 1 1 1); [apply t_FG_length | apply t_g_length | exact IH].
Qed.

Section F16.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, AC.AsanAllocAPI AC.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
(* The callee contracts: record_sum_closes (0x83614), joined_byte (0x836ac, a Theorem Labs lane's contract; the assembly
   discharges it with joined_byte.v's joined_byte_holds) and reac_identity_ingest (0x87e0c). *)
Hypothesis HRSC : RSC.record_sum_closes_contract.
Hypothesis HJB : JBC.joined_byte_contract.
Hypothesis HING : IGC.reac_identity_ingest_contract.

(* The allocator laws are read once per law in this file, in the three lemmas below (a Theorem Labs lane 15:32Z); every other
   site reads these lemmas. The block law goes through SlotInv's named fields (lw_blocks, lwb_end,
   lwb_byte_not_fs). *)
Lemma f16_blk : forall H mem md p n,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> In (p, n) H ->
  p + n <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, p <= a < p + n -> ~ AC.a_in_fs AC.ASYMS mem a).
Proof.
  intros H mem md p n HAH Hin.
  pose proof (lw_blocks (APIf rc) H mem md p n HAH Hin) as HB.
  split; [exact (lwb_end _ _ _ _ _ _ HB) | exact (lwb_byte_not_fs (APIf rc) H mem md p n HB)].
Qed.
Lemma f16_store : forall H mem mem' md,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ AC.a_store_ok H (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) a ->
     mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md /\
  (forall a, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem' md a <->
             AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) H mem md a) /\
  AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md = AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md.
Proof.
  intros H mem mem' md HAH Hmc Hw.
  destruct (AC.a_laws_store _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem mem' md HAH Hmc Hw)
    as (H1 & H2 & H3 & H4).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3 | exact H4].
Qed.
Lemma f16_fs_place : forall H mem md b,
  AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) H mem md -> word_mem rsegs mem (AC.as_tp AC.ASYMS) b ->
  0 <= b < 2 ^ 64 ->
  AC.GT <= b /\ b + AC.FS_SIZE <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
  (forall a, b <= a < b + AC.FS_SIZE -> app_mem a).
Proof.
  intros H mem md b HAH Hw Hb.
  destruct (AC.a_laws_fs_place _ _ _ _ _ (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) H mem md b HAH Hw Hb)
    as (H1 & H2 & _ & H4).
  split; [exact H1|]. split; [exact H2 | exact H4].
Qed.

(* The run lemma over the Lib engine of this file (as Seg/F13.v's sl_run_lib): an evt from the real config at pc
   that ends at some pc' with the register/memory predicate K lifts to SR Post through the lazy-model lemma
   AsanLift.evt_SR_canon_lazy; the end model md' is a materialization of md. *)
Lemma f16_run_lib : forall regs pc mem md
  (K : bvmap 5 word -> word -> (word -> option byte) -> Prop) (P : config -> Prop),
  m_halted md = None ->
  evt rsegs
    (fun ms => exists R pc' mem', ms = LMS.MS R fp_regs pc' fp_csr None mem' (seg_rom rsegs) /\ K R pc' mem')
    (LMS.MS (Regs6ss.mkR_of regs) fp_regs pc fp_csr None mem (seg_rom rsegs)) ->
  (forall R pc' mem' regs' md', K R pc' mem' -> (forall r, getr regs' r = getr R r) -> AsanLift.mat_le md md' ->
     SR rsegs (mkCfg (mkst regs' pc' mem' (seg_rom rsegs)) md') P) ->
  SR rsegs (mkCfg (mkst regs pc mem (seg_rom rsegs)) md) P.
Proof.
  intros regs pc mem md K P Hh HE HK.
  eapply (AsanLift.evt_SR_canon_lazy rsegs (mkst regs pc mem (seg_rom rsegs)) _ md P); [exact HE | exact Hh |].
  intros ms' md' (can & (R & pc' & mem' & -> & HKR) & Heq) Hmat.
  destruct Heq as (HR & HF' & Hpc & Hsvc & Hres & Hfc & Hm & Hrom).
  destruct ms' as [regs' fr' pcv' svc' rv' fc' m' ro'].
  cbn in HR, HF', Hpc, Hsvc, Hres, Hfc, Hm, Hrom. subst.
  apply (HK R _ _ regs' md' HKR); [apply kb_getr_eqv; exact HR | exact Hmat].
Qed.

(* FRA and ENT across the segment's two calls: they write only W = [sp - 32, sp) (the two callees' stack bytes;
   the ingest frame is the larger) and the 38 identity bytes [fr + 2688, fr + 2726) inside the frame body. The
   stack part is a_store_ok on both arms; the identity part is a_store_ok on the real arm (the frame is in
   [stklo, APPMEM_END)) and inside the side stack on the side arm (Tac_fs.a_fs_ok_store_AH); that per-arm
   analysis gives AH, the stack bounds and the owned set after the run. The entry-anchored slot window of mem'
   is the callee's post window below sp joined with FRA's window above it, the identity bytes being present by
   the ingest post. Then Tac_slot.sl_fr_cl rebuilds FRA (W misses the low image, the frame header, the two
   spill pairs, the saved registers and the frame's 392 shadow bytes), sl_fra_move moves it to regs' / md', and
   ent_store / ent_mat move ENT. *)
Lemma f16_fra : forall g fr hb regs regs' mem mem' md md' A,
  FRA B APIf ra g fr hb regs mem md -> ENT APIf g hb mem md ->
  rg regs 9 A -> 0 <= A < 2 ^ 64 ->
  LFr.munch [(AC.aspZ regs - 32, AC.aspZ regs); (fr + 2688, fr + 2688 + 38)] mem mem' ->
  LFr.wmono rsegs mem mem' -> ro_agree rsegs mem' ->
  LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs) ->
  (forall q, fr + 2688 <= q < fr + 2688 + 38 -> exists b, LMem.mrd rsegs mem' (LMem.wa q) = Some b) ->
  getr regs' 2 = getr regs 2 -> getr regs' 3 = getr regs 3 -> getr regs' 4 = getr regs 4 ->
  getr regs' 8 = getr regs 8 -> getr regs' 9 = getr regs 9 -> getr regs' 19 = getr regs 19 ->
  getr regs' 26 = getr regs 26 ->
  AsanLift.mat_le md md' ->
  FRA B APIf ra g fr hb regs' mem' md' /\ ENT APIf g hb mem' md'.
Proof.
  intros g fr hb regs regs' mem mem' md md' A HFRA HENT Hs1 HAb
    MU WM HroM HSTKW HPRES E2 E3 E4 E8 E9 E19 E26 Hmat.
  destruct (fra_app B APIf ra g fr hb regs mem md HFRA) as (HGTfr & Hfrapp).
  pose proof (fra_frame B APIf ra g fr hb regs mem md HFRA) as (Hfrw & _ & _ & _).
  unfold FRAME_BYTES in Hfrapp, Hfrw.
  assert (Hdisjfr : fr + 3136 <= AC.aspZ regs - 32 \/ AC.aspZ regs <= fr)
    by (apply Hfrw; unfold FN_STACK, AF.SLOT_STACK; lia).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspill & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  rewrite ?FRAME_SHADOW_val in *. unfold FRAME_BYTES in *.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb ++ g_H g) mem md HAH) as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  pose proof Hwin as HwinB. destruct HwinB as (Hw0 & Hw1 & _).
  assert (EA : A2 = A).
  { apply f16_bv_inj; [lia | lia |]. unfold rg in *. rewrite <- Hr9. exact Hs1. }
  subst A2.
  rewrite Haspz in Hdisjfr, MU, HSTKW.
  assert (Hfrhi : fr + 3136 <= APPMEM_END).
  { pose proof (Hfrapp (fr + 3135) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  set (W := [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  assert (HOW : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                  LFr.outside W x) by (intros x H1 H2; subst W; apply f16_out2; assumption).
  assert (Hallapp : all_app W).
  { subst W. cbn [all_app]. split; [|split; [|exact I]].
    - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
    - intros a Ha. apply Hfrapp. lia. }
  assert (HGTW : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { subst W. intros lo hi Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold AC.GT in *; lia. }
  assert (Hrtdj : AsanRTInv.rt_disjoint W) by exact (f16_rtdj_GT W HGTW).
  assert (Hwr : forall q, 0 <= q < 2 ^ 64 -> writable_at rsegs mem q -> writable_at rsegs mem' q)
    by (intros q _ Hq; exact (WM (Z_to_bv 64 q) Hq)).
  assert (HAHS : AC.aa_AH AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md /\
                 (forall q, AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem' md q <->
                            AC.aa_owned AC.ASYMS AsanRTInv.RT (APIf rc) (hb ++ g_H g) mem md q) /\
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md /\
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem' md =
                 AC.aa_stkhi AC.ASYMS AsanRTInv.RT (APIf rc) mem md).
  { destruct Hloc as [[Hs50 [Hspfr Hreal]] | [Hs5fr [Hfsb [Hfs _]]]].
    - assert (Hmc : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hnok.
        destruct (f16_out_dec W q) as [Ho|Hno].
        - apply MU. rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - exfalso. apply Hnok. subst W. apply f16_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + right; left. unfold AF.SLOT_STACK in *. split; lia.
          + right; left. apply Hreal. lia. }
      destruct (f16_store (hb ++ g_H g) mem mem' md HAH Hmc Hwr)
        as (HAH' & Hown' & HSTKeq & HSTKHIeq).
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq].
    - destruct (Hfs (fr + 3135) ltac:(lia)) as (FS & HFSr & HwFS & HFSlo & HFShi).
      pose proof (Hfsb FS HwFS HFSr) as HFSfr.
      destruct (f16_fs_place (hb ++ g_H g) mem md FS HAH HwFS HFSr)
        as (HGTFS & HFSend & HFSapp).
      assert (HFS64 : FS + AC.FS_SIZE <= 2 ^ 64).
      { pose proof (HFSapp (FS + AC.FS_SIZE - 1) ltac:(unfold AC.FS_SIZE; lia)) as H.
        unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
      assert (Hpres : forall q, 0 <= q < 2 ^ 64 -> (exists b, mbyte rsegs mem q = Some b) ->
                exists b, mbyte rsegs mem' q = Some b).
      { intros q Hq (b & Hb).
        destruct (f16_out_dec W q) as [Ho|Hno].
        - exists b. unfold mbyte in *. rewrite (MU (Z_to_bv 64 q)); [exact Hb|].
          rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - subst W. apply f16_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + destruct HSTKW as (_ & _ & Hs). destruct (Hs q ltac:(unfold FN_STACK, AF.SLOT_STACK in *; lia))
              as (_ & bb & Hbb). exists bb. exact Hbb.
          + destruct (HPRES q ltac:(lia)) as (bb & Hbb). exists bb. exact Hbb. }
      assert (Hmeta : forall q, Tac_fs.fs_meta FS q -> LFr.outside W q).
      { intros q Hq. pose proof (Tac_fs.fs_meta_below FS q Hq) as Hqb.
        apply HOW; unfold AF.SLOT_STACK in *; lia. }
      assert (Hagree : forall q, 0 <= q < 2 ^ 64 ->
                ~ AC.a_store_ok (hb ++ g_H g) (AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) q ->
                ~ (FS <= q < FS + AC.FS_SIZE) ->
                ~ (exists b, FS <= b < FS + AC.FS_SIZE /\ q = shadow_addr b) ->
                mem' (Z_to_bv 64 q) = mem (Z_to_bv 64 q)).
      { intros q Hq Hnok Hnfs Hnsh.
        destruct (f16_out_dec W q) as [Ho|Hno].
        - apply MU. rewrite LMS.unsigned_lit by exact Hq. exact Ho.
        - exfalso. subst W. apply f16_not_out2 in Hno. destruct Hno as [Hx|Hx].
          + apply Hnok. right; left. unfold AF.SLOT_STACK in *. split; lia.
          + apply Hnfs. lia. }
      destruct (Tac_fs.a_fs_ok_store_AH AC.ASYMS _ _ _ _ W (hb ++ g_H g) mem mem' md FS
                  LAWS HAH HwFS HFSr HFS64 MU Hwr Hpres Hmeta Hagree)
        as (HAH' & Hown' & HSTKeq & HSTKHIeq).
      split; [exact HAH'|]. split; [exact Hown'|]. split; [exact HSTKeq | exact HSTKHIeq]. }
  destruct HAHS as (HAHm & Hownm & HSTK & HSTKHI).
  assert (HSTKS : LFr.stk rsegs mem' (g_S g - AF.SLOT_STACK) (g_S g)).
  { apply (f16_stk_tr W mem mem' _ _ Hwin MU WM).
    intros x Hx.
    destruct (f16_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
    right. subst W. apply f16_not_out2 in Hno. destruct Hno as [Hr|Hr].
    - destruct HSTKW as (_ & _ & Hs). destruct (Hs x ltac:(unfold FN_STACK, AF.SLOT_STACK in *; lia))
        as (_ & bb & Hbb). exists bb. exact Hbb.
    - exact (HPRES x ltac:(lia)). }
  assert (HspA : forall A', getr regs 9 = Z_to_bv 64 A' -> 0 <= A' < 2 ^ 64 -> A' = A).
  { intros A' HA' HA'b. apply f16_bv_inj; [exact HA'b | exact HAb |].
    rewrite <- HA'. exact Hs1. }
  assert (HFRAm : FRA B APIf ra g fr hb regs mem' md).
  { apply (sl_fr_cl B APIf ra empty FF g fr hb regs regs mem mem' md W HFRA MU WM HroM Hallapp Hrtdj
             HAHm HSTK); try reflexivity.
    - intros x Hx. apply HOW; lia.
    - intros x Hx. apply HOW; lia.
    - intros A' HA' HA'b x Hx. rewrite (HspA A' HA' HA'b) in Hx. apply HOW; lia.
    - intros x Hx. apply HOW; lia.
    - intros x Hx. apply (f16_out_not_app W x Hallapp). intro Hap.
      exact (app_not_shadow x Hap (f16_frame_shadow fr x Hfrapp Hx)).
    - intros A' HA' HA'b x Hx. rewrite (HspA A' HA' HA'b) in Hx. apply HOW; lia.
    - (* the side-arm FakeStack record: W is at or above stklo <= S - SLOT_STACK < sp - 32 or in the frame body *)
      apply (fsrec_stklo APIf (hb ++ g_H g) mem mem' md W fr HAH MU). intros x Hx Hnf.
      unfold FRAME_BYTES in Hnf. apply HOW; lia.
    - (* the input block: below stklo and apart from the frame (fra_in_apart) *)
      intros x Hx. destruct (fra_in_apart B APIf ra g fr hb regs mem md HFRA x Hx) as (_ & Hxlo & Hxf & _).
      unfold FRAME_BYTES in Hxf. apply HOW; lia.
    - exact HSTKS. }
  split.
  - exact (sl_fra_move B APIf ra g fr hb regs regs' mem' md md' HFRAm E2 E3 E4 E8 E9 E19 E26 Hmat).
  - apply (ent_mat APIf g hb mem' md md'); [|exact Hmat].
    apply (ent_store B APIf ra g fr hb regs mem mem' md W HENT HFRA MU).
    + intros x Hx.
      destruct (f16_out_dec W x) as [Ho|Hno]; [left; exact Ho|].
      subst W. apply f16_not_out2 in Hno. destruct Hno as [Hr|Hr].
      * right; left. unfold AF.SLOT_STACK in *. lia.
      * right; right; left. unfold FRAME_BYTES. lia.
    + exact HSTK.
    + exact HSTKHI.
    + intros a Hia Ho. apply (proj2 (Hownm a)). exact Ho.
Qed.

(* ---- seg_F16 : 0x823d8 -> 0x82464 (S_F16), on the official cuts Inv_B823d8_at and Inv_B82464_at. ---- *)
Lemma seg_F16 : forall j,
  Hat B APIf ra (Inv_B82464_at B APIf ra) j -> Hat B APIf ra (Inv_B823d8_at B APIf ra) j.
Proof.
  intros j Hexit g c HInv.
  pose proof (proj1 FF) as SEGS.
  destruct HInv as (phi & regs & mem & md & fr & Ec & HFRA & HENT & Hgn & Hj & HHB & HLK & Hs4 & H224 &
    HFM & HFSj & Hs2 & H27cut & Haphi50e & (rb & Hrb & Hrbl) &
    (A & kp & Hs1 & Hkp & Hs8 & HAo & HspAo & HfrAo & Hw112 &
     (w272 & H272 & Hw272b & Hw272t & Hw272f) &
     Hphi112 & Hkp112 & HphiBC & HkpBC & Hphi2688 & Hkp2688 & H8819 & HNblk & HFSTblk & HPLLblk) &
    HFLV & Hrf & Ha1 & HbRec & HaRec & HfragOK & HU256 & (idb & HbId & LId) & Hturn & HRECF & HFS9).
  (* the record-sum argument block, the pointers of `first` / blk / the address cell, and the ingest pointers *)
  destruct HNblk as (N & bsN & HrN & Q120 & HN1 & HNfr & HbsN & HbsNl & HrecN & HadN).
  destruct HFSTblk as (HAVE & NB & AD & A0V & A1V & _ & _ & _ & _ & _ & Q168 & EA0V & Q312 & EA1V & Q288 &
    _ & _ & _).
  destruct HPLLblk as (PLL & idbP & pbP & Q304 & _ & Q296 & _ & Q176 & _ & _ & _ & _ & _ & _ & _ & HaId).
  subst A0V A1V.
  unfold FRAME_BYTES in HfrAo, HNfr.
  subst c. rewrite SEGS.
  destruct (fra_app B APIf ra g fr _ regs mem md HFRA) as (HGTfr & Hfrapp).
  destruct (fra_win B APIf ra g fr _ regs mem md HFRA) as (Hlow & HW0).
  pose proof (fra_frame B APIf ra g fr _ regs mem md HFRA) as (Hfrw & _ & _ & Hfrwr).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A2 & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA448 & HS4 & HAPP &
    Hspillq & Hsel & Hfr56 & Hloc & Hhdr1 & Hhdr2 & Hshf & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive & Hinb & Hinblk).
  clear Hs5 Hgimg Hsn Hsel Hfr56 Hhdr1 Hhdr2 Hshf Hsaved Herrno HAG HWA HSHI1 HSHI2 HSHI3 Hhb Hlive Hspillq
    Hinb Hinblk.
  unfold FRAME_BYTES in Hfrapp, Hfrwr, Hfrw.
  pose proof (AC.aa_laws AC.ASYMS AsanRTInv.RT (APIf rc)) as LAWS.
  pose proof (AC.a_laws_stack_high _ _ _ _ _ LAWS (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md HAH)
    as Hstkhi.
  assert (HHM : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  assert (HSS : AF.SLOT_STACK = 1048576) by reflexivity.
  assert (HGTv : AC.GT = 0x5fe000) by reflexivity.
  assert (HP64 : 2 ^ 64 = 18446744073709551616) by reflexivity.
  assert (HAE : APPMEM_END = 0x800000000000) by reflexivity.
  assert (HBK : BW.BCMP_WRAP_K = 4560) by reflexivity.
  assert (HFN : FN_STACK = 1044480) by reflexivity.
  pose proof Hwin as HwinB. destruct HwinB as (Hw0 & Hw1 & _).
  assert (Hsphi : HIGHMEM_BEG + AF.SLOT_STACK - 4096 < sp) by lia.
  assert (EA : A = A2).
  { pose proof (LMem.bytes_at_bound rsegs mem _ _ H272) as Hb. rewrite LMem.length_le8 in Hb.
    apply f16_bv_inj_spill; [lia | lia |]. unfold rg in *. rewrite <- Hr9. symmetry. exact Hs1. }
  subst A2.
  assert (HAb : 0 <= A < 2 ^ 64) by lia.
  assert (HA448' : A + 448 <= 2 ^ 64) by lia.
  assert (Hdisjfr : fr + 3136 <= sp - 32 \/ sp <= fr).
  { pose proof (Hfrw 32 ltac:(lia)) as H. rewrite Haspz in H. exact H. }
  assert (HdjK : fr + 3136 <= sp - BW.BCMP_WRAP_K \/ sp <= fr).
  { pose proof (Hfrw BW.BCMP_WRAP_K ltac:(lia)) as H. rewrite Haspz in H. exact H. }
  assert (Hfrhi : fr + 3136 <= APPMEM_END).
  { pose proof (Hfrapp (fr + 3135) ltac:(lia)) as H.
    unfold app_mem, LOWMEM_END, HIGHMEM_BEG, APPMEM_END in H. lia. }
  assert (Hfr0 : 0 <= fr) by lia.
  assert (Efragb : fragb fr = fr + 2768) by reflexivity.
  assert (Esp : bv_unsigned (getr regs 2) = sp) by (unfold AC.aspZ in Haspz; exact Haspz).
  assert (HAC0 : asan_cells mem) by exact (RT_cells sp mem md HRT).
  assert (HSW0 : shadow_rw mem) by exact (RT_shadow_rw sp mem md HRT).
  (* ---- the model side: the turn closes a record ---- *)
  pose proof (trf1_cls (g_in g) j Hrf) as Hcls.
  destruct (cls_close_inv _ _ _ Hcls) as (Hfrr & Hkeep & Hclose & _).
  pose proof (t_FG_length (g_in g) j) as HLst. pose proof (t_g_length (g_in g) j) as HLg.
  pose proof (t_FGf_length (g_in g) j) as HLf.
  pose proof (fr_n _ _ Hfrr) as Hn. pose proof (closeT64 _ _ Hkeep) as HT64.
  pose proof (frT14 _ _ Hclose) as HT14.
  pose proof (fr_len50 _ _ Hfrr) as Hlen50.
  assert (Hfl50 : 50 <= flen g j) by (unfold flen; lia).
  (* the FLV cells the ingest reads, and pll *)
  destruct HFLV as (F120 & F128 & F256 & F304 & F296 & Fcond).
  destruct (Fcond Hrf) as (Hpp & Hpn).
  (* the local `first` at fr + 2880: have = 1, n, the body (FI with frag_ok and fg_keep) *)
  pose proof HFSj as HFSj0.
  destruct HFSj0 as (Hhave & Hn8 & Hbody & Had40 & HFI).
  assert (Hbat6 : bat (t_FG (g_in g) j) 6 = 1).
  { pose proof (keep_hf _ _ Hkeep) as Hhf. unfold fg_hf in Hhf.
    destruct HfragOK as ([H0|H1] & _); [exfalso; apply Hhf; exact H0 | exact H1]. }
  destruct (HFI Hbat6) as (Hhave1 & Hnbeq & _).
  rewrite Hhave1 in Hhave.
  destruct (fst_bounds (g_in g) j) as (_ & Hnb).
  pose proof (fst_body_n (g_in g) j) as Hbl.
  pose proof (fst_body_len (g_in g) j) as HBL23.
  (* the frame-loop spill set *)
  pose proof HLK as HLK0. destruct HLK0 as (_ & H240s & HOURb & HFLI).
  destruct HFLI as (H27 & S168 & S96 & S112 & S120 & S128 & S136 & S144 & S152 & S280 & S160 & S176 &
    S192 & S200 & S216 & S208 & S104 & S256 & S264 & S288 & S296 & S304 & HFad & HFstk & HFrad & HFknt &
    S168b & S88).
  pose proof HFM as HFM0. destruct HFM0 as (S184 & Hs8r & Hs6r & Hs9r & S312).
  (* the identity record, the record bytes and the payload, as plain addresses *)
  assert (Hid0 : fr + 2688 <> 0) by lia.
  assert (Hidev : (fr + 2688) mod 2 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfrm in D.
    pose proof (Z.div_mod (fr + 2688) 2 ltac:(lia)) as D3.
    pose proof (Z.mod_pos_bound (fr + 2688) 2 ltac:(lia)).
    pose proof (Z.div_mod fr 2 ltac:(lia)) as D2. lia. }
  assert (Hal2880 : (fr + 2880) mod 4 = 0).
  { pose proof (Z.div_mod fr 32 ltac:(lia)) as D. rewrite Hfrm in D.
    replace (fr + 2880) with ((8 * (fr / 32) + 720) * 4) by lia. apply Z.mod_mul. lia. }
  assert (Hpnz : fragb fr + 19 <> 0) by lia.
  assert (HRnz : fragb fr + 15 <> 0) by lia.
  (* the ingest payload *)
  assert (Hpllb : 1 <= f_pll (t_FG (g_in g) j) (t_g (g_in g) j) <= 51)
    by (unfold f_pll; lia).
  assert (Hpb : bytes_at rsegs mem (fragb fr + 19)
            (firstn (Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))) (skipn 19 (t_FGf (g_in g) j)))).
  { apply ba_firstn. replace (fragb fr + 19) with (fragb fr + Z.of_nat 19) by lia.
    apply ba_skipn; [rewrite HLf; lia | exact HbRec]. }
  assert (Hpbl : length (firstn (Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)))
                                (skipn 19 (t_FGf (g_in g) j)))
                 = Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)))
    by (rewrite length_firstn, length_skipn, HLf; lia).
  assert (HADpb : addressable mem (fragb fr + 19) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))).
  { apply (addressable_sub mem (fragb fr) 72 19 _ HaRec); lia. }
  (* the identity record's 38 cells *)
  assert (Hidc : LSt.rw_cells rsegs mem (fr + 2688) [LCl.CB 38 idb]).
  { split.
    - split; [cbn; split; [exact LId | exact I]|].
      cbn [LCl.cells_bytes LCl.cbytes]. rewrite app_nil_r. exact HbId.
    - split; [lia|]. split; [cbn [LCl.cells_size LCl.csize]; lia|].
      intros i Hi. cbn [LCl.cells_size LCl.csize] in Hi. apply Hfrwr. lia. }
  (* the address the check compares: the fragment call's address is the joined record's bytes 17 / 18, which are
     joined_byte 9 / 10 of the FIRST state (joined_close, by FI) *)
  assert (HADb : 0 <= fg_addr (t_FG (g_in g) j) (t_g (g_in g) j) < 65536).
  { unfold fg_addr.
    pose proof (bat_nonneg (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 17).
    pose proof (bat_lt (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 17).
    pose proof (bat_nonneg (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 18).
    pose proof (bat_lt (fg_join (t_FG (g_in g) j) (t_g (g_in g) j)) 18). lia. }
  destruct (joined_close _ _ _ HLst HLg HfragOK HFI Hbat6 Hn HT14) as (E17 & E18).
  assert (EADj : fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)
                 = joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 10
                   + 256 * joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 9)
    by (unfold fg_addr; rewrite E17, E18; lia).
  pose proof (JB.jb_model_range (fst_at (g_in g) j) (t_g (g_in g) j) 9) as Rj9.
  pose proof (JB.jb_model_range (fst_at (g_in g) j) (t_g (g_in g) j) 10) as Rj10.
  (* the frame bytes at Phi that joined_byte reads past the FIRST body, and Phi's place below the stack *)
  assert (Hgb : bytes_at rsegs mem phi (t_g (g_in g) j))
    by (apply (fturn_g g j phi regs mem Hturn); unfold flen in Hfl50; lia).
  destruct (f16_blk (hb1 phi (AC.a_size (flen g j)) ++ g_H g) mem md phi (AC.a_size (flen g j)) HAH
              ltac:(apply in_or_app; left; unfold hb1; cbn [In]; left; reflexivity)) as (Hblkend & Hblkfs).
  assert (Easz : AC.a_size (flen g j) = flen g j)
    by (unfold AC.a_size; rewrite Z.max_l by lia; reflexivity).
  rewrite Easz in Hblkend, Hblkfs.
  assert (Hphisp : phi + 50 <= sp - 32) by lia.
  assert (Hphi50ad : addressable mem phi 50).
  { destruct HHB as (_ & Hphiad). rewrite Easz in Hphiad.
    pose proof (addressable_sub mem phi (flen g j) 0 50 Hphiad ltac:(lia) ltac:(lia) ltac:(lia)) as H.
    rewrite Z.add_0_r in H. exact H. }
  assert (Hphi0 : 0 < phi) by (destruct Haphi50e as (H0 & _); destruct HHB as (Hnz & _); lia).
  (* the ingest is not refused, and its result is 0 or 1 *)
  assert (Href : IGC.ingest_refused (fr + 2688) (fragb fr + 19)
                   (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) = false).
  { unfold IGC.ingest_refused. apply Bool.orb_false_intro.
    - apply Z.eqb_neq. exact Hid0.
    - apply Bool.andb_false_intro2. apply Z.eqb_neq. exact Hpnz. }
  set (pb := firstn (Z.to_nat (f_pll (t_FG (g_in g) j) (t_g (g_in g) j))) (skipn 19 (t_FGf (g_in g) j))).
  set (v0 := IGC.ingest_ret (fr + 2688) (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) (fragb fr + 19)
               (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)) idb pb).
  (* the identity record the ingest leaves is turn j + 1's (the cut's bytes are t_IDr j, by RECF) *)
  assert (Eidb : idb = t_IDr (g_in g) j).
  { apply (ba_det mem (fr + 2688) idb (t_IDr (g_in g) j) HbId (proj1 (proj1 HRECF))).
    rewrite LId, t_IDr_length. reflexivity. }
  assert (EIDS : t_ID (g_in g) (S j)
                 = snd (ING idb (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) pb)).
  { rewrite Eidb, (t_ID_S_rf (g_in g) j Hrf). reflexivity. }
  assert (Hv0b : 0 <= v0 < 2 ^ 63).
  { subst v0. unfold IGC.ingest_ret. rewrite Href.
    destruct (ING_ret idb (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)) pb) as [E|E]; rewrite E; lia. }
  set (W := [(sp - 32, sp); (fr + 2688, fr + 2688 + 38)]).
  assert (HGTW : forall lo hi, In (lo, hi) W -> AC.GT <= lo).
  { subst W. intros lo hi Hin. cbn in Hin.
    destruct Hin as [E|[E|[]]]; injection E as <- <-; unfold AC.GT in *; lia. }
  (* ---- the run 0x823d8 -> 0x82464 through the four calls ---- *)
  apply (f16_run_lib regs (Z_to_bv 64 0x823d8) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x82464 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\
       getr R 8 = getr regs 8 /\ getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\
       getr R 26 = getr regs 26 /\ getr R 18 = getr regs 18 /\ getr R 20 = getr regs 20 /\
       getr R 22 = getr regs 22 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 27 = getr regs 27 /\ getr R 10 = Z_to_bv 64 v0 /\
       LFr.munch W mem mem' /\ LFr.wmono rsegs mem mem' /\ ro_agree rsegs mem' /\
       LFr.stk rsegs mem' (sp - FN_STACK) sp /\
       LSt.rw_cells rsegs mem' (fr + 2688) [LCl.CB 38 (t_ID (g_in g) (S j))])
    (Post B APIf ra g)).
  - exact Hhalt.
  - (* the run reads none of the exit-only facts: clearing them keeps the run's lia calls from case-splitting on
       the cut's disjunctions and implications; the continuation is a separate goal and keeps them *)
    clear Hloc HphiBC HkpBC Hphi2688 Hkp2688 Hphi112 Hkp112 HdjK H8819 HRECF Hturn HFS9.
    clear Hcls Hfrr Hkeep Hclose Hrb Hrbl Haphi50e H27 H224 H240s HOURb Hw112 Hkp Hblkfs E17 E18
      HFad HFknt HFrad HFstk Hstkhi Hid0 Hpnz HFM HFSj HLK HENT HFRA Hexit Eidb LAWS Fcond HFI.
    rewrite f16_mkR_of_expand.
    f16_subst_slot Hs1. f16_subst_slot HrN. f16_subst_slot Hs6r. f16_subst_slot H27cut.
    f16_subst_slot Hs8. f16_subst_slot Hs9r.
    assert (ER : bv_unsigned (Z_to_bv 64 (fragb fr + 15)) = fragb fr + 15) by (apply LMS.unsigned_lit; lia).
    assert (EN : bv_unsigned (Z_to_bv 64 N) = N) by (apply LMS.unsigned_lit; lia).
    assert (E2880 : bv_unsigned (Z_to_bv 64 (fr + 2880)) = fr + 2880) by (apply LMS.unsigned_lit; lia).
    assert (E18q : bv_unsigned (Z_to_bv 64 (phi + 18)) = phi + 18) by (apply LMS.unsigned_lit; lia).
    assert (Enb : bv_unsigned (Z_to_bv 8 (fs_n (fst_at (g_in g) j))) = fs_n (fst_at (g_in g) j))
      by (apply JB.jb_lit8; lia).
    (* the facts the run reads carry over every callee's 16-byte window [sp - 16, sp) *)
    assert (HAW1 : all_app [(sp - 16, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia. }
    assert (HD1 : AsanRTInv.rt_disjoint [(sp - 16, sp)]).
    { apply f16_rtdj_GT. intros lo hi Hin. cbn in Hin. destruct Hin as [E|[]].
      injection E as <- <-. unfold AC.GT in *. lia. }
    assert (CARRY : forall m', LFr.munch [(sp - 16, sp)] mem m' -> LFr.wmono rsegs mem m' ->
      asan_cells m' /\ shadow_rw m' /\
      (forall a (bs0 : list byte), bytes_at rsegs mem a bs0 ->
         (a + Z.of_nat (length bs0) <= sp - 16 \/ sp <= a) -> bytes_at rsegs m' a bs0) /\
      (forall a n, addressable mem a n -> addressable m' a n)).
    { intros m' MU WM.
      pose proof (AsanRTInv.RT_store sp sp mem m' md md _ HRT MU WM HAW1 HD1) as HRT'.
      split; [exact (RT_cells sp m' md HRT')|]. split; [exact (RT_shadow_rw sp m' md HRT')|].
      split.
      - intros a bs0 Hb Hd. eapply fl_bytes; [exact Hb | exact MU |].
        intros x Hx. cbn. split; [lia | exact I].
      - intros a n Ha. exact (sl_addr_keep mem m' [(sp - 16, sp)] a n Ha MU HAW1). }
    (* the premises of joined_byte (first, blk, i) on a memory that keeps the frame bytes and Phi's bytes *)
    assert (JBP : forall m' i, (i = 9 \/ i = 10) ->
      bytes_at rsegs m' (fr + 2885) (fs_body (fst_at (g_in g) j)) ->
      bytes_at rsegs m' phi (t_g (g_in g) j) ->
      addressable m' (fr + 2880) 40 -> addressable m' phi 50 ->
      bytes_at rsegs m' (JBC.jb_addr (fr + 2880) (phi + 18) (fs_n (fst_at (g_in g) j)) i)
        [Z_to_bv 8 (joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) i)] /\
      addressable m' (JBC.jb_addr (fr + 2880) (phi + 18) (fs_n (fst_at (g_in g) j)) i) 1 /\
      (JBC.jb_addr (fr + 2880) (phi + 18) (fs_n (fst_at (g_in g) j)) i + 1 <= sp - 16 \/
       sp <= JBC.jb_addr (fr + 2880) (phi + 18) (fs_n (fst_at (g_in g) j)) i)).
    { intros m' i Hi Hbd Hg' Ha1' Ha2'.
      split.
      { apply (JB.joined_byte_model_rd m' fr phi _ _ i Hi); [lia | exact Hbl | rewrite HLg; lia | exact Hbd
                                                            | exact Hg']. }
      destruct (f16_jb_addr m' fr phi (fs_n (fst_at (g_in g) j)) i Hi Hnb Ha1' Ha2') as (Had & Hrng).
      split; [exact Had|].
      destruct Hrng as [Hr|Hr]; destruct Hdisjfr as [Hd|Hd]; lia. }
    pose proof HRSC as HR.
    unfold RSC.record_sum_closes_contract, RSC.RECORD_SUM_CLOSES, RSC.RECORD_SUM_CLOSES_FRAME in HR.
    pose proof HJB as HJ.
    unfold JBC.joined_byte_contract, JBC.JOINED_BYTE, JBC.JOINED_BYTE_FRAME in HJ.
    pose proof HING as HI.
    unfold IGC.reac_identity_ingest_contract, IGC.REAC_IDENTITY_INGEST, IGC.REAC_IDENTITY_INGEST_FRAME in HI.
    (* 0x823d8 ld a0,120(s1) ; 0x823dc jal record_sum_closes *)
    pose proof (f16_rd8 mem _ _ Q120 ltac:(apply LMem.length_le8)) as RD120.
    step. step.
    eapply evt_cut.
    { eapply HR with (bs := bsN) (lo := sp - FN_STACK).
      - rewrite EN. exact HbsNl.
      - right. rewrite ER, EN. split; [exact HRnz|]. split; [lia|].
        split; [exact HbsN|]. rewrite Esp.
        destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - rewrite Esp. rewrite Haspz in HW0. exact HW0.
      - rewrite Esp. lia.
      - intros _. exact HAC0.
      - intros _. exact HSW0.
      - intros _. rewrite ER, EN. exact HadN.
      - intros _ x Hx. rewrite Esp. apply (f16_rt_out1 sp x 16); [lia | lia | exact Hx]. }
    intros ms' (t0' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & m1 & Ems & MU1 & WM1 & MI1 & ST1).
    subst ms'.
    replace (if recsum bsN =? 0 then 1 else 0) with 1 by (rewrite HrecN; reflexivity).
    replace (ret_pc (Z_to_bv 64 533472)) with (Z_to_bv 64 533472)
      by (symmetry; apply LMS.ret_pc_even; [lia | reflexivity]).
    rewrite Esp in MU1, ST1.
    destruct (CARRY m1 MU1 WM1) as (HAC1 & HSW1 & TR1 & AD1).
    assert (QA1 : forall off v, 0 <= off -> q64 mem (A + off) v -> q64 m1 (A + off) v)
      by (intros off v Hoff Hq; unfold q64 in *; apply TR1; [exact Hq | right; lia]).
    assert (FB1 : forall a (bs0 : list byte), fr <= a -> a + Z.of_nat (length bs0) <= fr + 3136 ->
                    bytes_at rsegs mem a bs0 -> bytes_at rsegs m1 a bs0)
      by (intros a bs0 H1 H2 Hb; apply TR1; [exact Hb | destruct Hdisjfr as [Hd|Hd]; [left | right]; lia]).
    assert (Hhv1 : u32 m1 (fr + 2880) 1)
      by (unfold u32 in *; apply FB1; [lia | rewrite LMem.length_le4; lia | exact Hhave]).
    assert (HU1 : u16 m1 (fr + 256) (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)))
      by (unfold u16 in *; apply FB1; [lia | rewrite LMem.length_le2; lia | exact HU256]).
    assert (Hn81 : b8 m1 (fr + 2884) (fs_n (fst_at (g_in g) j)))
      by (unfold b8 in *; apply FB1; [lia | cbn [length]; lia | exact Hn8]).
    assert (Hbd1 : bytes_at rsegs m1 (fr + 2885) (fs_body (fst_at (g_in g) j)))
      by (apply FB1; [lia | lia | exact Hbody]).
    assert (Hg1 : bytes_at rsegs m1 phi (t_g (g_in g) j))
      by (apply TR1; [exact Hgb | rewrite HLg; left; lia]).
    pose proof (f16_rd8 m1 _ _ (QA1 168 _ ltac:(lia) Q168) ltac:(apply LMem.length_le8)) as RD168.
    pose proof (f16_rd4 m1 _ _ Hhv1 ltac:(apply LMem.length_le4)) as RDhv.
    pose proof (f16_rd8 m1 _ _ (QA1 288 _ ltac:(lia) Q288) ltac:(apply LMem.length_le8)) as RD288.
    pose proof (f16_rd2 m1 _ _ HU1 ltac:(apply LMem.length_le2)) as RDad.
    pose proof (f16_rd8 m1 _ _ (QA1 312 _ ltac:(lia) Q312) ltac:(apply LMem.length_le8)) as RD312.
    (* 0x823e0 beqz a0 : the callee returned 1, not taken *)
    step. if_false.
    (* 0x823e4 ld a0,168(s1) ; 0x823e8 lw a0,0(a0) ; 0x823ec beqz a0 : first->have = 1, not taken *)
    step. step. step. if_false.
    (* 0x823f0 ld a0,288(s1) ; 0x823f4 lhu s5,0(a0) ; 0x823f8 li a2,9 ; 0x823fc ld s6,168(s1) ;
       0x82400 mv a0,s6 ; 0x82404 mv s11,s8 ; 0x82408 mv s8,s9 ; 0x8240c ld s9,312(s1) ; 0x82410 mv a1,s9 ;
       0x82414 jal joined_byte *)
    step. step. step. step. step. step. step. step. step. step.
    rewrite ?(f16_zx16 _ HADb).
    destruct (JBP m1 9 ltac:(lia) Hbd1 Hg1 (AD1 _ _ Had40) (AD1 _ _ Hphi50ad)) as (HB9 & HA9 & HD9).
    eapply evt_cut.
    { eapply HJ with (i := 9) (lo := sp - FN_STACK) (nb := Z_to_bv 8 (fs_n (fst_at (g_in g) j)))
        (b := Z_to_bv 8 (joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 9)).
      all: rewrite ?E2880, ?E18q, ?Enb, ?Esp.
      - left; reflexivity.
      - reflexivity.
      - exact Hal2880.
      - replace (fr + 2880 + 4) with (fr + 2884) by lia. exact Hn81.
      - intros _. lia.
      - exact HB9.
      - exact ST1.
      - lia.
      - destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - exact HD9.
      - exact HAC1.
      - exact HSW1.
      - apply (addressable_sub m1 (fr + 2880) 40 4 1 (AD1 _ _ Had40)); lia.
      - exact HA9.
      - intros x Hx. apply (f16_rt_out1 sp x 16); [lia | lia | exact Hx]. }
    intros ms' (a1'' & a2'' & a3'' & a4'' & a5'' & a6'' & m2 & Ems & MU2 & WM2 & MI2 & ST2).
    subst ms'.
    rewrite (f16_zxb8 _ Rj9).
    replace (ret_pc (Z_to_bv 64 533528)) with (Z_to_bv 64 533528)
      by (symmetry; apply LMS.ret_pc_even; [lia | reflexivity]).
    rewrite Esp in MU2, ST2.
    assert (MU12 : LFr.munch [(sp - 16, sp)] mem m2)
      by (intros x Hx; rewrite (MU2 x Hx); apply MU1; exact Hx).
    assert (WM12 : LFr.wmono rsegs mem m2) by (intros x Hx; apply WM2; apply WM1; exact Hx).
    destruct (CARRY m2 MU12 WM12) as (HAC2 & HSW2 & TR2 & AD2).
    assert (FB2 : forall a (bs0 : list byte), fr <= a -> a + Z.of_nat (length bs0) <= fr + 3136 ->
                    bytes_at rsegs mem a bs0 -> bytes_at rsegs m2 a bs0)
      by (intros a bs0 H1 H2 Hb; apply TR2; [exact Hb | destruct Hdisjfr as [Hd|Hd]; [left | right]; lia]).
    assert (Hn82 : b8 m2 (fr + 2884) (fs_n (fst_at (g_in g) j)))
      by (unfold b8 in *; apply FB2; [lia | cbn [length]; lia | exact Hn8]).
    assert (Hbd2 : bytes_at rsegs m2 (fr + 2885) (fs_body (fst_at (g_in g) j)))
      by (apply FB2; [lia | lia | exact Hbody]).
    assert (Hg2 : bytes_at rsegs m2 phi (t_g (g_in g) j))
      by (apply TR2; [exact Hgb | rewrite HLg; left; lia]).
    (* 0x82418 slli s7,a0,8 ; 0x8241c li a2,10 ; 0x82420 mv a0,s6 ; 0x82424 li s6,1 ; 0x82428 mv a1,s9 ;
       0x8242c mv s9,s8 ; 0x82430 mv s8,s11 ; 0x82434 li s11,-8 ; 0x82438 jal joined_byte *)
    step. step. step. step. step. step. step. step. step.
    destruct (JBP m2 10 ltac:(lia) Hbd2 Hg2 (AD2 _ _ Had40) (AD2 _ _ Hphi50ad)) as (HB10 & HA10 & HD10).
    eapply evt_cut.
    { eapply HJ with (i := 10) (lo := sp - FN_STACK) (nb := Z_to_bv 8 (fs_n (fst_at (g_in g) j)))
        (b := Z_to_bv 8 (joined_byte (fst_at (g_in g) j) (t_g (g_in g) j) 10)).
      all: rewrite ?E2880, ?E18q, ?Enb, ?Esp.
      - right; reflexivity.
      - reflexivity.
      - exact Hal2880.
      - replace (fr + 2880 + 4) with (fr + 2884) by lia. exact Hn82.
      - intros _. lia.
      - exact HB10.
      - exact ST2.
      - lia.
      - destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - exact HD10.
      - exact HAC2.
      - exact HSW2.
      - apply (addressable_sub m2 (fr + 2880) 40 4 1 (AD2 _ _ Had40)); lia.
      - exact HA10.
      - intros x Hx. apply (f16_rt_out1 sp x 16); [lia | lia | exact Hx]. }
    intros ms' (a1''' & a2''' & a3''' & a4''' & a5''' & a6''' & m3 & Ems & MU3 & WM3 & MI3 & ST3).
    subst ms'.
    rewrite (f16_zxb8 _ Rj10).
    replace (ret_pc (Z_to_bv 64 533564)) with (Z_to_bv 64 533564)
      by (symmetry; apply LMS.ret_pc_even; [lia | reflexivity]).
    rewrite Esp in MU3, ST3.
    assert (MU13 : LFr.munch [(sp - 16, sp)] mem m3)
      by (intros x Hx; rewrite (MU3 x Hx); apply MU12; exact Hx).
    assert (WM13 : LFr.wmono rsegs mem m3) by (intros x Hx; apply WM3; apply WM12; exact Hx).
    destruct (CARRY m3 MU13 WM13) as (HAC3 & HSW3 & TR3 & AD3).
    assert (QA3 : forall off v, 0 <= off -> q64 mem (A + off) v -> q64 m3 (A + off) v)
      by (intros off v Hoff Hq; unfold q64 in *; apply TR3; [exact Hq | right; lia]).
    assert (FB3 : forall a (bs0 : list byte), fr <= a -> a + Z.of_nat (length bs0) <= fr + 3136 ->
                    bytes_at rsegs mem a bs0 -> bytes_at rsegs m3 a bs0)
      by (intros a bs0 H1 H2 Hb; apply TR3; [exact Hb | destruct Hdisjfr as [Hd|Hd]; [left | right]; lia]).
    assert (HU3 : u16 m3 (fr + 256) (fg_addr (t_FG (g_in g) j) (t_g (g_in g) j)))
      by (unfold u16 in *; apply FB3; [lia | rewrite LMem.length_le2; lia | exact HU256]).
    assert (Hpp3 : q64 m3 (fr + 272) (fragb fr + 19))
      by (unfold q64 in *; apply FB3; [lia | rewrite LMem.length_le8; lia | exact Hpp]).
    assert (Hpn3 : q64 m3 (fr + 304) (f_pll (t_FG (g_in g) j) (t_g (g_in g) j)))
      by (unfold q64 in *; apply FB3; [lia | rewrite LMem.length_le8; lia | exact Hpn]).
    assert (Hpb3 : bytes_at rsegs m3 (fragb fr + 19) pb)
      by (subst pb; apply FB3; [lia | rewrite Hpbl; lia | exact Hpb]).
    assert (Hidc3 : LSt.rw_cells rsegs m3 (fr + 2688) [LCl.CB 38 idb]).
    { eapply LFr.rw_cells_transport; [exact Hidc | exact MU13 | exact WM13 |].
      cbn [LCl.cells_size LCl.csize Nat.add]. cbn.
      split; [destruct Hdisjfr as [Hd|Hd]; [left | right]; lia | exact I]. }
    pose proof (f16_rd8 m3 _ _ (QA3 288 _ ltac:(lia) Q288) ltac:(apply LMem.length_le8)) as RD288'.
    pose proof (f16_rd2 m3 _ _ HU3 ltac:(apply LMem.length_le2)) as RDad'.
    pose proof (f16_rd8 m3 _ _ (QA3 304 _ ltac:(lia) Q304) ltac:(apply LMem.length_le8)) as RD304.
    pose proof (f16_rd8 m3 _ _ Hpp3 ltac:(apply LMem.length_le8)) as RDpp.
    pose proof (f16_rd8 m3 _ _ (QA3 296 _ ltac:(lia) Q296) ltac:(apply LMem.length_le8)) as RD296.
    pose proof (f16_rd8 m3 _ _ Hpn3 ltac:(apply LMem.length_le8)) as RDpn.
    pose proof (f16_rd8 m3 _ _ (QA3 176 _ ltac:(lia) Q176) ltac:(apply LMem.length_le8)) as RD176.
    (* 0x8243c or a0,s7,a0 ; 0x82440 bne a0,s5 : (jb 9 << 8) | jb 10 = joined_addr = the fragment's address *)
    step.
    rewrite (f16_or8 _ _ Rj10 Rj9), <- EADj.
    rewrite ?(f16_zx16 _ HADb).
    step. if_false.
    (* 0x82444 ld a0,288(s1) ; 0x82448 lhu a1,0(a0) ; 0x8244c ld a0,304(s1) ; 0x82450 ld a2,0(a0) ;
       0x82454 ld a0,296(s1) ; 0x82458 ld a3,0(a0) ; 0x8245c ld a0,176(s1) ; 0x82460 jal reac_identity_ingest *)
    step. step. step. step. step. step. step. step.
    rewrite ?(f16_zx16 _ HADb).
    eapply evt_cut.
    { eapply HI with (id := fr + 2688) (ad := fg_addr (t_FG (g_in g) j) (t_g (g_in g) j))
        (p := fragb fr + 19) (len := f_pll (t_FG (g_in g) j) (t_g (g_in g) j))
        (idb := idb) (pb := pb) (lo := sp - FN_STACK).
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - reflexivity.
      - lia.
      - exact HADb.
      - lia.
      - lia.
      - intros _. split; [exact Hidev | exact Hidc3].
      - subst pb. exact Hpbl.
      - intros _ _. exact Hpb3.
      - intros _ _ _. right. lia.
      - rewrite Esp. exact ST3.
      - rewrite Esp. lia.
      - intros _. rewrite Esp. destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - intros _ _. rewrite Esp. destruct Hdisjfr as [Hd|Hd]; [left | right]; lia.
      - exact HAC3.
      - exact HSW3.
      - intros _. exact (AD3 _ _ HaId).
      - intros _ _. exact (AD3 _ _ HADpb).
      - intros x Hx. rewrite Esp.
        unfold IGC.reac_identity_ingest_W, IGC.REAC_IDENTITY_INGEST_FRAME.
        apply (f16_rt_out2 sp fr x); [lia | exact HGTfr | exact Hfrapp | exact Hx]. }
    intros ms' (ti0 & ti1 & ti2 & ai1 & ai2 & ai3 & ai4 & ai5 & ai6 & ai7 & ti3 & ti4 & ti5 & ti6
                & m4 & Ems4 & MU4 & WM4 & MI4 & ST4 & _ & HRW).
    subst ms'.
    replace (ret_pc (Z_to_bv 64 533604)) with (Z_to_bv 64 533604)
      by (symmetry; apply LMS.ret_pc_even; [lia | reflexivity]).
    rewrite Esp in MU4, ST4. unfold IGC.reac_identity_ingest_W, IGC.REAC_IDENTITY_INGEST_FRAME in MU4.
    assert (MUW : LFr.munch W mem m4).
    { subst W. intros x Hx. rewrite (MU4 x Hx). apply MU13.
      cbn in Hx |- *. destruct Hx as (Hx1 & _). split; [lia | exact I]. }
    apply evt_done. cbv beta.
    do 3 eexists. split; [reflexivity|].
    do 15 (split; [first [reflexivity | apply bv_eq; vm_compute; reflexivity | f_equal; lia]|]).
    split; [exact MUW|].
    split; [intros x Hx; apply WM4; apply WM13; exact Hx|].
    split; [exact (f16_ro_keep W mem m4 HGTW MUW Hro)|].
    split; [exact ST4|].
    rewrite EIDS. exact (HRW Href).
  - (* ---- the continuation: rebuild the official F17 entry cut at 0x82464 ---- *)
    intros R pc' mem' regs' md'
      (Hpc & Er2 & Er3 & Er4 & Er8 & Er9 & Er19 & Er26 & Er18 & Er20 & Er22 & Er24 & Er25 & Er27 & Er10 &
       MU & WM & HroM & ST' & Hib) Hreg Hmat.
    subst pc'.
    assert (Fr2 : getr regs' 2 = getr regs 2) by (rewrite Hreg; exact Er2).
    assert (Fr3 : getr regs' 3 = getr regs 3) by (rewrite Hreg; exact Er3).
    assert (Fr4 : getr regs' 4 = getr regs 4) by (rewrite Hreg; exact Er4).
    assert (Fr8 : getr regs' 8 = getr regs 8) by (rewrite Hreg; exact Er8).
    assert (Fr9 : getr regs' 9 = getr regs 9) by (rewrite Hreg; exact Er9).
    assert (Fr19 : getr regs' 19 = getr regs 19) by (rewrite Hreg; exact Er19).
    assert (Fr26 : getr regs' 26 = getr regs 26) by (rewrite Hreg; exact Er26).
    assert (Fr18 : getr regs' 18 = getr regs 18) by (rewrite Hreg; exact Er18).
    assert (Fr20 : getr regs' 20 = getr regs 20) by (rewrite Hreg; exact Er20).
    assert (Fr22 : getr regs' 22 = getr regs 22) by (rewrite Hreg; exact Er22).
    assert (Fr24 : getr regs' 24 = getr regs 24) by (rewrite Hreg; exact Er24).
    assert (Fr25 : getr regs' 25 = getr regs 25) by (rewrite Hreg; exact Er25).
    assert (Fr27 : getr regs' 27 = getr regs 27) by (rewrite Hreg; exact Er27).
    assert (Fr10 : getr regs' 10 = Z_to_bv 64 v0) by (rewrite Hreg; exact Er10).
    assert (Easp : AC.aspZ regs' = AC.aspZ regs) by (unfold AC.aspZ; rewrite Fr2; reflexivity).
    assert (HOW : forall x, (x < sp - 32 \/ sp <= x) -> (x < fr + 2688 \/ fr + 2688 + 38 <= x) ->
                    LFr.outside W x) by (intros x H1 H2; subst W; apply f16_out2; assumption).
    assert (Hallapp : all_app W).
    { subst W. cbn [all_app]. split; [|split; [|exact I]].
      - intros a Ha. unfold app_mem. right. unfold HIGHMEM_BEG, APPMEM_END, AF.SLOT_STACK in *. lia.
      - intros a Ha. apply Hfrapp. lia. }
    assert (HPRES : forall q, fr + 2688 <= q < fr + 2688 + 38 ->
              exists b, LMem.mrd rsegs mem' (LMem.wa q) = Some b).
    { intros q Hq.
      apply (f16_present mem' (fr + 2688) (t_ID (g_in g) (S j)) q
               (f16_lrw38 mem' _ (t_ID (g_in g) (S j)) Hib)).
      rewrite t_ID_length. lia. }
    assert (MUa : LFr.munch [(AC.aspZ regs - 32, AC.aspZ regs); (fr + 2688, fr + 2688 + 38)] mem mem')
      by (rewrite Haspz; exact MU).
    assert (STa : LFr.stk rsegs mem' (AC.aspZ regs - FN_STACK) (AC.aspZ regs))
      by (rewrite Haspz; exact ST').
    destruct (f16_fra g fr (hb1 phi (AC.a_size (flen g j))) regs regs' mem mem' md md' A HFRA HENT Hs1 HAb
                MUa WM HroM STa HPRES Fr2 Fr3 Fr4 Fr8 Fr9 Fr19 Fr26 Hmat)
      as (HFRA' & HENT').
    (* the placements of Phi, of the frame cells and of the spill area against W *)
    assert (Hphi50 : phi + 50 <= AC.aa_stklo AC.ASYMS AsanRTInv.RT (APIf rc) mem md) by lia.
    (* the whole record block, not only its first 50 bytes: FTURN's Phi bytes are len_j long *)
    assert (HOphi : forall x, phi <= x < phi + flen g j -> LFr.outside W x).
    { intros x Hx. apply HOW; [left; lia|].
      destruct (Z_lt_le_dec x (fr + 2688)) as [Hl|Hl]; [left; lia|].
      destruct (Z_lt_le_dec x (fr + 2688 + 38)) as [Hh|Hh]; [|right; lia].
      exfalso. unfold FRAME_BYTES in Hloc. destruct Hloc as [[_ [_ Hreal]]|[_ [_ [Hfs _]]]].
      - destruct (Hreal x ltac:(lia)) as (Hlo2 & _). lia.
      - exact (Hblkfs x ltac:(lia) (Hfs x ltac:(lia))). }
    assert (HOphi50 : forall x, phi <= x < phi + 50 -> LFr.outside W x)
      by (intros x Hx; apply HOphi; lia).
    (* the two frame / save-area facts below need only the frame-vs-stack placement and Hx: lia on the whole
       context case-splits on every placement disjunction of the cut *)
    assert (HOWfr : forall x, fr <= x < fr + 2688 \/ fr + 2688 + 38 <= x < fr + 3136 -> LFr.outside W x).
    { intros x Hx. apply HOW; clear - Hx Hdisjfr; lia. }
    assert (HOA : forall x, A <= x < A + 448 -> LFr.outside W x)
      by (intros x Hx; apply HOW; clear - Hx HspAo HfrAo Haspz; lia).
    assert (HOsh : forall x, in_shadow x -> LFr.outside W x).
    { intros x Hx. apply (f16_out_not_app W x Hallapp). intro Hap. exact (app_not_shadow x Hap Hx). }
    assert (Hmeta : meta_kept mem mem') by exact (munch_meta W mem mem' MU Hallapp).
    rewrite <- SEGS. apply Hexit.
    exists phi, regs', mem', md', fr.
    split; [reflexivity|].
    split; [exact HFRA'|].
    split; [exact HENT'|].
    split; [exact Hgn|].
    split; [exact Hj|].
    split.
    { destruct HHB as (Hphinz & Hphiad). split; [exact Hphinz|].
      exact (addressable_kept mem mem' phi (AC.a_size (flen g j)) Hphiad Hmeta). }
    split.
    { eapply f16_lk_keep; [exact HLK | exact Hs1 | lia | lia | exact Fr9 | exact Fr27 | exact MU | exact WM
                          | exact Hallapp | exact HOA | | |].
      - intros x Hx. apply HOWfr. lia.
      - intros x Hx. apply HOW; [left; unfold AC.GT, HIGHMEM_BEG, AF.SLOT_STACK in *; lia
                                | left; unfold AC.GT in *; lia].
      (* the kind-name table is image memory below GT, under both parts of W *)
      - (* a frame byte inside W is an identity byte (the stack part misses the frame), present by the ingest *)
        intros x Hx. destruct (f16_out_dec W x) as [Ho|Hno]; [left; exact Ho|]. right.
        subst W. apply f16_not_out2 in Hno.
        destruct Hno as [Hr|Hr]; [exfalso; destruct Hdisjfr; lia | exact (HPRES x ltac:(lia))]. }
    split; [unfold rg in *; rewrite Fr20; exact Hs4|].
    split.
    { eapply f16_spill_keep; [exact H224 | exact Hs1 | lia | lia | lia | exact Fr9 | exact MU | exact HOA]. }
    split.
    { eapply f16_fm_keep; [exact HFM | exact Hs1 | lia | lia | exact Fr9 | exact Fr22 | exact Fr24
                          | exact Fr25 | exact MU | exact HOA]. }
    split.
    { eapply f16_fsj_keep; [exact HFSj | exact MU | exact Hallapp | | lia].
      intros x Hx. apply HOWfr. lia. }
    split; [unfold rg in *; rewrite Fr18; exact Hs2|].
    split.
    { destruct HHB as (_ & Hphiad).
      assert (Had : addressable mem' phi (AC.a_size (flen g j)))
        by exact (addressable_kept mem mem' phi (AC.a_size (flen g j)) Hphiad Hmeta).
      pose proof (addressable_sub mem' phi (AC.a_size (flen g j)) 0 50 Had ltac:(lia) ltac:(lia)
                    ltac:(rewrite Easz; lia)) as Hsub.
      replace (phi + 0) with phi in Hsub by lia. exact Hsub. }
    split.
    { exists (firstn 38 rb). split; [|rewrite length_firstn; lia].
      eapply fl_bytes; [apply ba_firstn; exact Hrb | exact MU |].
      rewrite length_firstn. intros x Hx. apply HOphi. lia. }
    split.
    { exists v0. split; [unfold rg; exact Fr10 | exact Hv0b]. }
    split; [unfold rg in *; rewrite Fr27; exact H27|].
    split.
    { exists A, kp.
      split; [unfold rg in *; rewrite Fr9; exact Hs1|].
      split.
      { unfold q64 in *. eapply fl_bytes; [exact Hkp | exact MU |].
        rewrite LMem.length_le8. intros x Hx. apply HOA. lia. }
      split; [exact Hw112|].
      split.
      { exists w272.
        split.
        { unfold q64 in *. eapply fl_bytes; [exact H272 | exact MU |].
          rewrite LMem.length_le8. intros x Hx. apply HOA. lia. }
        split; [exact Hw272b|]. split; [exact Hw272t | exact Hw272f]. }
      split; [unfold rg in *; rewrite Fr24; exact Hs8|].
      split; [exact Hphi112|].
      split; [exact Hkp112|].
      split; [rewrite Easp; exact HphiBC|].
      split; [rewrite Easp; exact HkpBC|].
      (* the record facts are carried only on the parsed-header arm, as the cut states them *)
      intros H8. destruct (H8819 H8) as (HRI &
        (L & ls & rs & QL & HBL & HLls & HBR & HLrs & Hmm & HADL & HapL6 & HapL7 & HLBC & HLA & HL2688) &
        (L2 & ls2 & rs2 & QL2 & HBL2 & HLls2 & HBR2 & HLrs2 & Hmm2 & HADL2 & HapL26 & HapL27 & HL2BC & HL2A &
         HL22688)).
      (* the two compare operands miss the ingest's write set: they are below the wrapper's scratch (so below
         sp - 32) or at or above sp, and apart from the identity record *)
      assert (HOL : forall x, L <= x < L + 6 -> LFr.outside W x).
      { intros x Hx. apply HOW; [destruct HLBC as [Hd|Hd]; [left | right]; lia
                                | destruct HL2688 as [Hd|Hd]; [left | right]; lia]. }
      assert (HOL2 : forall x, L2 <= x < L2 + 6 -> LFr.outside W x).
      { intros x Hx. apply HOW; [destruct HL2BC as [Hd|Hd]; [left | right]; lia
                                | destruct HL22688 as [Hd|Hd]; [left | right]; lia]. }
      assert (HOkp : forall x, kp + 20 <= x < kp + 22 -> LFr.outside W x).
      { intros x Hx. apply HOW; [destruct HkpBC as [Hd|Hd]; [left; rewrite Haspz in Hd; lia
                                                            | right; rewrite Haspz in Hd; lia]
                                | destruct Hkp2688 as [Hd|Hd]; [left | right]; lia]. }
      split.
      { apply (f16_rec_inv_keep g j phi A kp mem mem' W HRI MU HOphi50);
          [intros x Hx; apply HOA; lia | exact HOsh | exact HOkp]. }
      split.
      { exists L, ls, rs.
        split.
        { unfold q64 in *. eapply fl_bytes; [exact QL | exact MU |].
          rewrite LMem.length_le8. intros x Hx. apply HOA. lia. }
        split.
        { eapply fl_bytes; [exact HBL | exact MU |]. rewrite HLls. intros x Hx. apply HOL. lia. }
        split; [lia|].
        split.
        { eapply fl_bytes; [exact HBR | exact MU |]. rewrite HLrs. intros x Hx. apply HOphi. lia. }
        split; [lia|].
        split; [exact Hmm|].
        split; [exact (addressable_kept mem mem' L 6 HADL Hmeta)|].
        split; [exact HapL6|]. split; [exact HapL7|].
        split; [rewrite Easp; exact HLBC | exact HLA]. }
      { exists L2, ls2, rs2.
        split.
        { unfold q64 in *. eapply fl_bytes; [exact QL2 | exact MU |].
          rewrite LMem.length_le8. intros x Hx. apply HOA. lia. }
        split.
        { eapply fl_bytes; [exact HBL2 | exact MU |]. rewrite HLls2. intros x Hx. apply HOL2. lia. }
        split; [lia|].
        split.
        { eapply fl_bytes; [exact HBR2 | exact MU |]. rewrite HLrs2. intros x Hx. apply HOphi. lia. }
        split; [lia|].
        split; [exact Hmm2|].
        split; [exact (addressable_kept mem mem' L2 6 HADL2 Hmeta)|].
        split; [exact HapL26|]. split; [exact HapL27|].
        split; [rewrite Easp; exact HL2BC | exact HL2A]. } }
    (* FTURN: the turn's two cursor spills and Phi's frame bytes *)
    split.
    { destruct Hturn as (T224 & T232 & Tphi & Tlen).
      split.
      { eapply f16_spill_keep; [exact T224 | exact Hs1 | lia | lia | lia | exact Fr9 | exact MU |].
        intros x Hx. apply HOA. lia. }
      split.
      { eapply f16_spill_keep; [exact T232 | exact Hs1 | lia | lia | lia | exact Fr9 | exact MU |].
        intros x Hx. apply HOA. lia. }
      split; [|exact Tlen].
      eapply fl_bytes; [exact Tphi | exact MU |]. intros x Hx. apply HOphi. unfold flen in *. lia. }
    (* RECS: the identity record the ingest wrote is turn j + 1's, the fragment record is the fragment call's *)
    split.
    { split.
      - split.
        + unfold IDBe. exact (f16_lrw38 mem' (fr + 2688) _ Hib).
        + rewrite EIDS, Eidb. apply RcIdentLib.ING_id_ok;
            [apply t_IDr_length | exact (proj2 (proj1 HRECF))].
      - split.
        + unfold FGBe. rewrite t_FG_S. eapply fl_bytes; [exact HbRec | exact MU |].
          rewrite t_FGf_length. intros x Hx. apply HOWfr. unfold fragb in *. lia.
        + apply fok_FG. }
    (* FS9: the spill [A+248] is above the run's write set *)
    eapply f16_fs9_keep; [exact HFS9 | exact Hs1 | lia | lia | exact Fr9 | exact MU | exact HOA].
Qed.

End F16.
