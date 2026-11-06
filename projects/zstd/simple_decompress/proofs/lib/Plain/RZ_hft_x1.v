(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac u32st2 RK s x v :=
  lazymatch type of RK with u32arr ?segs ?mx ?Wb (map (Z_to_bv 64) ?l) =>
    let a := cur_mem_addr in
    let SOK := fresh "SOK" in
    pose proof (u32arr_store_ok segs mx Wb _ s a RK ltac:(rewrite length_map, ?Zupd_length; lia) ltac:(unfold wa; f_equal; lia)) as SOK;
    zstep;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem mx ?a2 _) _) =>
      replace a2 with (wa (Wb + 4 * s)) by (unfold wa; f_equal; lia) end;
    let S2 := fresh "RK" in
    pose proof (u32arr_write segs mx Wb _ s (Z_to_bv 64 x) RK ltac:(rewrite length_map, ?Zupd_length; lia)) as S2;
    clear RK; store_done;
    apply (u32arr_upd_Z segs _ Wb l (Z.to_nat s) x v) in S2; [| first [ reflexivity | rewrite Z.mod_mod by lia; reflexivity ]];
    rename S2 into RK
  end.

Section X1.
  Hypothesis RSTATS : huf_rstats_stmt.

  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV SRC n DT WK wksz lo : Z) (src dtb : list byte).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.
  Hypothesis SRCLEN : Z.of_nat (length src) = n.  Hypothesis SRCL : 4096 <= SRC.  Hypothesis NR : n < 2^32.  Hypothesis SRCH : SRC + n < 2^47.
  Hypothesis HDR : huf_hdr_ok dtb.  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis OFFSRC : SRC + n <= lo \/ SPV <= SRC.  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis DTSRC : DT + HUF_DTABLE_BYTES <= SRC \/ SRC + n <= DT.  Hypothesis WKSRC : WK + wksz <= SRC \/ SRC + n <= WK.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation MUNCH := [(DT, DT + HUF_DTABLE_BYTES); (WK, WK + wksz); (SPV - HUF_TBL_STACK, SPV)].

  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -176)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].

  (* [comment removed for export] *)
  Lemma x1_exit : forall m1 f0 dtb' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    u8arr psegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk psegs m1 WK (WK + wksz) -> stk psegs m1 lo (SPV + -176) ->
    rw_cells psegs m1 (SPV + -176) f0 -> cells_size f0 = 72%nat -> rw_cells psegs m1 (SPV + -104) SAVED ->
    mem_inv psegs m1 -> munch MUNCH m m1 -> wmono psegs m m1 -> 0 <= r < 2^64 ->
    (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> false = true)) ->
    evt psegs POST (STF 0x1cf3c m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros DTC HDR' WKS STK F0 SZ0 FSAV MI MU WM RR RES. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    zstep. do 13 zstep. zstep.
    apply stk_of_rw_cells in F0, FSAV. rewrite SZ0 in F0. cbn [cells_size csize Nat.add] in FSAV.
    assert (STK' : stk psegs m1 lo SPV).
    { apply (stk_merge psegs m1 lo (SPV + -176) SPV STK); [|lia].
      apply (stk_merge psegs m1 (SPV + -176) (SPV + -104) SPV); [replace (SPV + -104) with (SPV + -176 + Z.of_nat 72) by lia; exact F0| |lia].
      replace SPV with (SPV + -104 + Z.of_nat 104) at 2 by lia. exact FSAV. }
    zstep. apply evt_done. unfold huf_rd_post.
    do 14 eexists. exists m1, r, dtb'.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact STK'|].
    split; [exact WKS|]. split; [exact DTC|]. split; [exact HDR'|]. split; [exact RR| exact RES].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section P2.
  Variables (fa fb wn wt : word) (f2 f3 f4 f5 f6 f7 : list byte) (hw rank : list Z) (nbs tl r0 hdw : Z).
  Notation FL0 := [CB 8 f2; CB 8 f3; CB 8 f4; CB 8 f5; CB 8 f6; CB 8 f7].
  Hypothesis STOK : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBR : 2 <= nbs <= 256.  Hypothesis R0R : 1 <= r0 <= n.  Hypothesis WK1492 : 1492 <= wksz.
  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis HWBY : Forall isbyte hw.  Hypothesis RKLEN : Z.of_nat (length rank) = 13.

  (* [comment removed for export] *)
  Definition X1S (fl : list cell) (dt rst : list Z) (syb : list byte) (m1 : fmem) : Prop :=
    u8arr psegs m1 DT (map (Z_to_bv 8) dt) /\ Z.of_nat (length dt) = 16388 /\ Forall isbyte dt
    /\ u8arr psegs m1 (WK + 1236) (map (Z_to_bv 8) hw)
    /\ u32arr psegs m1 WK (map (Z_to_bv 64) rank)
    /\ u32arr psegs m1 (WK + 52) (map (Z_to_bv 64) rst) /\ Z.of_nat (length rst) = 13
    /\ stk psegs m1 (WK + 104) (WK + 980)
    /\ u8arr psegs m1 (WK + 980) syb /\ Z.of_nat (length syb) = 256
    /\ stk psegs m1 (WK + 1492) (WK + wksz)
    /\ rw_cells psegs m1 (SPV + -176) (C8 fa :: C8 fb :: fl) /\ cells_size fl = 48%nat
    /\ rw_cells psegs m1 (SPV + -112) [C4 wn; C4 wt]
    /\ rw_cells psegs m1 (SPV + -104) SAVED /\ stk psegs m1 lo (SPV + -176)
    /\ mem_inv psegs m1 /\ munch MUNCH m m1 /\ wmono psegs m m1.
  Ltac open_x1s I := destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold X1S, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.

  (* [comment removed for export] *)
  Notation STS2 pc mm x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) x10 x11 x12 x13 x14 x15 x16 x17
         (Z_to_bv 64 (WK + 1236)) x19 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 tl) x24 x25 x26 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_rstart : forall j m1 fl dt rst syb k p15 x1 x5 x6 x7 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat (tl + 1 - k) = j -> X1S fl dt rst syb m1 -> 0 <= k <= tl -> p15 = WK + 4 * k ->
    (forall v, 0 <= v < k -> Znth v rst = xsym rank v) ->
    (forall m2 rst' y17, X1S fl dt rst' syb m2 -> (forall v, 0 <= v <= tl -> Znth v rst' = xsym rank v) ->
       evt psegs POST (STS2 0x1cae8 m2 x1 x5 x6 x7 (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (xsym rank (tl + 1))) (Z_to_bv 64 (nbs + -3))
                            (Z_to_bv 64 (WK + 4 * (tl + 1))) (Z_to_bv 64 (WK + 4 * (tl + 1))) (Z_to_bv 64 ((tl + 1) * 4294967296)) y17
                            x19 x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (STS2 0x1cad4 m1 x1 x5 x6 x7 (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (xsym rank k)) (Z_to_bv 64 (nbs + -3))
                         (Z_to_bv 64 (WK + 4 * (tl + 1))) (Z_to_bv 64 p15) (Z_to_bv 64 ((tl + 1) * 4294967296)) x17
                         x19 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I KR EP PRE KONT; [exfalso; lia|]. subst p15.
    open_x1s I. pose proof STOK as (TLR & _).
    pose proof (st_rank_nonneg _ _ _ STOK k ltac:(lia)) as RK0.
    assert (RKB : Znth k rank <= 256).
    { pose proof (xsym_step rank k ltac:(lia)) as S1. pose proof (xsym_mono _ _ _ STOK (k + 1) 13 ltac:(lia) ltac:(lia)) as S2.
      pose proof (xsym_nonneg _ _ _ STOK k ltac:(lia)) as S3. rewrite (xsym_total _ _ _ STOK) in S2.
      unfold FseNCount.Zlength in S2. rewrite length_firstn in S2. lia. }
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 WK rank k a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep. rewrite (sx32w_small (Znth k rank)) by lia.
    u32st2 RST k (xsym rank k) (xsym rank k).
    change (upd_nat (Z.to_nat k) (xsym rank k) rst) with (Zupd k (xsym rank k) rst) in RST.
    zstep. zstep.
    assert (XS : Znth k rank + xsym rank k = xsym rank (k + 1)) by (rewrite (xsym_step rank k) by lia; lia).
    rewrite XS.
    assert (PRE' : forall v, 0 <= v < k + 1 -> Znth v (Zupd k (xsym rank k) rst) = xsym rank v).
    { intros v Hv. destruct (Z.eq_dec v k) as [->|NE].
      - apply Znth_Zupd_same. unfold FseNCount.Zlength. lia.
      - rewrite Znth_Zupd_other by lia. apply PRE. lia. }
    assert (I' : X1S fl dt (Zupd k (xsym rank k) rst) syb m0).
    { assert (RSTLEN' : Z.of_nat (length (Zupd k (xsym rank k) rst)) = 13) by (rewrite Zupd_length; exact RSTLEN). close_x1s. }
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 4 * k + 4)) with (Z_to_bv 64 (WK + 4 * (k + 1))) by (f_equal; lia).
      eapply (IH m0 fl dt _ syb (k + 1) (WK + 4 * (k + 1))); [lia | exact I' | lia | reflexivity | exact PRE' | exact KONT].
    - assert (EK : k = tl) by lia. subst k.
      replace (Z_to_bv 64 (WK + 4 * tl + 4)) with (Z_to_bv 64 (WK + 4 * (tl + 1))) by (f_equal; lia).
      eapply KONT; [exact I'|]. intros v Hv. apply PRE'. lia.
  Qed.

  (* [comment removed for export] *)
  Notation ws := (firstn (Z.to_nat nbs) hw).
  Lemma ws_len : FseNCount.Zlength ws = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i ws = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Definition SORT (i : Z) (rst : list Z) : Prop :=
    forall v, 0 <= v <= tl -> Znth v rst = xsym rank v + hcount (firstn (Z.to_nat i) ws) v.

  (* [comment removed for export] *)
  Definition KFILL (dt : list Z) : Prop :=
    forall m2 rst syb x1 x5 x6 x7 x13 x14 x15 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
      X1S FL0 dt rst syb m2 ->
      evt psegs POST (STF 0x1cbcc m2 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (WK + 980))
                          x13 x14 x15 (Z_to_bv 64 ((tl + 1) * 4294967296)) x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_sort_tail : forall j m1 dt rst syb i x1 x5 x6 x7 x13 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    KFILL dt -> Z.to_nat (nbs - i) = j -> X1S FL0 dt rst syb m1 -> 0 <= i < nbs -> SORT i rst ->
    evt psegs POST (STS2 0x1cba0 m1 x1 x5 x6 x7 (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (WK + 980)) x13
                         (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 i) (Z_to_bv 64 ((tl + 1) * 4294967296)) x17
                         x19 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KF EJ I IR INV; [exfalso; lia|].
    open_x1s I. pose proof STOK as (TLR & _).
    destruct (sort_slot _ _ _ STOK i (Znth i hw) ltac:(rewrite ws_len; lia) (ws_nth i IR)) as (WR & SLOT). rewrite ws_len in SLOT.
    pose proof (sort_step _ _ _ STOK i (Znth i hw) rst ltac:(rewrite ws_len; lia) (ws_nth i IR) ltac:(unfold FseNCount.Zlength; lia) INV) as INV'.
    rewrite <- (INV (Znth i hw) WR) in SLOT.
    remember (Znth i hw) as w eqn:EW.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth psegs m1 (WK + 1236) hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite <- EW in RD.
    zstep. cbv beta. rewrite (byte_lit w) by lia.
    zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 (WK + 52) rst w a RST ltac:(lia) ltac:(addr_tac)) as RD2 end.
    zstep.
    rewrite (zx32w_small (Znth w rst)) by lia.
    zstep. zstep.
    u32st2 RST w (Znth w rst + 1) (Znth w rst + 1).
    change (upd_nat (Z.to_nat w) (Znth w rst + 1) rst) with (Zupd w (Znth w rst + 1) rst) in RST.
    outst SYC SYLEN.
    assert (I' : X1S FL0 dt (Zupd w (Znth w rst + 1) rst) out m1).
    { assert (RSTLEN' : Z.of_nat (length (Zupd w (Znth w rst + 1) rst)) = 13) by (rewrite Zupd_length; exact RSTLEN). close_x1s. }
    zstep. zstep. if_cases KB; zify_cond KB.
    - eapply (IH m1 dt _ out (i + 1)); [exact KF | lia | exact I' | lia | exact INV'].
    - eapply KF. exact I'.
  Qed.

  (* [comment removed for export] *)
  Tactic Notation "sort_facts" constr(INV) constr(i) ident(w) ident(WR) ident(SLOT) ident(INV') ident(EW) :=
    lazymatch type of INV with SORT _ ?rs =>
      destruct (sort_slot _ _ _ STOK i (Znth i hw) ltac:(rewrite ws_len; lia) (ws_nth i ltac:(lia))) as (WR & SLOT); rewrite ws_len in SLOT;
      pose proof (sort_step _ _ _ STOK i (Znth i hw) rs ltac:(rewrite ws_len; lia) (ws_nth i ltac:(lia))
                    ltac:(unfold FseNCount.Zlength; rewrite ?Zupd_length; lia) INV) as INV';
      change (SORT (i + 1) (Zupd (Znth i hw) (Znth (Znth i hw) rs + 1) rs)) in INV';
      rewrite <- (INV (Znth i hw) WR) in SLOT;
      remember (Znth i hw) as w eqn:EW
    end.
  (* [comment removed for export] *)
  Tactic Notation "sort_mach" hyp(HWC) hyp(RST) hyp(SYC) hyp(SYLEN) constr(i) constr(w) hyp(EW) integer(k) :=
    let RD := fresh "RD" in let RD2 := fresh "RD" in
    lazymatch type of HWC with u8arr _ ?mm _ _ =>
      (lazymatch goal with |- _ => let a := cur_mem_addr in
        pose proof (u8_znth psegs mm (WK + 1236) hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end);
      rewrite <- EW in RD;
      zstep; cbv beta; rewrite (byte_lit w) by lia; clear RD;
      zstep; replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
      zstep;
      lazymatch type of RST with u32arr _ _ _ (map _ ?rs) =>
        (lazymatch goal with |- _ => let a := cur_mem_addr in
          pose proof (u32_znth psegs mm (WK + 52) rs w a RST ltac:(rewrite ?Zupd_length; lia) ltac:(addr_tac)) as RD2 end);
        zstep; rewrite (zx32w_small (Znth w rs)) by lia; clear RD2;
        do k zstep;
        u32st2 RST w (Znth w rs + 1) (Znth w rs + 1);
        change (upd_nat (Z.to_nat w) (Znth w rs + 1) rs) with (Zupd w (Znth w rs + 1) rs) in RST;
        outst SYC SYLEN;
        let rsn := fresh "rst" in let ER := fresh "ER" in let RL := fresh "RSTLEN" in
        remember (Zupd w (Znth w rs + 1) rs) as rsn eqn:ER;
        assert (RL : Z.of_nat (length rsn) = 13) by (subst rsn; rewrite Zupd_length; assumption);
        clear ER
      end
    end.

  (* [comment removed for export] *)
  Lemma x1_sort4 : forall j m1 dt rst syb i x1 x5 x6 x7 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    KFILL dt -> (Z.to_nat (nbs - i) <= j)%nat -> X1S FL0 dt rst syb m1 -> 0 <= i -> i + 3 < nbs -> SORT i rst ->
    evt psegs POST (STS2 0x1cb00 m1 x1 x5 x6 x7 (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (WK + 980)) (Z_to_bv 64 (nbs + -3))
                         (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 i) (Z_to_bv 64 ((tl + 1) * 4294967296)) (Z_to_bv 64 i)
                         x19 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KF EJ I I0 I3 INV; [exfalso; lia|].
    open_x1s I. pose proof STOK as (TLR & _).
    zstep.
    sort_facts INV i w0 WR0 SLOT0 INV1 EW0.
    sort_mach HWC RST SYC SYLEN i w0 EW0 2.
    sort_facts INV1 (i + 1) w1 WR1 SLOT1 INV2 EW1.
    sort_mach HWC RST SYC SYLEN (i + 1) w1 EW1 3.
    sort_facts INV2 (i + 1 + 1) w2 WR2 SLOT2 INV3 EW2.
    sort_mach HWC RST SYC SYLEN (i + 1 + 1) w2 EW2 3.
    sort_facts INV3 (i + 1 + 1 + 1) w3 WR3 SLOT3 INV4 EW3.
    sort_mach HWC RST SYC SYLEN (i + 1 + 1 + 1) w3 EW3 4.
    replace (i + 1 + 1 + 1 + 1) with (i + 4) in INV4 by lia.
    assert (I' : X1S FL0 dt rst3 out2 m1) by (clear RSTLEN RSTLEN0 RSTLEN1 RSTLEN2; close_x1s).
    zstep. rewrite (swrap32_small (i + 4)) by lia.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH m1 dt rst3 out2 (i + 4)); [exact KF | lia | exact I' | lia | lia | exact INV4].
    - zstep. if_cases KC; zify_lts KC.
      + eapply KF. exact I'.
      + eapply (x1_sort_tail (Z.to_nat (nbs - (i + 4))) m1 dt rst3 out2 (i + 4)); [exact KF | reflexivity | exact I' | lia | exact INV4].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_sort : forall m1 dt rst syb x1 x5 x6 x7 x12 x14 x15 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    KFILL dt -> X1S FL0 dt rst syb m1 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
    evt psegs POST (STS2 0x1cae8 m1 x1 x5 x6 x7 (Z_to_bv 64 r0) (Z_to_bv 64 (tl + 1)) x12 (Z_to_bv 64 (nbs + -3))
                         x14 x15 (Z_to_bv 64 ((tl + 1) * 4294967296)) x17 x19 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KF I RS0.
    assert (INV : SORT 0 rst) by (intros v Hv; rewrite (RS0 v Hv); change (Z.to_nat 0) with 0%nat; cbn [firstn]; rewrite hcount_nil; lia).
    zstep. zstep. zstep. zstep. if_cases KA; zify_lts KA.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases KB; zify_lts KB; [|exfalso; lia].
      eapply (x1_sort_tail (Z.to_nat (nbs - 0)) m1 dt rst syb 0); [exact KF | reflexivity | exact I | lia | exact INV].
    - zstep. zstep.
      eapply (x1_sort4 (Z.to_nat (nbs - 0)) m1 dt rst syb 0); [exact KF | lia | exact I | lia | lia | exact INV].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma rank_le : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= nbs.
  Proof.
    intros v Hv. destruct STOK as (_ & _ & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
    pose proof (count_occ_bound Z.eq_dec v ws) as CB. pose proof ws_len as WL. unfold FseNCount.Zlength in WL. lia.
  Qed.

  (* [comment removed for export] *)
  Definition PREF (cur : Z) (dt : list Z) : Prop :=
    Znth 0 dt = 12 /\ Znth 1 dt = 0 /\ Znth 2 dt = tl /\ forall u, 0 <= u < cur -> 0 <= Znth (4 + 2 * u) dt <= 12.

  Lemma pref_extend : forall cur len dt dt', PREF cur dt -> 0 <= cur -> 0 <= len ->
    (forall j, 0 <= j < 4 + 2 * cur -> Znth j dt' = Znth j dt) ->
    (forall u, cur <= u < cur + len -> 0 <= Znth (4 + 2 * u) dt' <= 12) -> PREF (cur + len) dt'.
  Proof.
    intros cur len dt dt' (H0 & H1 & H2 & HP) Hc Hl SAME NEW.
    split; [rewrite SAME by lia; exact H0|]. split; [rewrite SAME by lia; exact H1|]. split; [rewrite SAME by lia; exact H2|].
    intros u Hu. destruct (Z.lt_ge_cases u cur) as [LT|GE]; [rewrite SAME by lia; apply HP; lia | apply NEW; lia].
  Qed.

  (* [comment removed for export] *)
  Notation FLF := [C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 (DT + 20)); C8 (Z_to_bv 64 (DT + 5)); C8 (Z_to_bv 64 (DT + 7));
                   C8 (Z_to_bv 64 (DT + 4)); C8 (Z_to_bv 64 (DT + 12))].
  (* [comment removed for export] *)
  Notation STFL pc mm x1 x5 x6 x7 x13 x14 x15 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31 :=
    (STF pc mm x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 3) (Z_to_bv 64 (tl + 1)) (Z_to_bv 64 (WK + 980)) x13 x14 x15
         (Z_to_bv 64 (tl + 1)) x17 x18 (Z_to_bv 64 281479271743489) x20 x21 x22 x23 x24 x25 x26 x27 x28 (Z_to_bv 64 1) x30 x31).

  Section FILLW.
  Variables (rst : list Z) (w cur sym count len nb : Z).
  Hypothesis NBR12 : 1 <= nb <= 12.
  Hypothesis SLOTS : forall s, 0 <= s < count -> 0 <= sym + s < 256 /\ 0 <= cur + s * len /\ cur + s * len + len <= 4096.
  Hypothesis CUR0 : 0 <= cur.

  (* [comment removed for export] *)
  Definition KLATCH : Prop :=
    forall m2 dt' syb' x1 x5 x6 x7 x13 x17 x18 x23 x24 x25 x26 x27 x28 x30 x31,
      X1S FLF dt' rst syb' m2 -> PREF (cur + count * len) dt' ->
      evt psegs POST (STFL 0x1cc2c m2 x1 x5 x6 x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18 (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                           x23 x24 x25 x26 x27 x28 x30 x31).

  (* [comment removed for export] *)
  Lemma x1_fill1 : forall j m1 dt syb s x1 x5 x7 x13 x17 x18 x25 x26 x27 x30 x31,
    KLATCH -> len = 1 -> Z.to_nat (count - s) = j -> X1S FLF dt rst syb m1 -> PREF (cur + s) dt -> 0 <= s < count ->
    evt psegs POST (STFL 0x1ce88 m1 x1 x5 (Z_to_bv 64 (WK + 980 + sym + s)) x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len) (Z_to_bv 64 (DT + 5 + 2 * (cur + count))) (Z_to_bv 64 nb) x25 x26 x27
                         (Z_to_bv 64 (DT + 5 + 2 * (cur + s))) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB.
    replace (Z_to_bv 64 (DT + 5 + 2 * (cur + s))) with (Z_to_bv 64 (DT + (4 + 2 * (cur + s)) + 1)) by (f_equal; lia).
    u8_sok DTC (4 + 2 * (cur + s)). zstep. u8_store DTC (4 + 2 * (cur + s)) nb; [reflexivity|].
    lazymatch goal with |- _ => let v := reg_val 25 in lazymatch v with Z_to_bv 64 ?e =>
      let sv := fresh "sv" in let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
    u8_sok DTC (4 + 2 * (cur + s) + 1). zstep. u8_store DTC (4 + 2 * (cur + s) + 1) sv; [reflexivity|].
    destruct (SLOTS (count - 1) ltac:(lia)) as (_ & _ & CE). rewrite L1 in CE.
    remember (Zupd (4 + 2 * (cur + s) + 1) sv (Zupd (4 + 2 * (cur + s)) nb dt)) as dt' eqn:EDT'.
    assert (DTLEN' : Z.of_nat (length dt') = 16388) by (subst dt'; rewrite !Zupd_length; exact DTLEN).
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : PREF (cur + s + 1) dt').
    { subst dt'. apply (pref_extend (cur + s) 1 dt); [exact PR | lia | lia | |].
      - intros j0 Hj. rewrite !Znth_Zupd_other by lia. reflexivity.
      - intros u Hu. assert (EU : u = cur + s) by lia. subst u.
        rewrite Znth_Zupd_other by lia. rewrite Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). lia. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLF dt' rst syb m1) by close_x1s.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (DT + (4 + 2 * (cur + s)) + 3)) with (Z_to_bv 64 (DT + 5 + 2 * (cur + (s + 1)))) by (f_equal; lia).
      replace (Z_to_bv 64 (WK + 980 + sym + s + 1)) with (Z_to_bv 64 (WK + 980 + sym + (s + 1))) by (f_equal; lia).
      replace (cur + s + 1) with (cur + (s + 1)) in PR' by lia.
      eapply (IH m1 dt' syb (s + 1)); [exact KL | exact L1 | lia | exact I' | exact PR' | lia].
    - assert (ES : s + 1 = count) by lia.
      zstep. eapply KL; [exact I'|]. rewrite L1. replace (cur + count * 1) with (cur + s + 1) by lia. exact PR'.
  Qed.

  (* [comment removed for export] *)
  Ltac getbyte r sv SVR :=
    lazymatch goal with |- _ => let v := reg_val r in lazymatch v with Z_to_bv 64 ?e =>
      let ESV := fresh "ESV" in remember e as sv eqn:ESV;
      assert (SVR : 0 <= sv < 256) by (subst sv; match goal with |- 0 <= bv_unsigned ?b < 256 => let X := fresh "X" in pose proof (bv_unsigned_in_range 8 b) as X; unfold bv_modulus in X; cbn in X; lia end);
      clear ESV end end.
  (* [comment removed for export] *)
  Ltac dtst DTC i v := u8_sok DTC i; zstep; u8_store DTC i v; [first [reflexivity | rewrite Z.mod_mod by lia; reflexivity | lia]|].
  (* [comment removed for export] *)
  Ltac znth_upd :=
    repeat match goal with |- context [Znth ?j (Zupd ?i ?v ?l)] =>
      first [ rewrite (Znth_Zupd_other i j v l) by lia
            | replace j with i by lia; rewrite (Znth_Zupd_same i v l) by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia) ] end.

  (* [comment removed for export] *)
  Lemma x1_fill2 : forall j m1 dt syb s x1 x5 x7 x17 x18 x25 x26 x27 x30 x31,
    KLATCH -> len = 2 -> Z.to_nat (count - s) = j -> X1S FLF dt rst syb m1 -> PREF (cur + 2 * s) dt -> 0 <= s < count ->
    evt psegs POST (STFL 0x1cc84 m1 x1 x5 (Z_to_bv 64 (WK + 980 + sym + s)) x7 (Z_to_bv 64 (DT + 7)) (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len) (Z_to_bv 64 (WK + 980 + sym + count)) (Z_to_bv 64 nb) x25 x26 x27
                         (Z_to_bv 64 (DT + 7 + 2 * (cur + 2 * s))) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    destruct (SLOTS (count - 1) ltac:(lia)) as (SYE & _ & CE). rewrite L1 in CE.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 25 sv SVR.
    zstep.
    dtst DTC (4 + 2 * (cur + 2 * s)) nb.
    dtst DTC (4 + 2 * (cur + 2 * s) + 1) sv.
    dtst DTC (4 + 2 * (cur + 2 * s) + 2) nb.
    dtst DTC (4 + 2 * (cur + 2 * s) + 3) sv.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = 16388) by (subst dt'; rewrite !Zupd_length; exact DTLEN).
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : PREF (cur + 2 * s + 2) dt').
    { subst dt'. apply (pref_extend (cur + 2 * s) 2 dt); [exact PR | lia | lia | |].
      - intros j0 Hj. rewrite !Znth_Zupd_other by lia. reflexivity.
      - intros u Hu. assert (EU : u = cur + 2 * s \/ u = cur + 2 * s + 1) by lia.
        destruct EU as [-> | ->]; znth_upd; lia. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLF dt' rst syb m1) by close_x1s.
    zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 980 + sym + s + 1)) with (Z_to_bv 64 (WK + 980 + sym + (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 28 in replace v with (Z_to_bv 64 (DT + 7 + 2 * (cur + 2 * (s + 1)))) by (f_equal; lia) end.
      replace (cur + 2 * s + 2) with (cur + 2 * (s + 1)) in PR' by lia.
      eapply (IH m1 dt' syb (s + 1)); [exact KL | exact L1 | lia | exact I' | exact PR' | lia].
    - zstep. eapply KL; [exact I'|]. rewrite L1. replace (cur + count * 2) with (cur + 2 * s + 2) by lia. exact PR'.
  Qed.

  (* [comment removed for export] *)
  Ltac dtstB DTC i v BH := u8_sok DTC i; zstep; u8_store DTC i v; [unfold hidden in BH; rewrite BH; symmetry; apply Z.mod_small; lia|].

  (* [comment removed for export] *)
  Lemma x1_fill4 : forall j m1 dt syb s x1 x5 x7 x13 x17 x18 x25 x26 x27 x30 x31,
    KLATCH -> len = 4 -> Z.to_nat (count - s) = j -> X1S FLF dt rst syb m1 -> PREF (cur + 4 * s) dt -> 0 <= s < count ->
    evt psegs POST (STFL 0x1cec8 m1 x1 x5 (Z_to_bv 64 nb) x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len) (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * s))) (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * count))) x25 x26 x27
                         (Z_to_bv 64 (WK + 980 + sym + s)) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    destruct (SLOTS (count - 1) ltac:(lia)) as (SYE & _ & CE). rewrite L1 in CE.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 25 sv SVR.
    zstep. zstep. zstep.
    change (Z.lor (sv ≪ 8 mod 18446744073709551616) nb * 281479271743489) with (d4 sv nb).
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    do 6 zstep. rewrite ?(Z.mod_small D 18446744073709551616) by lia.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 4) nb B4.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 5) sv B5.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 6) nb B6.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 7) sv B7.
    zstep.
    replace (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * s))) with (Z_to_bv 64 (DT + (4 + 2 * (cur + 4 * s)) + 0)) by (f_equal; lia).
    dtstB DTC (4 + 2 * (cur + 4 * s)) nb B0.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 1) sv B1.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 2) nb B2.
    dtstB DTC (4 + 2 * (cur + 4 * s) + 3) sv B3.
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = 16388) by (subst dt'; rewrite !Zupd_length; exact DTLEN).
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : PREF (cur + 4 * s + 4) dt').
    { subst dt'. apply (pref_extend (cur + 4 * s) 4 dt); [exact PR | lia | lia | |].
      - intros j0 Hj. rewrite !Znth_Zupd_other by lia. reflexivity.
      - intros u Hu. assert (EU : u = cur + 4 * s \/ u = cur + 4 * s + 1 \/ u = cur + 4 * s + 2 \/ u = cur + 4 * s + 3) by lia.
        destruct EU as [-> | [-> | [-> | ->]]]; znth_upd; lia. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLF dt' rst syb m1) by close_x1s.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 980 + sym + s + 1)) with (Z_to_bv 64 (WK + 980 + sym + (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 23 in replace v with (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * (s + 1)))) by (f_equal; lia) end.
      replace (cur + 4 * s + 4) with (cur + 4 * (s + 1)) in PR' by lia.
      eapply (IH m1 dt' syb (s + 1)); [exact KL | exact L1 | lia | exact I' | exact PR' | lia].
    - zstep. eapply KL; [exact I'|]. rewrite L1. replace (cur + count * 4) with (cur + 4 * s + 4) by lia. exact PR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_fill8 : forall j m1 dt syb s x1 x5 x7 x13 x17 x18 x25 x26 x27 x30 x31,
    KLATCH -> len = 8 -> Z.to_nat (count - s) = j -> X1S FLF dt rst syb m1 -> PREF (cur + 8 * s) dt -> 0 <= s < count ->
    evt psegs POST (STFL 0x1ccdc m1 x1 x5 (Z_to_bv 64 nb) x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len) (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * s))) (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * count))) x25 x26 x27
                         (Z_to_bv 64 (WK + 980 + sym + s)) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L1 EJ I PR SR; [exfalso; lia|].
    open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1). rewrite L1 in C0, C1.
    destruct (SLOTS (count - 1) ltac:(lia)) as (SYE & _ & CE). rewrite L1 in CE.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 13 sv SVR.
    zstep. zstep. zstep.
    change (Z.lor (sv ≪ 8 mod 18446744073709551616) nb * 281479271743489) with (d4 sv nb).
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    do 7 zstep. rewrite ?(Z.mod_small D 18446744073709551616) by lia.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    remember (4 + 2 * (cur + 8 * s)) as bs eqn:EBS.
    replace (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * s))) with (Z_to_bv 64 (DT + bs + 8)) by (f_equal; lia).
    dtstB DTC (bs + 4) nb B4.
    dtstB DTC (bs + 5) sv B5.
    dtstB DTC (bs + 6) nb B6.
    dtstB DTC (bs + 7) sv B7.
    replace (Z_to_bv 64 (DT + bs + 8)) with (Z_to_bv 64 (DT + bs + 0 + 8)) by (f_equal; lia).
    dtstB DTC (bs + 0) nb B0.
    dtstB DTC (bs + 1) sv B1.
    dtstB DTC (bs + 2) nb B2.
    dtstB DTC (bs + 3) sv B3.
    dtstB DTC (bs + 12) nb B4.
    dtstB DTC (bs + 13) sv B5.
    dtstB DTC (bs + 14) nb B6.
    dtstB DTC (bs + 15) sv B7.
    dtstB DTC (bs + 8) nb B0.
    dtstB DTC (bs + 9) sv B1.
    dtstB DTC (bs + 10) nb B2.
    dtstB DTC (bs + 11) sv B3.
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = 16388) by (subst dt'; rewrite !Zupd_length; exact DTLEN).
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : PREF (cur + 8 * s + 8) dt').
    { subst dt'. apply (pref_extend (cur + 8 * s) 8 dt); [exact PR | lia | lia | |].
      - intros j0 Hj. rewrite !Znth_Zupd_other by lia. reflexivity.
      - intros u Hu.
        assert (EU : u = cur + 8 * s \/ u = cur + 8 * s + 1 \/ u = cur + 8 * s + 2 \/ u = cur + 8 * s + 3 \/ u = cur + 8 * s + 4
                     \/ u = cur + 8 * s + 5 \/ u = cur + 8 * s + 6 \/ u = cur + 8 * s + 7) by lia.
        clear - EU DTLEN NBR12 C0 C1 CUR0 EBS.
        destruct EU as [-> | [-> | [-> | [-> | [-> | [-> | [-> | ->]]]]]]]; znth_upd; lia. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLF dt' rst syb m1) by close_x1s.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 980 + sym + s + 1)) with (Z_to_bv 64 (WK + 980 + sym + (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 23 in replace v with (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * (s + 1)))) by (f_equal; lia) end.
      replace (cur + 8 * s + 8) with (cur + 8 * (s + 1)) in PR' by lia.
      eapply (IH m1 dt' syb (s + 1)); [exact KL | exact L1 | lia | exact I' | exact PR' | lia].
    - zstep. eapply KL; [exact I'|]. rewrite L1. replace (cur + count * 8) with (cur + 8 * s + 8) by lia. exact PR'.
  Qed.

  (* [comment removed for export] *)
  Definition KSYM (s off : Z) : Prop :=
    forall m2 dt' syb' x1 x5 x6 x7 x13 x17 x18 x26 x30 x31,
      X1S FLF dt' rst syb' m2 -> PREF (cur + off + len) dt' ->
      evt psegs POST (STFL 0x1cd88 m2 x1 x5 x6 x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18 (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                           (Z_to_bv 64 s) (Z_to_bv 64 nb) (Z_to_bv 64 (2 * len)) x26 (Z_to_bv 64 (2 * cur + 2 * len + 20))
                           (Z_to_bv 64 (DT + 20 + 2 * (cur + off))) x30 x31).

  Lemma x1_fillD_in : forall j m1 dt syb s off q Q D sv x5 x7 x13 x17 x18 x30 x31,
    KSYM s off -> len = 16 * Q -> Z.to_nat (Q - q) = j -> X1S FLF dt rst syb m1 -> PREF (cur + off + 16 * q) dt ->
    0 <= off -> cur + off + len <= 4096 -> 0 <= q < Q -> 0 <= sv < 256 ->
    0 <= D < 18446744073709551616 -> D mod 256 = nb -> (D ≫ 8) mod 256 = sv -> (D ≫ 16) mod 256 = nb -> (D ≫ 24) mod 256 = sv ->
    (D ≫ 32) mod 256 = nb -> (D ≫ 40) mod 256 = sv -> (D ≫ 48) mod 256 = nb -> (D ≫ 56) mod 256 = sv ->
    evt psegs POST (STFL 0x1cdc0 m1 (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 2 * len)) x5 (Z_to_bv 64 D) x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                         (Z_to_bv 64 s) (Z_to_bv 64 nb) (Z_to_bv 64 (2 * len)) (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 32 * q)) (Z_to_bv 64 (2 * cur + 2 * len + 20))
                         (Z_to_bv 64 (DT + 20 + 2 * (cur + off))) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KS L16 EJ I PR OFF0 OFFH QR SVR DR B0 B1 B2 B3 B4 B5 B6 B7; [exfalso; lia|].
    open_x1s I.
    hide B0. hide B1. hide B2. hide B3. hide B4. hide B5. hide B6. hide B7.
    do 7 zstep.
    remember (4 + 2 * (cur + off + 16 * q)) as bs eqn:EBS.
    replace (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 32 * q)) with (Z_to_bv 64 (DT + bs + 16)) by (f_equal; lia).
    dtstB DTC (bs + 4) nb B4.
    dtstB DTC (bs + 5) sv B5.
    dtstB DTC (bs + 6) nb B6.
    dtstB DTC (bs + 7) sv B7.
    dtstB DTC (bs + 0) nb B0.
    dtstB DTC (bs + 1) sv B1.
    dtstB DTC (bs + 2) nb B2.
    dtstB DTC (bs + 3) sv B3.
    dtstB DTC (bs + 12) nb B4.
    dtstB DTC (bs + 13) sv B5.
    dtstB DTC (bs + 14) nb B6.
    dtstB DTC (bs + 15) sv B7.
    dtstB DTC (bs + 8) nb B0.
    dtstB DTC (bs + 9) sv B1.
    dtstB DTC (bs + 10) nb B2.
    dtstB DTC (bs + 11) sv B3.
    dtstB DTC (bs + 20) nb B4.
    dtstB DTC (bs + 21) sv B5.
    dtstB DTC (bs + 22) nb B6.
    dtstB DTC (bs + 23) sv B7.
    dtstB DTC (bs + 16) nb B0.
    dtstB DTC (bs + 17) sv B1.
    dtstB DTC (bs + 18) nb B2.
    dtstB DTC (bs + 19) sv B3.
    dtstB DTC (bs + 28) nb B4.
    dtstB DTC (bs + 29) sv B5.
    dtstB DTC (bs + 30) nb B6.
    dtstB DTC (bs + 31) sv B7.
    dtstB DTC (bs + 24) nb B0.
    dtstB DTC (bs + 25) sv B1.
    dtstB DTC (bs + 26) nb B2.
    dtstB DTC (bs + 27) sv B3.
    pose proof B0 as B0'. pose proof B1 as B1'. pose proof B2 as B2'. pose proof B3 as B3'. pose proof B4 as B4'. pose proof B5 as B5'. pose proof B6 as B6'. pose proof B7 as B7'.
    clear B0 B1 B2 B3 B4 B5 B6 B7.
    lazymatch type of DTC with u8arr _ _ _ (map _ ?d) => remember d as dt' eqn:EDT' end.
    assert (DTLEN' : Z.of_nat (length dt') = 16388) by (subst dt'; rewrite !Zupd_length; exact DTLEN).
    assert (DTBY' : Forall isbyte dt') by (subst dt'; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
    assert (PR' : PREF (cur + off + 16 * q + 16) dt').
    { subst dt'. apply (pref_extend (cur + off + 16 * q) 16 dt); [exact PR | lia | lia | |].
      - intros j0 Hj. rewrite !Znth_Zupd_other by lia. reflexivity.
      - intros u Hu. remember (cur + off + 16 * q) as c0 eqn:EC0.
        assert (EU : u = c0 \/ u = c0 + 1 \/ u = c0 + 2 \/ u = c0 + 3 \/ u = c0 + 4 \/ u = c0 + 5 \/ u = c0 + 6 \/ u = c0 + 7
                     \/ u = c0 + 8 \/ u = c0 + 9 \/ u = c0 + 10 \/ u = c0 + 11 \/ u = c0 + 12 \/ u = c0 + 13 \/ u = c0 + 14 \/ u = c0 + 15) by lia.
        clear Hu. assert (EB : bs = 4 + 2 * c0) by lia. assert (C0R : 0 <= c0 /\ c0 + 16 <= 4096) by lia. clear EBS EC0.
        clear - EU EB C0R DTLEN NBR12.
        repeat (destruct EU as [-> | EU]; [znth_upd; lia|]). subst u. znth_upd. lia. }
    clear EDT' DTLEN DTBY.
    assert (I' : X1S FLF dt' rst syb m1) by close_x1s.
    zstep. zstep. if_cases KB; zify_cond KB.
    - lazymatch goal with |- _ => let v := reg_val 26 in replace v with (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 32 * (q + 1))) by (f_equal; lia) end.
      replace (cur + off + 16 * q + 16) with (cur + off + 16 * (q + 1)) in PR' by lia.
      unfold hidden in B0', B1', B2', B3', B4', B5', B6', B7'.
      assert (EJ' : Z.to_nat (Q - (q + 1)) = j) by (clear - EJ QR; lia).
      assert (QR' : 0 <= q + 1 < Q) by (first [clear - QR KB L16 EJ; lia | lia]).
      clear DTC.
      eapply (IH m1 dt' syb s off (q + 1) Q D sv);
        [exact KS | exact L16 | exact EJ' | exact I' | exact PR' | exact OFF0 | exact OFFH | exact QR' | exact SVR | exact DR
        | exact B0' | exact B1' | exact B2' | exact B3' | exact B4' | exact B5' | exact B6' | exact B7'].
    - zstep. eapply KS; [exact I'|]. replace (cur + off + len) with (cur + off + 16 * q + 16) by lia. exact PR'.
  Qed.

  Lemma x1_fillD_in' : forall m1 dt syb s off Q D sv p26 x5 x7 x13 x17 x18 x30 x31,
    KSYM s off -> len = 16 * Q -> 0 < Q -> X1S FLF dt rst syb m1 -> PREF (cur + off) dt ->
    0 <= off -> cur + off + len <= 4096 -> 0 <= sv < 256 ->
    0 <= D < 18446744073709551616 -> D mod 256 = nb -> (D ≫ 8) mod 256 = sv -> (D ≫ 16) mod 256 = nb -> (D ≫ 24) mod 256 = sv ->
    (D ≫ 32) mod 256 = nb -> (D ≫ 40) mod 256 = sv -> (D ≫ 48) mod 256 = nb -> (D ≫ 56) mod 256 = sv ->
    p26 = DT + 20 + 2 * (cur + off) ->
    evt psegs POST (STFL 0x1cdc0 m1 (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 2 * len)) x5 (Z_to_bv 64 D) x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18
                         (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                         (Z_to_bv 64 s) (Z_to_bv 64 nb) (Z_to_bv 64 (2 * len)) (Z_to_bv 64 p26) (Z_to_bv 64 (2 * cur + 2 * len + 20))
                         (Z_to_bv 64 (DT + 20 + 2 * (cur + off))) x30 x31).
  Proof.
    intros until x31; intros KS L16 Q1 I PR OFF0 OFFH SVR DR B0 B1 B2 B3 B4 B5 B6 B7 EP.
    replace p26 with (DT + 20 + 2 * (cur + off) + 32 * 0) by lia.
    eapply (x1_fillD_in (Z.to_nat (Q - 0)) m1 dt syb s off 0 Q D sv); try eassumption; try lia.
    replace (cur + off + 16 * 0) with (cur + off) by lia. exact PR.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_fillD_sym : forall j m1 dt syb s Q x1 x5 x6 x7 x13 x17 x18 x26 x30 x31,
    KLATCH -> len = 16 * Q -> 1 <= Q -> Z.to_nat (count - s) = j -> X1S FLF dt rst syb m1 -> PREF (cur + len * s) dt -> 0 <= s < count ->
    evt psegs POST (STFL 0x1cd94 m1 x1 x5 x6 x7 x13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) x17 x18 (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                         (Z_to_bv 64 s) (Z_to_bv 64 nb) (Z_to_bv 64 (2 * len)) x26 (Z_to_bv 64 (2 * cur + 2 * len + 20))
                         (Z_to_bv 64 (DT + 20 + 2 * (cur + len * s))) x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KL L16 Q1 EJ I PR SR; [exfalso; lia|].
    pose proof I as I0. open_x1s I.
    destruct (SLOTS s SR) as (SY & C0 & C1).
    destruct (SLOTS (count - 1) ltac:(lia)) as (SYE & _ & _). destruct (SLOTS 0 ltac:(lia)) as (SY0 & _ & _).
    assert (CNTR : count <= 256) by lia.
    remember (len * s) as off eqn:EOFF.
    assert (OFFR : 0 <= off /\ cur + off + len <= 4096) by (subst off; split; [apply Z.mul_nonneg_nonneg; lia | lia]).
    zstep.
    if_cases KA; zify_lts KA; [exfalso; lia|].
    zstep. zstep.
    pose proof (proj1 SYC) as SYB. lbyte SYB. clear SYB. getbyte 13 sv SVR.
    zstep.
    replace (2 * len * s) with (2 * off) by (rewrite EOFF; ring).
    zstep. zstep. zstep. zstep. zstep. zstep.
    change (Z.lor (sv ≪ 8 mod 18446744073709551616) nb * 281479271743489) with (d4 sv nb).
    pose proof (d4_bytes sv nb SVR ltac:(lia)) as (DR & B0 & B1 & B2 & B3 & B4 & B5 & B6 & B7).
    remember (d4 sv nb) as D eqn:ED. clear ED.
    replace (Z_to_bv 64 (DT + (2 * cur + 2 * len + 20 + 2 * off))) with (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 2 * len)) by (f_equal; lia).
    eapply (x1_fillD_in' m1 dt syb s off Q D sv); try eassumption; try lia.
    (* [comment removed for export] *)
    clear B0 B1 B2 B3 B4 B5 B6 B7 DR. unfold KSYM. intros m2 dt2 syb2 y1 y5 y6 y7 y13 y17 y18 y26 y30 y31 I2 PR2.
    zstep. zstep. zstep. if_cases KB; zify_cond KB.
    - (* [comment removed for export] *)
      eapply KL; [exact I2|]. replace (cur + count * len) with (cur + off + len); [exact PR2|]. rewrite EOFF. replace count with (s + 1) by lia. ring.
    - replace (Z_to_bv 64 (DT + 20 + 2 * (cur + off) + 2 * len)) with (Z_to_bv 64 (DT + 20 + 2 * (cur + len * (s + 1)))) by (f_equal; rewrite EOFF; ring).
      eapply (IH m2 dt2 syb2 (s + 1) Q); try eassumption; try lia.
      replace (cur + len * (s + 1)) with (cur + off + len) by (rewrite EOFF; ring). exact PR2.
  Qed.
  End FILLW.

  (* [comment removed for export] *)
  Lemma x1_done : forall m2 dt2 rst syb2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    X1S FLF dt2 rst syb2 m2 -> PREF (2^tl) dt2 ->
    evt psegs POST (STF 0x1cf38 m2 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I (H0 & H1 & H2 & HP). open_x1s I. pose proof STOK as (TLR & _).
    zstep.
    assert (P2TL : 1 <= 2^tl <= 4096) by (split; [pose proof (Z.pow_pos_nonneg 2 tl ltac:(lia) ltac:(lia)); lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    assert (NTH : forall k, 0 <= k < 16388 -> nth_error (map (Z_to_bv 8) dt2) (Z.to_nat k) = Some (Z_to_bv 8 (Znth k dt2))).
    { intros k Hk. apply nth_error_map_Znth. lia. }
    assert (WKS : stk psegs m2 WK (WK + wksz)).
    { apply u8arr_of_u32arr in RK, RST. apply rw_cells_of_u8arr in RK, RST, SYC, HWC. apply stk_of_rw_cells in RK, RST, SYC, HWC.
      cbn [cells_size csize] in RK, RST, SYC, HWC. rewrite u32s_length, length_map in RK, RST. rewrite length_map in HWC.
      apply (stk_merge psegs m2 WK (WK + 52) (WK + wksz)); [replace (WK + 52) with (WK + Z.of_nat (4 * length rank + 0)) by lia; exact RK| |lia].
      apply (stk_merge psegs m2 (WK + 52) (WK + 104) (WK + wksz)); [replace (WK + 104) with (WK + 52 + Z.of_nat (4 * length rst + 0)) by lia; exact RST| |lia].
      apply (stk_merge psegs m2 (WK + 104) (WK + 980) (WK + wksz)); [exact STS| |lia].
      apply (stk_merge psegs m2 (WK + 980) (WK + 1236) (WK + wksz)); [replace (WK + 1236) with (WK + 980 + Z.of_nat (length syb2 + 0)) by lia; exact SYC| |lia].
      apply (stk_merge psegs m2 (WK + 1236) (WK + 1492) (WK + wksz)); [replace (WK + 1492) with (WK + 1236 + Z.of_nat (length hw + 0)) by lia; exact HWC| exact WKR |lia]. }
    assert (FL : rw_cells psegs m2 (SPV + -176) ((C8 fa :: C8 fb :: FLF) ++ [C4 wn; C4 wt])).
    { apply (proj2 (rw_cells_app psegs m2 (SPV + -176) (C8 fa :: C8 fb :: FLF) [C4 wn; C4 wt])). split; [exact F0|].
      cbn [cells_size csize Nat.add]. replace (SPV + -176 + Z.of_nat 64) with (SPV + -112) by lia. exact NSC. }
    eapply (x1_exit m2 _ (map (Z_to_bv 8) dt2) r0); try eassumption; try reflexivity.
    - split; [rewrite length_map; exact DTLEN|]. rewrite <- H0. exact (NTH 0 ltac:(lia)).
    - lia.
    - intros _. split.
      + split; [split; [rewrite length_map; exact DTLEN | rewrite <- H0; exact (NTH 0 ltac:(lia))]|].
        exists (Z_to_bv 8 0), tl. split; [rewrite <- H1; exact (NTH 1 ltac:(lia))|]. split; [rewrite <- H2; exact (NTH 2 ltac:(lia))|].
        split; [lia|]. split; [intros NZ; exfalso; apply NZ; reflexivity|].
        change (negb (bv_unsigned (Z_to_bv 8 0) =? 0)) with false. intros i Hi.
        exists (Z_to_bv 8 (Znth (4 + 2 * i) dt2)). split; [replace (2 * i + 4) with (4 + 2 * i) by lia; apply NTH; lia|].
        specialize (HP i Hi). rewrite byte_lit by lia. lia.
      + exists (Z_to_bv 8 0). split; [rewrite <- H1; exact (NTH 1 ltac:(lia))|]. split; [intros NZ; exfalso; apply NZ; reflexivity | intros E; discriminate E].
  Qed.

  (* [comment removed for export] *)
  Lemma x1_fill_loop : forall j m1 dt rst syb w x1 x5 x6 x7 x13 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x30 x31,
    Z.to_nat (tl + 1 - w) = j -> X1S FLF dt rst syb m1 -> PREF (xcur rank w) dt -> 1 <= w <= tl ->
    evt psegs POST (STFL 0x1cc40 m1 x1 x5 x6 x7 x13 (Z_to_bv 64 (xcur rank w)) (Z_to_bv 64 (xsym rank w)) x17 x18 (Z_to_bv 64 w)
                         x21 x22 x23 x24 x25 x26 x27 x28 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I PR WR; [exfalso; lia|].
    pose proof STOK as (TLR & _).
    pose proof (rank_le w ltac:(lia)) as CNTR.
    assert (P2TL : 2^tl <= 4096) by (change 4096 with (2^12); apply Z.pow_le_mono_r; lia).
    assert (SLOTS : forall s, 0 <= s < Znth w rank ->
              0 <= xsym rank w + s < 256 /\ 0 <= xcur rank w + s * hw_cells w /\ xcur rank w + s * hw_cells w + hw_cells w <= 4096).
    { intros s Hs. destruct (fill_slot _ _ _ STOK w s WR Hs) as (A & B & C). rewrite ws_len in A. lia. }
    pose proof (xcur_nonneg _ _ _ STOK w ltac:(lia)) as CUR0.
    pose proof (xsym_nonneg _ _ _ STOK w ltac:(lia)) as SYM0.
    assert (NBR12 : 1 <= tl + 1 - w <= 12) by lia.
    assert (CURH : xcur rank w <= 4096).
    { pose proof (xcur_mono _ _ _ STOK w (tl + 1) ltac:(lia) ltac:(lia)) as X. rewrite (xcur_end _ _ _ STOK) in X. lia. }
    assert (SYMH : xsym rank w <= 256).
    { pose proof (xsym_mono _ _ _ STOK w 13 ltac:(lia) ltac:(lia)) as X. rewrite (xsym_total _ _ _ STOK), ws_len in X. lia. }
    assert (LENR : 0 <= hw_cells w <= 2048) by (split; [apply hw_cells_nonneg | apply hw_cells_bound; lia]).
    remember (Znth w rank) as count eqn:ECNT. remember (hw_cells w) as len eqn:ELEN.
    remember (xcur rank w) as cur eqn:ECUR. remember (xsym rank w) as sym eqn:ESYM.
    (* [comment removed for export] *)
    assert (KL : KLATCH rst w cur sym count len).
    { unfold KLATCH. intros m2 dt2 syb2 y1 y5 y6 y7 y13 y17 y18 y23 y24 y25 y26 y27 y28 y30 y31 I2 PR2.
      assert (CLB : 0 <= count * len /\ cur + count * len <= 4096).
      { destruct (Z.eq_dec count 0) as [->|NZ]; [lia|].
        destruct (SLOTS (count - 1) ltac:(lia)) as (_ & A & B). split; [apply Z.mul_nonneg_nonneg; lia | lia]. }
      assert (XS : count + sym = xsym rank (w + 1)) by (rewrite (xsym_step rank w) by lia; lia).
      assert (XC : count * len + cur = xcur rank (w + 1)) by (rewrite (xcur_step rank w) by lia; lia).
      pose proof (xsym_mono _ _ _ STOK (w + 1) 13 ltac:(lia) ltac:(lia)) as X13. rewrite (xsym_total _ _ _ STOK), ws_len in X13.
      zstep. rewrite (swrap32_small (count + sym)) by lia.
      zstep. zstep. zstep.
      rewrite ?(Z.mod_small len 18446744073709551616) by lia.
      rewrite ?(Z.mod_small (count * len) 18446744073709551616) by lia.
      rewrite (swrap32_small (count * len + cur)) by lia.
      rewrite XS, XC.
      zstep. if_cases KE; zify_cond KE.
      - (* [comment removed for export] *)
        eapply (x1_done m2 dt2 rst syb2); [exact I2|].
        replace (2^tl) with (cur + count * len); [exact PR2|]. rewrite <- (xcur_end _ _ _ STOK). replace (tl + 1) with (w + 1) by lia. lia.
      - eapply (IH m2 dt2 rst syb2 (w + 1)); [lia | exact I2 | | lia].
        replace (xcur rank (w + 1)) with (cur + count * len) by lia. exact PR2. }
    open_x1s I.
    zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 WK rank w a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite <- ECNT in RD.
    zstep. rewrite (sx32w_small count) by lia. clear RD.
    zstep. rewrite (sllw_pow2 w) by lia.
    zstep.
    assert (P2W : 2 <= 2^w <= 4096) by (split; [change 2 with (2^1) at 1; apply Z.pow_le_mono_r; lia | change 4096 with (2^12); apply Z.pow_le_mono_r; lia]).
    rewrite (signed_lit (2^w)) by lia.
    assert (ELEN2 : 2^w ≫ 1 = len).
    { rewrite ELEN. unfold hw_cells. destruct (Z.eqb_spec w 0); [lia|]. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
      replace w with (Z.succ (w - 1)) at 1 by lia. rewrite Z.pow_succ_r by lia. rewrite Z.mul_comm, Z.div_mul by lia. reflexivity. }
    rewrite ELEN2.
    assert (LENW : (w = 1 /\ len = 1) \/ (w = 2 /\ len = 2) \/ (w = 3 /\ len = 4) \/ (w = 4 /\ len = 8) \/ (5 <= w /\ len = 16 * 2^(w - 5))).
    { rewrite ELEN. unfold hw_cells. destruct (Z.eqb_spec w 0); [lia|].
      destruct (Z.eq_dec w 1) as [->|N1]; [left; split; reflexivity|]. destruct (Z.eq_dec w 2) as [->|N2]; [right; left; split; reflexivity|].
      destruct (Z.eq_dec w 3) as [->|N3]; [right; right; left; split; reflexivity|]. destruct (Z.eq_dec w 4) as [->|N4]; [right; right; right; left; split; reflexivity|].
      right; right; right; right. split; [lia|]. change 16 with (2^4). rewrite <- Z.pow_add_r by lia. f_equal. lia. }
    zstep. rewrite (swrap32_small (tl + 1 - w)) by lia.
    zstep.
    assert (KL0 : forall y1 y5 y6 y7 y13 y17 y18 y23 y24 y25 y26 y27 y28 y30 y31,
              count <= 0 -> evt psegs POST (STFL 0x1cc2c m1 y1 y5 y6 y7 y13 (Z_to_bv 64 cur) (Z_to_bv 64 sym) y17 y18 (Z_to_bv 64 w) (Z_to_bv 64 count) (Z_to_bv 64 len)
                                                 y23 y24 y25 y26 y27 y28 y30 y31)).
    { intros. eapply KL; [close_x1s|]. replace (cur + count * len) with cur by (assert (count = 0) by lia; subst count; lia). exact PR. }
    destruct LENW as [(W1 & L1) | [(W2 & L2) | [(W3 & L4) | [(W4 & L8) | (W5 & L16)]]]].
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [exfalso; lia|].
      zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. if_cases K3; zify_lts K3; [eapply KL0; lia|].
      do 7 zstep.
      rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
      replace (Z_to_bv 64 (WK + 980 + sym)) with (Z_to_bv 64 (WK + 980 + sym + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 5 + cur * 2 + count * 2)) with (Z_to_bv 64 (DT + 5 + 2 * (cur + count))) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 5 + cur * 2)) with (Z_to_bv 64 (DT + 5 + 2 * (cur + 0))) by (f_equal; lia).
      eapply x1_fill1 with (rst := rst) (w := w) (cur := cur) (sym := sym) (count := count) (len := len) (nb := tl + 1 - w)
        (j := Z.to_nat (count - 0)) (s := 0) (dt := dt) (syb := syb); try eassumption; try lia.
      + close_x1s.
      + replace (cur + 0) with cur by lia. exact PR.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [exfalso; lia|].
      zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
      zstep. if_cases K3; zify_lts K3; [eapply KL0; lia|].
      do 6 zstep.
      rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
      replace (Z_to_bv 64 (WK + 980 + sym)) with (Z_to_bv 64 (WK + 980 + sym + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 7 + cur * 2)) with (Z_to_bv 64 (DT + 7 + 2 * (cur + 2 * 0))) by (f_equal; lia).
      eapply x1_fill2 with (rst := rst) (w := w) (cur := cur) (sym := sym) (count := count) (len := len) (nb := tl + 1 - w)
        (j := Z.to_nat (count - 0)) (s := 0) (dt := dt) (syb := syb); try eassumption; try lia.
      + close_x1s.
      + replace (cur + 2 * 0) with cur by lia. exact PR.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. zstep. if_cases K2; zify_cond K2; [|exfalso; lia].
      zstep. if_cases K3; zify_lts K3; [eapply KL0; lia|].
      do 8 zstep.
      replace (Z.land (tl + 1 - w) 255) with (tl + 1 - w) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
      rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2. change (2^3) with 8.
      replace (Z_to_bv 64 (WK + 980 + sym)) with (Z_to_bv 64 (WK + 980 + sym + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + cur * 2)) with (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + cur * 2 + count * 8)) with (Z_to_bv 64 (DT + 4 + 2 * (cur + 4 * count))) by (f_equal; lia).
      eapply x1_fill4 with (rst := rst) (w := w) (cur := cur) (sym := sym) (count := count) (len := len) (nb := tl + 1 - w)
        (j := Z.to_nat (count - 0)) (s := 0) (dt := dt) (syb := syb); try eassumption; try lia.
      + close_x1s.
      + replace (cur + 4 * 0) with cur by lia. exact PR.
    - (* [comment removed for export] *)
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep. if_cases K2b; zify_cond K2b; [exfalso; lia|].
      zstep. if_cases K3; zify_lts K3; [eapply KL0; lia|].
      do 8 zstep.
      replace (Z.land (tl + 1 - w) 255) with (tl + 1 - w) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
      rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2. change (2^4) with 16.
      replace (Z_to_bv 64 (WK + 980 + sym)) with (Z_to_bv 64 (WK + 980 + sym + 0)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 12 + cur * 2)) with (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * 0))) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 12 + cur * 2 + count * 16)) with (Z_to_bv 64 (DT + 12 + 2 * (cur + 8 * count))) by (f_equal; lia).
      eapply x1_fill8 with (rst := rst) (w := w) (cur := cur) (sym := sym) (count := count) (len := len) (nb := tl + 1 - w)
        (j := Z.to_nat (count - 0)) (s := 0) (dt := dt) (syb := syb); try eassumption; try lia.
      + close_x1s.
      + replace (cur + 8 * 0) with cur by lia. exact PR.
    - (* [comment removed for export] *)
      assert (Q1 : 1 <= 2^(w - 5)) by (pose proof (Z.pow_pos_nonneg 2 (w - 5) ltac:(lia) ltac:(lia)); lia).
      assert (QH : 2^(w - 5) <= 128) by (change 128 with (2^7); apply Z.pow_le_mono_r; lia).
      remember (2^(w - 5)) as Q eqn:EQ. clear EQ.
      if_cases K1; zify_lts K1; [|exfalso; lia].
      zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
      zstep. zstep. if_cases K2b; zify_cond K2b; [|exfalso; lia].
      zstep. if_cases K3; zify_lts K3; [eapply KL0; lia|].
      do 11 zstep.
      assert (LM32 : Z.land ((len ≪ 1 + -2) mod 18446744073709551616) 18446744073709551584 = 2 * len - 32).
      { rewrite L16. clear - Q1 QH.
        assert (B : forallb (fun q => Z.land (((16 * q) ≪ 1 + -2) mod 18446744073709551616) 18446744073709551584 =? 2 * (16 * q) - 32)
                      (map Z.of_nat (seq 1 128)) = true) by (vm_compute; reflexivity).
        rewrite forallb_forall in B. apply Z.eqb_eq. apply B. apply in_map_iff. exists (Z.to_nat Q). split; [lia|]. apply in_seq. lia. }
      rewrite LM32.
      replace (Z.land (tl + 1 - w) 255) with (tl + 1 - w) by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; rewrite Z.mod_small; lia).
      rewrite !Z.shiftl_mul_pow2 by lia. change (2^1) with 2.
      replace (Z_to_bv 64 (len * 2)) with (Z_to_bv 64 (2 * len)) by (f_equal; lia).
      replace (Z_to_bv 64 (2 * len - 32 + cur * 2 + 52)) with (Z_to_bv 64 (2 * cur + 2 * len + 20)) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 20 + cur * 2)) with (Z_to_bv 64 (DT + 20 + 2 * (cur + len * 0))) by (f_equal; lia).
      eapply x1_fillD_sym with (rst := rst) (w := w) (cur := cur) (sym := sym) (count := count) (len := len) (nb := tl + 1 - w)
        (j := Z.to_nat (count - 0)) (s := 0) (dt := dt) (syb := syb) (Q := Q); try eassumption; try lia.
      + close_x1s.
      + replace (cur + len * 0) with cur by lia. exact PR.
  Qed.

  (* [comment removed for export] *)
  Lemma x1_fill : forall dt, PREF 0 dt -> KFILL dt.
  Proof.
    intros dt PR0. unfold KFILL. intros until x31; intros I. open_x1s I. pose proof STOK as (TLR & _).
    zstep. zstep. if_cases KA; zify_cond KA; [exfalso; lia|].
    zstep. zstep. zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs _ WK rank 0 a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    zstep.
    pose proof (rank_le 0 ltac:(lia)) as R0B.
    rewrite (sx32w_small (Znth 0 rank)) by lia. clear RD.
    do 11 zstep. do 7 zstep.
    replace (((tl + 1) * 4294967296) ≫ 32) with (tl + 1) by (rewrite Z.shiftr_div_pow2 by lia; change (2^32) with 4294967296; rewrite Z.div_mul by lia; reflexivity).
    assert (XC1 : xcur rank 1 = 0) by (unfold xcur; change (Z.to_nat 1) with 1%nat; cbn [psum]; change (Z.of_nat 0) with 0; change (hw_cells 0) with 0; lia).
    assert (XS1 : xsym rank 1 = Znth 0 rank) by (unfold xsym; change (Z.to_nat 1) with 1%nat; cbn [psum]; change (Z.of_nat 0) with 0; lia).
    rewrite <- XS1. replace (Z_to_bv 64 0) with (Z_to_bv 64 (xcur rank 1)) by (rewrite XC1; reflexivity).
    eapply (x1_fill_loop (Z.to_nat (tl + 1 - 1)) _ dt rst syb 1); [reflexivity | close_x1s | rewrite XC1; exact PR0 | lia].
  Qed.
  End P2.

  (* [comment removed for export] *)
  Definition X1M (fa fb : word) (f2 f3 f4 f5 f6 f7 : cell) (wn wt : word) (dt hw rank : list Z) (m1 : fmem) : Prop :=
      u8arr psegs m1 DT (map (Z_to_bv 8) dt) /\ Z.of_nat (length dt) = 16388 /\ Forall isbyte dt
      /\ u8arr psegs m1 (WK + 1236) (map (Z_to_bv 8) hw) /\ Z.of_nat (length hw) = 256 /\ Forall isbyte hw
      /\ u32arr psegs m1 WK (map (Z_to_bv 64) rank) /\ Z.of_nat (length rank) = 13
      /\ stk psegs m1 (WK + 52) (WK + 104) /\ stk psegs m1 (WK + 104) (WK + 980) /\ stk psegs m1 (WK + 980) (WK + 1236)
      /\ stk psegs m1 (WK + 1492) (WK + wksz)
      /\ rw_cells psegs m1 (SPV + -176) [C8 fa; C8 fb; f2; f3; f4; f5; f6; f7] /\ cells_size [f2; f3; f4; f5; f6; f7] = 48%nat
      /\ rw_cells psegs m1 (SPV + -112) [C4 wn; C4 wt]
      /\ rw_cells psegs m1 (SPV + -104) SAVED /\ stk psegs m1 lo (SPV + -176)
      /\ mem_inv psegs m1 /\ munch MUNCH m m1 /\ wmono psegs m m1.

  (* [comment removed for export] *)
  Lemma x1_build : forall m1 fa fb f2 f3 f4 f5 f6 f7 wn wt dt hw rank r0 nbs tl hdw x1 x5 x6 x7 x11 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
      X1M fa fb (CB 8 f2) (CB 8 f3) (CB 8 f4) (CB 8 f5) (CB 8 f6) (CB 8 f7) wn wt dt hw rank m1 ->
      huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl -> 2 <= nbs <= 256 -> 1 <= r0 <= n ->
      Znth 0 dt = 12 -> 0 <= hdw < 4294967296 -> hdw mod 256 = 12 -> 1492 <= wksz ->
      evt psegs POST (STF 0x1caa4 m1 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 r0) x11 x12 x13 x14 x15 x16 x17
                          (Z_to_bv 64 (WK + 1236)) x19 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 tl) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I STOK NBR R0R DTZ0 HDWR HDW12 WK1492.
    destruct I as (DTC & DTLEN & DTBY & HWC & HWLEN & HWBY & RK & RKLEN & RTS & STS & SYS & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof STOK as (TLR & _).
    zstep. zstep. zstep. zstep.
    replace (Z_to_bv 64 DT) with (Z_to_bv 64 (DT + 0)) by (f_equal; lia).
    u8_sok DTC 0. zstep. u8_store DTC 0 12.
    1: (rewrite HDW12; reflexivity).
    u8_sok DTC 1. zstep.
    rewrite <- (le1_lit 0). u8_store DTC 1 0; [reflexivity|].
    u8_sok DTC 2. zstep. u8_store DTC 2 tl; [reflexivity|].
    u8_sok DTC 3. zstep. u8_store DTC 3 ((hdw ≫ 24) mod 256); [rewrite Z.mod_mod by lia; reflexivity|].
  assert (H24 : 0 <= hdw ≫ 24 mod 256 < 256) by (apply Z.mod_pos_bound; lia).
  remember (Zupd 3 (hdw ≫ 24 mod 256) (Zupd 2 tl (Zupd 1 0 (Zupd 0 12 dt)))) as dt1 eqn:EDT1.
  assert (DT1L : Z.of_nat (length dt1) = 16388) by (subst dt1; rewrite !Zupd_length; exact DTLEN).
  assert (DT1BY : Forall isbyte dt1) by (subst dt1; repeat (apply Forall_Zupd; [|lia]); exact DTBY).
  assert (DT1H : Znth 0 dt1 = 12 /\ Znth 1 dt1 = 0 /\ Znth 2 dt1 = tl).
  { subst dt1. unfold FseNCount.Zlength in *.
    rewrite (Znth_Zupd_other 3 0), (Znth_Zupd_other 2 0), (Znth_Zupd_other 1 0), Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia).
    rewrite (Znth_Zupd_other 3 1), (Znth_Zupd_other 2 1), Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia).
    rewrite (Znth_Zupd_other 3 2), Znth_Zupd_same by (unfold FseNCount.Zlength; rewrite ?Zupd_length; lia). auto. }
  clear EDT1.
  rewrite (swrap32_small (tl + 1)) by lia. rewrite (swrap32_small (nbs + -3)) by lia.
  zstep. replace ((tl + 1) ≪ 32) with ((tl + 1) * 4294967296) by (rewrite Z.shiftl_mul_pow2 by lia; reflexivity).
  zstep.
  replace (((tl + 1) * 4294967296) ≫ 30) with (4 * (tl + 1))
    by (rewrite Z.shiftr_div_pow2 by lia; change 4294967296 with (4 * 2^30); rewrite Z.mul_assoc, Z.div_mul by lia; lia).
  zstep. zstep.
  (* [comment removed for export] *)
  destruct (u32arr_of_stk psegs _ (WK + 52) 13%nat ltac:(replace (WK + 52 + 4 * Z.of_nat 13) with (WK + 104) by lia; exact RTS) ltac:(lia)) as (rst0 & RST & RSTLEN0).
  destruct (stk_open psegs _ (WK + 980) (WK + 1236) (WK + 980) 256%nat SYS ltac:(lia) ltac:(lia)) as (syb & SYC & _ & _).
  assert (SYLEN : Z.of_nat (length syb) = 256) by (destruct SYC as [[WF _] _]; cbn in WF; destruct WF as [LJ _]; lia).
  apply u8arr_of_rw_cells in SYC.
  assert (I2 : X1S fa fb wn wt hw rank [CB 8 f2; CB 8 f3; CB 8 f4; CB 8 f5; CB 8 f6; CB 8 f7] dt1 rst0 syb m1).
  { unfold X1S, HUF_TBL_STACK, HUF_DTABLE_BYTES. repeat (split; [first [eassumption | lia | reflexivity]|]). eassumption. }
  assert (XS0 : xsym rank 0 = 0) by reflexivity.
  replace (Z_to_bv 64 0) with (Z_to_bv 64 (xsym rank 0)) by (rewrite XS0; reflexivity).
  eapply x1_rstart with (k := 0) (p15 := WK) (rst := rst0) (syb := syb) (dt := dt1) (j := Z.to_nat (tl + 1 - 0)) (r0 := r0) (hdw := hdw);
    try eassumption; try reflexivity; try lia.
  all: try (intros v Hv; exfalso; lia).
  intros m2 rst' y17 I3 RS'.
  eapply x1_sort with (r0 := r0) (hdw := hdw); try eassumption; try lia.
  eapply x1_fill; try eassumption; try lia.
  destruct DT1H as (A & B & C). split; [exact A|]. split; [exact B|]. split; [exact C|]. intros u Hu. lia.
  Unshelve. all: try exact 0.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma resc_val : forall w s, 0 <= w -> 0 <= s < 18446744073709551616 ->
  Z.land ((Z.b2z (w <? 1) + -1) mod 18446744073709551616) s + w = resc s w.
Proof.
  intros w s Hw Hs. unfold resc. destruct (Z.ltb_spec w 1) as [L|L].
  - assert (w = 0) by lia. subst w. cbn [Z.b2z]. change ((1 + -1) mod 18446744073709551616) with 0. rewrite Z.land_0_l. reflexivity.
  - destruct (Z.eqb_spec w 0); [lia|]. cbn [Z.b2z]. change ((0 + -1) mod 18446744073709551616) with (Z.ones 64).
    rewrite Z.land_comm, Z.land_ones by lia. change (2^64) with 18446744073709551616. rewrite Z.mod_small by lia. lia.
Qed.

Section RESC.
  Variables (fa fb : word) (f2 f3 f4 f5 f6 f7 : list byte) (wn wt : word) (dt hw rank : list Z) (r0 nbs tl0 sc hdw : Z).
  Hypothesis NBR : 2 <= nbs <= 256.  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis HWBY : Forall isbyte hw.
  Hypothesis WTL : forall i, 0 <= i < nbs -> 0 <= Znth i hw <= tl0.
  Hypothesis SCR : 0 < sc.  Hypothesis TLSC : tl0 + sc = 11.  Hypothesis TL0 : 1 <= tl0.
  Hypothesis WK1492 : 1492 <= wksz.
  Hypothesis RKB : forall v, 0 <= v <= 12 -> 0 <= Znth v rank <= 256.

  Notation X1Mr := (X1M fa fb (CB 8 f2) (CB 8 f3) (CB 8 f4) (CB 8 f5) (CB 8 f6) (CB 8 f7) wn wt dt).
  Notation hwk k := (map (resc sc) (firstn (Z.to_nat k) hw) ++ skipn (Z.to_nat k) hw).

  (* [comment removed for export] *)
  Lemma x1_wloop : forall j m1 k p14 x1 x5 x6 x7 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat (nbs - k) = j -> X1Mr (hwk k) rank m1 -> 0 <= k < nbs -> p14 = WK + 1236 + k ->
    (forall m2 y15 y16, X1Mr (hwk nbs) rank m2 ->
       evt psegs POST (STF 0x1ca44 m2 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 r0) (Z_to_bv 64 tl0) (Z_to_bv 64 sc)
                           (Z_to_bv 64 (nbs + WK + 1236)) (Z_to_bv 64 (nbs + WK + 1236)) y15 y16 x17
                           (Z_to_bv 64 (WK + 1236)) x19 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 11) x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (STF 0x1ca24 m1 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 r0) (Z_to_bv 64 tl0) (Z_to_bv 64 sc)
                        (Z_to_bv 64 (nbs + WK + 1236)) (Z_to_bv 64 p14) x15 x16 x17
                        (Z_to_bv 64 (WK + 1236)) x19 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 11) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I KR EP KONT; [exfalso; lia|]. subst p14.
    destruct I as (DTC & DTLEN & DTBY & HWC & HWKLEN & HWKBY & RK & RKLEN & RTS & STS & SYS & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    pose proof (WTL k KR) as WKB.
    assert (NTHK : Znth k (hwk k) = Znth k hw) by (unfold Znth; apply resc_nth_nat).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth psegs m1 (WK + 1236) (hwk k) k a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite NTHK in RD.
    remember (Znth k hw) as w eqn:EW.
    zstep. cbv beta. rewrite (byte_lit w) by lia. clear RD.
    zstep. zstep. zstep. zstep.
    rewrite (resc_val w sc) by lia.
    assert (RV : 0 <= resc sc w < 256) by (unfold resc; destruct (w =? 0); lia).
    u8_sok HWC k. zstep. u8_store HWC k (resc sc w); [reflexivity|].
    assert (STEP : Zupd k (resc sc w) (hwk k) = hwk (k + 1)).
    { unfold Zupd. rewrite EW. unfold Znth. replace (Z.to_nat (k + 1)) with (S (Z.to_nat k)) by lia. apply resc_step_nat. lia. }
    assert (HWKLEN' : Z.of_nat (length (hwk (k + 1))) = 256) by (rewrite resc_len_nat; exact HWLEN).
    assert (HWKBY' : Forall isbyte (hwk (k + 1))) by (rewrite <- STEP; apply Forall_Zupd; [exact HWKBY | lia]).
    rewrite STEP in HWC.
    assert (I' : X1Mr (hwk (k + 1)) rank m0).
    { unfold X1M, HUF_TBL_STACK, HUF_DTABLE_BYTES. repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 1236 + k + 1)) with (Z_to_bv 64 (WK + 1236 + (k + 1))) by (f_equal; lia).
      eapply (IH m0 (k + 1) (WK + 1236 + (k + 1))); [lia | exact I' | lia | reflexivity | exact KONT].
    - assert (EK : k + 1 = nbs) by lia. rewrite EK in I'.
      replace (Z_to_bv 64 (WK + 1236 + k + 1)) with (Z_to_bv 64 (nbs + WK + 1236)) by (f_equal; lia).
      eapply KONT. exact I'.
  Qed.

  Notation X1Mh := (X1M fa fb (CB 8 f2) (CB 8 f3) (CB 8 f4) (CB 8 f5) (CB 8 f6) (CB 8 f7) wn wt dt (hwk nbs)).

  (* [comment removed for export] *)
  Lemma x1_rloop : forall j m1 cur s x1 x5 x6 x7 x15 x16 x17 x24 x25 x26 x27 x28 x29 x30 x31,
    Z.to_nat (s - sc) = j -> X1Mh cur m1 -> shifted s sc rank cur -> sc < s <= 11 ->
    (forall m2 cur' y10 y15, X1Mh cur' m2 -> shifted sc sc rank cur' ->
       evt psegs POST (STF 0x1ca78 m2 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) y10 (Z_to_bv 64 tl0) (Z_to_bv 64 sc)
                           (Z_to_bv 64 (- (4 * sc))) (Z_to_bv 64 sc) y15 x16 x17
                           (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 11) x24 x25 x26 x27 x28 x29 x30 x31)) ->
    evt psegs POST (STF 0x1ca60 m1 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 (WK + 4 * s)) (Z_to_bv 64 tl0) (Z_to_bv 64 sc)
                        (Z_to_bv 64 (- (4 * sc))) (Z_to_bv 64 s) x15 x16 x17
                        (Z_to_bv 64 (WK + 1236)) (Z_to_bv 64 r0) (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 11) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros EJ I SH SR KONT; [exfalso; lia|].
    destruct I as (DTC & DTLEN & DTBY & HWC & HWKLEN & HWKBY & RK & RKLEN & RTS & STS & SYS & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    destruct (shifted_step s sc rank cur SH ltac:(lia) ltac:(lia)) as (ERD & SH').
    zstep.
    assert (CURL : Z.of_nat (length cur) = 13) by (destruct SH as (L & _); exact L).
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth psegs m1 WK cur (s - sc) a RK ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite ERD in RD. pose proof (RKB (s - sc) ltac:(lia)) as RVB.
    zstep. rewrite (sx32w_small (Znth (s - sc) rank)) by lia. clear RD.
    zstep. rewrite (swrap32_small (s + -1)) by lia.
    u32st2 RK s (Znth (s - sc) rank) (Znth (s - sc) rank).
    change (upd_nat (Z.to_nat s) (Znth (s - sc) rank) cur) with (Zupd s (Znth (s - sc) rank) cur) in RK.
    remember (Zupd s (Znth (s - sc) rank) cur) as cur' eqn:ECUR'.
    assert (RKLEN' : Z.of_nat (length cur') = 13) by (subst cur'; rewrite Zupd_length; exact CURL).
    clear ECUR'.
    assert (I' : X1Mh cur' m0).
    { unfold X1M, HUF_TBL_STACK, HUF_DTABLE_BYTES. clear RKLEN. repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (WK + 4 * s + -4)) with (Z_to_bv 64 (WK + 4 * (s + -1))) by (f_equal; lia).
      eapply (IH m0 cur' (s + -1)); [lia | exact I' | replace (s + -1) with (s - 1) by lia; exact SH' | lia | exact KONT].
    - assert (ES : s - 1 = sc) by lia. rewrite ES in SH'. replace (s + -1) with sc by lia.
      eapply KONT; [exact I' | exact SH'].
  Qed.

  Hypothesis STOK0 : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl0.
  Hypothesis R0R : 1 <= r0 <= n.  Hypothesis DTZ0 : Znth 0 dt = 12.
  Hypothesis HDWR : 0 <= hdw < 4294967296.  Hypothesis HDW12 : hdw mod 256 = 12.

  (* [comment removed for export] *)
  Lemma x1_rescale : forall m1 x1 x5 x6 x7 x12 x13 x14 x15 x16 x17 x19 x24 x25 x26 x27 x28 x29 x30 x31,
    X1M fa fb (CB 8 f2) (CB 8 f3) (CB 8 f4) (CB 8 f5) (CB 8 f6) (CB 8 f7) wn wt dt hw rank m1 ->
    evt psegs POST (STF 0x1ca10 m1 x1 x5 x6 x7 (Z_to_bv 64 WK) (Z_to_bv 64 DT) (Z_to_bv 64 r0) (Z_to_bv 64 tl0) x12 x13 x14 x15 x16 x17
                        (Z_to_bv 64 (WK + 1236)) x19 (Z_to_bv 64 nbs) (Z_to_bv 64 nbs) (Z_to_bv 64 hdw) (Z_to_bv 64 11) x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I.
    zstep. rewrite (swrap32_small (11 - tl0)) by lia. replace (11 - tl0) with sc by lia.
    zstep. if_cases K0; zify_cond K0; [exfalso; lia|].
    zstep. zstep. zstep.
    assert (HK0 : hwk 0 = hw) by reflexivity.
    eapply (x1_wloop (Z.to_nat (nbs - 0)) m1 0 (WK + 1236)); [reflexivity | rewrite HK0; exact I | lia | lia |].
    intros m2 y15 y16 I2.
    zstep. zstep. if_cases K1; zify_cond K1; [exfalso; lia|].
    do 5 zstep.
    replace (sc ≪ 2) with (4 * sc) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite (Z.mod_small (4 * sc)) by lia.
    replace (Z_to_bv 64 (0 - 4 * sc)) with (Z_to_bv 64 (- (4 * sc))) by (f_equal; lia).
    replace (Z_to_bv 64 (WK + 44)) with (Z_to_bv 64 (WK + 4 * 11)) by (f_equal; lia).
    pose proof STOK0 as (_ & _ & _ & RKL0 & _).
    eapply (x1_rloop (Z.to_nat (11 - sc)) m2 rank 11); [reflexivity | exact I2 | apply shifted_init; exact RKL0 | lia |].
    intros m3 cur' y10 y15' I3 SH3.
    do 9 zstep.
    assert (EA : (((11 + Z.lxor tl0 18446744073709551615) mod 18446744073709551616) ≪ 32 mod 18446744073709551616) ≫ 30 = 4 * (sc - 1)).
    { replace sc with (11 - tl0) by lia. clear - TL0 SCR TLSC.
      assert (C : tl0 = 1 \/ tl0 = 2 \/ tl0 = 3 \/ tl0 = 4 \/ tl0 = 5 \/ tl0 = 6 \/ tl0 = 7 \/ tl0 = 8 \/ tl0 = 9 \/ tl0 = 10) by lia.
      repeat (destruct C as [E|C]; [rewrite E; vm_compute; reflexivity|]). rewrite C. vm_compute. reflexivity. }
    rewrite EA.
    replace (sc ≪ 2) with (4 * sc) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    rewrite (swrap32_small (4 * sc)) by lia. rewrite (Z.mod_small (WK + 4 * sc)) by lia.
    replace (WK + 4 * sc - 4 * (sc - 1)) with (WK + 4) by lia. replace (4 * (sc - 1) + 4) with (4 * sc) by lia.
    zstep.
    destruct I3 as (DTC & DTLEN & DTBY & HWC & HWKLEN & HWKBY & RK & RKLEN & RTS & STS & SYS & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM).
    unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    (* [comment removed for export] *)
    set (wsl := map (Z_to_bv 64) cur') in *.
    assert (WSL : length wsl = 13%nat) by (unfold wsl; rewrite length_map; lia).
    assert (ESPL : wsl = firstn 1 wsl ++ firstn (Z.to_nat sc) (skipn 1 wsl) ++ skipn (1 + Z.to_nat sc) wsl).
    { rewrite <- (firstn_skipn 1 wsl) at 1. f_equal. rewrite <- (firstn_skipn (Z.to_nat sc) (skipn 1 wsl)) at 1. f_equal. rewrite skipn_skipn. f_equal. lia. }
    remember (firstn 1 wsl) as ws1 eqn:EW1. remember (firstn (Z.to_nat sc) (skipn 1 wsl)) as ws2 eqn:EW2. remember (skipn (1 + Z.to_nat sc) wsl) as ws3 eqn:EW3.
    assert (L1 : length ws1 = 1%nat) by (subst ws1; rewrite length_firstn; lia).
    assert (L2 : length ws2 = Z.to_nat sc) by (subst ws2; rewrite length_firstn, length_skipn; lia).
    assert (L3 : length ws3 = (12 - Z.to_nat sc)%nat) by (subst ws3; rewrite length_skipn; lia).
    apply u8arr_of_u32arr in RK. rewrite ESPL, !u32s_app in RK.
    apply (proj1 (u8arr_app psegs _ WK (u32s ws1) (u32s ws2 ++ u32s ws3))) in RK. destruct RK as [RK1 RK23].
    apply (proj1 (u8arr_app psegs _ _ (u32s ws2) (u32s ws3))) in RK23. destruct RK23 as [RK2 RK3].
    rewrite u32s_length, L1 in RK2, RK3. rewrite u32s_length, L2 in RK3.
    replace (WK + Z.of_nat (4 * 1)) with (WK + 4) in RK2, RK3 by lia.
    replace (WK + 4 + Z.of_nat (4 * Z.to_nat sc)) with (WK + 4 + 4 * sc) in RK3 by lia.
    apply rw_cells_of_u8arr in RK2. rewrite u32s_length, L2 in RK2.
    remember (u32s ws2) as mid eqn:EMID. clear EMID.
    clear EA.
    eapply evt_cut.
    { eapply (memset_spec _ _ gp tp _ _ _ _ _ (Z_to_bv 64 (WK + 4)) (Z_to_bv 64 0) (Z_to_bv 64 (4 * sc)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m3 mid); [|eassumption].
      rewrite !unsigned_lit by lia. replace (Z.to_nat (4 * sc)) with (4 * Z.to_nat sc)%nat by lia. exact RK2. }
    unfold memset_post. rewrite !unsigned_lit by lia. post_call psegs m3.
    (* [comment removed for export] *)
    apply u8arr_of_rw_cells in POST.
    replace (repeat (Z_to_bv 8 (0 mod 256)) (Z.to_nat (4 * sc))) with (u32s (map (Z_to_bv 64) (repeat 0 (Z.to_nat sc)))) in POST
      by (rewrite u32s_zeros; f_equal; lia).
    assert (RKN : u32arr psegs x32 WK (ws1 ++ map (Z_to_bv 64) (repeat 0 (Z.to_nat sc)) ++ ws3)).
    { apply u32arr_of_u32s. rewrite !u32s_app.
      apply (proj2 (u8arr_app psegs _ WK (u32s ws1) _)). split; [exact RK1|].
      rewrite u32s_length, L1. replace (WK + Z.of_nat (4 * 1)) with (WK + 4) by lia.
      apply (proj2 (u8arr_app psegs _ (WK + 4) _ (u32s ws3))). split; [exact POST|].
      rewrite u32s_length, length_map, repeat_length. replace (WK + 4 + Z.of_nat (4 * Z.to_nat sc)) with (WK + 4 + 4 * sc) by lia. exact RK3. }
    assert (EMOD : ws1 ++ map (Z_to_bv 64) (repeat 0 (Z.to_nat sc)) ++ ws3
                   = map (Z_to_bv 64) ([Znth 0 cur'] ++ repeat 0 (Z.to_nat sc) ++ skipn (Z.to_nat (sc + 1)) cur')).
    { rewrite !map_app. subst ws1 ws3. unfold wsl. rewrite firstn_map, skipn_map. f_equal; [|f_equal; f_equal; f_equal; lia].
      destruct cur' as [|c0 t]; [cbn in RKLEN; lia|]. reflexivity. }
    rewrite EMOD in RKN. clear EMOD RK1 RK3 POST.
    remember ([Znth 0 cur'] ++ repeat 0 (Z.to_nat sc) ++ skipn (Z.to_nat (sc + 1)) cur') as rank' eqn:ERK'.
    assert (RR : rank_resc sc rank rank').
    { subst rank'. apply (shifted_resc sc rank cur' tl0 SH3 SCR TLSC TL0). intros v Hv. apply (st_rank_high _ _ _ STOK0 v Hv). }
    assert (RKLEN' : Z.of_nat (length rank') = 13) by (destruct RR as (L & _); exact L).
    zstep.
    assert (EFH : firstn (Z.to_nat nbs) (hwk nbs) = map (resc sc) (firstn (Z.to_nat nbs) hw)).
    { assert (LL : length (map (resc sc) (firstn (Z.to_nat nbs) hw)) = Z.to_nat nbs) by (rewrite length_map, length_firstn; lia).
      rewrite firstn_app, LL, Nat.sub_diag, firstn_O, app_nil_r. rewrite <- LL at 1. apply firstn_all. }
    assert (STOK' : huf_stats_ok (firstn (Z.to_nat nbs) (hwk nbs)) rank' 11).
    { rewrite EFH. replace 11 with (tl0 + sc) by lia. apply (huf_stats_rescale _ rank rank' tl0 sc STOK0 SCR ltac:(lia) RR). }
    eapply x1_build with (hw := hwk nbs) (rank := rank') (tl := 11) (nbs := nbs) (hdw := hdw); try eassumption; try lia.
    unfold X1M, HUF_TBL_STACK, HUF_DTABLE_BYTES. clear RKLEN. repeat (split; [first [eassumption | reflexivity]|]). eassumption.
  Qed.
End RESC.

(* [comment removed for export] *)
Lemma x1_exit_stk : forall m1 dtb' r x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
  u8arr psegs m1 DT dtb' -> huf_hdr_ok dtb' -> stk psegs m1 WK (WK + wksz) -> stk psegs m1 lo (SPV + -176) ->
  stk psegs m1 (SPV + -176) (SPV + -104) -> rw_cells psegs m1 (SPV + -104) SAVED ->
  mem_inv psegs m1 -> munch MUNCH m m1 -> wmono psegs m m1 -> 0 <= r < 2^64 ->
  (zd_is_error r = false -> huf_tbl_ok dtb' /\ exists ty, nth_error dtb' 1 = Some ty /\ (bv_unsigned ty <> 0 <-> false = true)) ->
  evt psegs POST (STF 0x1cf3c m1 x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 (Z_to_bv 64 r) x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
Proof.
  intros until x31; intros DTC HDR' WKS STK STF0 FSAV MI MU WM RR RES.
  destruct (stk_open psegs m1 (SPV + -176) (SPV + -104) (SPV + -176) 72%nat STF0 ltac:(lia) ltac:(lia)) as (j & C & _ & _).
  eapply (x1_exit m1 [CB 72 j] dtb' r); try eassumption. reflexivity.
Qed.

  Theorem huf_rdx1_body : forall (t0 t1 t2 flags a6 a7 t3 t4 t5 t6 : word),
    mem_inv psegs m -> stk psegs m lo SPV -> bytes_at psegs m SRC src -> u8arr psegs m DT dtb -> stk psegs m WK (WK + wksz) ->
    evt psegs POST
      (MS (mkR ra (Z_to_bv 64 SPV) gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 DT) (Z_to_bv 64 SRC) (Z_to_bv 64 n) (Z_to_bv 64 WK)
               (Z_to_bv 64 wksz) flags a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 PHUF_RDX1) fc None m (seg_rom psegs)).
  Proof.
    intros t0 t1 t2 flags a6 a7 t3 t4 t5 t6 MI STK SRCB DTC WKS. unfold PHUF_RDX1.
    pose proof HDR as [DTLEN DT0]. unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
    assert (MU : munch [(DT, DT + 16388); (WK, WK + wksz); (SPV - 1024, SPV)] m m) by apply munch_refl.
    assert (WM : wmono psegs m m) by apply wmono_refl.
    zstep. carve_frame 176%nat STK.
    do 13 zstep. zstep.
    lazymatch type of FR with rw_cells _ _ _ (CB 72 ?j :: _) => generalize dependent j; intros fj FR end.
    lazymatch type of FR with rw_cells _ _ _ (CB 72 ?j :: ?post) =>
      apply (rw_cells_split_CB psegs _ _ [] 72 j post [8; 8; 8; 8; 8; 8; 8; 8; 4; 4]%nat) in FR; [| reflexivity] end.
    cbn [mk_CB_cells app] in FR.
    repeat match type of FR with context [CB ?k (firstn ?a ?b)] => let j := fresh "fj" in set (j := firstn a b) in FR; clearbody j end.
    clear fj.
    zstep. zstep.
    (* [comment removed for export] *)
    lazymatch type of FR with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: ?rest) =>
      apply (proj1 (rw_cells_app psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9] rest)) in FR; destruct FR as [F0 FSAV] end.
    cbn [cells_size csize Nat.add] in FSAV. replace (SPV + -176 + Z.of_nat 72) with (SPV + -104) in FSAV by lia.
    zstep. zstep. zstep. if_cases K0; zify_cond K0.
    { (* [comment removed for export] *)
      replace (Z_to_bv 64 (-44)) with (Z_to_bv 64 18446744073709551572) by (apply bv_eq; reflexivity).
      eapply (x1_exit _ _ dtb 18446744073709551572); try eassumption; try reflexivity; [lia | intros E; discriminate E]. }
    do 13 zstep.
    zstep. zstep.
    (* [comment removed for export] *)
    destruct (stk_split psegs _ WK (WK + 52) (WK + wksz) WKS ltac:(lia)) as [RSS WKS1].
    destruct (stk_split psegs _ (WK + 52) (WK + 104) (WK + wksz) WKS1 ltac:(lia)) as [RTS WKS2].
    destruct (stk_split psegs _ (WK + 104) (WK + 980) (WK + wksz) WKS2 ltac:(lia)) as [STS WKS3].
    destruct (stk_split psegs _ (WK + 980) (WK + 1236) (WK + wksz) WKS3 ltac:(lia)) as [SYS WKS4].
    destruct (stk_split psegs _ (WK + 1236) (WK + 1492) (WK + wksz) WKS4 ltac:(lia)) as [HWS WKR].
    clear WKS WKS1 WKS2 WKS3 WKS4.
    (* [comment removed for export] *)
    lazymatch type of F0 with rw_cells _ _ _ (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?rest) =>
      apply (proj1 (rw_cells_app psegs _ _ [c0; c1; c2; c3; c4; c5; c6; c7] rest)) in F0; destruct F0 as [F0 NSC] end.
    cbn [cells_size csize Nat.add] in NSC. replace (SPV + -176 + Z.of_nat 64) with (SPV + -112) in NSC by lia.
    assert (ARGB : bytes_at psegs m0 (SPV + -176) (le8 (Z_to_bv 64 876))).
    { pose proof (SysStep.rw_cells_bytes_at _ _ _ _ F0) as HB. cbn [cells_bytes cbytes] in HB. apply bytes_at_app in HB. exact (proj1 HB). }
    pose proof NSC as NSS. apply stk_of_rw_cells in NSS. cbn [cells_size csize Nat.add] in NSS. replace (SPV + -112 + Z.of_nat 8) with (SPV + -112 + 8) in NSS by lia.
    clear NSC.
    replace (Z_to_bv 64 (SPV + -108)) with (Z_to_bv 64 (SPV + -112 + 4)) by (f_equal; lia).
    eapply evt_cut.
    { eapply (RSTATS _ gp tp _ _ _ _ _ _ _ _ _ _ _ s8 s9 s10 s11 _ _ _ _ F fc m0 (SPV + -176) (WK + 1236) WK (SPV + -112) SRC n (WK + 104) 876 lo WK wksz src);
        try eassumption; try lia.
      - replace (WK + 1236 + 256) with (WK + 1492) by lia. exact HWS.
      - replace (WK + 104 + 876) with (WK + 980) by lia. exact STS. }
    unfold huf_rstats_post. post_call psegs m0.
    rename x14 into r0. rename PC into STK'. rename PC0 into STS'. rename PC1 into R0R.
    zstep. zstep. if_cases K1; zify_cond K1.
    { (* [comment removed for export] *)
      destruct POST as [(RNE & _) | (RE & HWS' & RSS' & NSS')]; [exfalso; unfold zd_is_error, ZE_maxCode in RNE; apply Z.ltb_ge in RNE; lia|].
      zstep. zstep.
      eapply (x1_exit_stk _ dtb r0); try eassumption.
      - apply (stk_merge psegs _ WK (WK + 52) (WK + wksz) RSS'); [|lia].
        apply (stk_merge psegs _ (WK + 52) (WK + 104) (WK + wksz) RTS); [|lia].
        apply (stk_merge psegs _ (WK + 104) (WK + 980) (WK + wksz)); [replace (WK + 980) with (WK + 104 + 876) by lia; exact STS'| |lia].
        apply (stk_merge psegs _ (WK + 980) (WK + 1236) (WK + wksz) SYS); [|lia].
        apply (stk_merge psegs _ (WK + 1236) (WK + 1492) (WK + wksz)); [replace (WK + 1492) with (WK + 1236 + 256) by lia; exact HWS' | exact WKR | lia].
      - apply stk_of_rw_cells in F0. cbn [cells_size csize Nat.add] in F0.
        apply (stk_merge psegs _ (SPV + -176) (SPV + -112) (SPV + -104)); [replace (SPV + -112) with (SPV + -176 + Z.of_nat 64) by lia; exact F0 | | lia].
        replace (SPV + -104) with (SPV + -112 + 8) by lia. exact NSS'.
      - intros E. rewrite RE in E. discriminate E. }
    destruct POST as [(RNE & R0N & hw & rank & tl0 & nbs & HWC & HWLEN & HWBY & RK & NSC & SOK & NBR) | (RE & _)];
      [| exfalso; unfold zd_is_error, ZE_maxCode in RE; apply Z.ltb_lt in RE; lia].
    rewrite <- (bytes_of_unsigned dtb) in DTC.
    remember (map bv_unsigned dtb) as dt eqn:EDT.
    assert (DTL' : Z.of_nat (length dt) = 16388) by (subst dt; rewrite length_map; exact DTLEN).
    assert (DTBY : Forall (fun c => 0 <= c < 256) dt) by (subst dt; apply bytes_unsigned_range).
    assert (DTZ0 : Znth 0 dt = 12).
    { subst dt. unfold Znth. change (Z.to_nat 0) with 0%nat. destruct dtb as [|b0 t]; [discriminate DT0|]. cbn in DT0 |- *. injection DT0 as ->. reflexivity. }
    clear EDT.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => let a := cur_mem_addr in
      pose proof (u8_znth4 psegs mm DT dt 0 a (proj1 DTC) DTBY ltac:(lia) ltac:(lia) ltac:(addr_tac)) as RDH end.
    zstep.
    pose proof (Forall_Znth _ dt 1 DTBY ltac:(lia)) as B1. pose proof (Forall_Znth _ dt 2 DTBY ltac:(lia)) as B2. pose proof (Forall_Znth _ dt 3 DTBY ltac:(lia)) as B3. cbv beta in B1, B2, B3.
    rewrite DTZ0.
    remember (12 + 256 * Znth 1 dt + 65536 * Znth 2 dt + 16777216 * Znth 3 dt) as hdw eqn:EHDW.
    assert (HDWR : 0 <= hdw < 4294967296 /\ hdw mod 256 = 12) by (subst hdw; clear - B1 B2 B3; Z.div_mod_to_equations; lia).
    clear EHDW RDH.
    rewrite (zx32w_small hdw) by lia.
    zstep.
    replace (Z.land hdw 255) with 12 by (change 255 with (Z.ones 8); rewrite Z.land_ones by lia; change (2^8) with 256; lia).
    zstep. zstep. zstep. zstep. if_cases K2; zify_cond K2; [exfalso; lia|].
    zstep.
    zstep. zstep.
    pose proof SOK as (TL0R & _).
    rewrite (zx32w_small nbs) by lia. rewrite (sx32w_small tl0) by lia.
    zstep.
    rewrite (swrap32_small (nbs + 0)) by lia. replace (nbs + 0) with nbs by lia.
    assert (IM : X1M (Z_to_bv 64 876) flags (CB 8 fj2) (CB 8 fj3) (CB 8 fj4) (CB 8 fj5) (CB 8 fj6) (CB 8 fj7) (Z_to_bv 64 nbs) (Z_to_bv 64 tl0) dt hw rank x13).
    { unfold X1M, HUF_TBL_STACK, HUF_DTABLE_BYTES.
      assert (RKLEN : Z.of_nat (length rank) = 13) by (destruct SOK as (_ & _ & _ & L & _); exact L).
      replace (WK + 104 + 876) with (WK + 980) in STS' by lia.
      repeat (split; [first [eassumption | reflexivity]|]). eassumption. }
    zstep. if_cases K3; zify_cond K3.
    - (* [comment removed for export] *)
      zstep. if_cases K4; zify_cond K4.
      + (* [comment removed for export] *)
        assert (E11 : tl0 = 11) by lia. subst tl0.
        eapply x1_build with (hw := hw) (rank := rank) (tl := 11) (nbs := nbs) (hdw := hdw); try eassumption; try lia.
      + (* [comment removed for export] *)
        eapply x1_rescale with (hw := hw) (rank := rank) (tl0 := tl0) (sc := 11 - tl0) (nbs := nbs) (hdw := hdw); try eassumption; try lia.
        * intros i Hi. destruct SOK as (_ & _ & FA & _).
          assert (WSI : Znth i (firstn (Z.to_nat nbs) hw) = Znth i hw).
          { unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2. rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity. }
          rewrite <- WSI. apply (Forall_Znth _ _ i FA). rewrite length_firstn. lia.
        * intros v Hv. destruct SOK as (_ & (_ & LENW) & _ & _ & CNT & _). rewrite (CNT v Hv). unfold hcount.
          pose proof (count_occ_bound Z.eq_dec v (firstn (Z.to_nat nbs) hw)) as CB. unfold FseNCount.Zlength in LENW. lia.
    - (* [comment removed for export] *)
      zstep. zstep. if_cases K4; zify_cond K4; [|exfalso; lia].
      eapply x1_build with (hw := hw) (rank := rank) (tl := tl0) (nbs := nbs) (hdw := hdw); try eassumption; try lia.
  Qed.
End X1.

(* [comment removed for export] *)
Theorem huf_rdx1_proof : huf_rstats_stmt -> huf_rdx1_stmt.
Proof.
  intros RSTATS. unfold huf_rdx1_stmt, huf_rd_stmt_at. intros.
  eapply (huf_rdx1_body RSTATS); eassumption.
Qed.
