(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdSeqTable.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require FseNCountRT.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require SysStep.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX SepHide.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg F_memset RZ_huf_iface RZ_hft_iface RZ_hft_rs_iface RZ_hft_kit RZ_hft_bdt_defs RZ_hft_x1_kit huf411_kit_x1_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section X1.
  Variables (ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : fmem)
            (SPV n DT WK wksz lo : Z).
  Hypothesis LO0 : 4096 <= lo.  Hypothesis LOS : lo <= SPV - HUF_TBL_STACK.  Hypothesis SPR : SPV < 2^47.  Hypothesis SP16 : SPV mod 16 = 0.
  Hypothesis NR : n < 2^32.
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTAL : DT mod 4 = 0.
  Hypothesis WKL : 4096 <= WK.  Hypothesis WKSZ : 0 <= wksz < 2^32.  Hypothesis WKH : WK + wksz < 2^47.  Hypothesis WKAL : WK mod 4 = 0.
  Hypothesis OFFDT : DT + HUF_DTABLE_BYTES <= lo \/ SPV <= DT.  Hypothesis OFFWK : WK + wksz <= lo \/ SPV <= WK.
  Hypothesis DTWK : DT + HUF_DTABLE_BYTES <= WK \/ WK + wksz <= DT.
  Hypothesis WK1492 : 1492 <= wksz.

  Notation POST := (huf_rd_post ra gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc SPV DT WK wksz lo false m).
  Notation STF pc mm x1 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31 :=
    (MS (mkR x1 (Z_to_bv 64 (SPV + -240)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).
  Notation SAVED := [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra].
  Variables (flags : word) (f16 f24 f32 f40 f48 f56 f64 f72 f80 f88 f104 f112 f120 : list byte).
  Variables (hw rank : list Z) (nbs tl r0 : Z).
  Hypothesis STOK : huf_stats_ok (firstn (Z.to_nat nbs) hw) rank tl.
  Hypothesis NBR : 2 <= nbs <= 256.  Hypothesis R0R : 1 <= r0 <= n.
  Hypothesis HWLEN : Z.of_nat (length hw) = 256.  Hypothesis HWBY : Forall isbyte hw.  Hypothesis RKLEN : Z.of_nat (length rank) = 13.
  Notation X1S fl wn wt dt rst syb m1 := (x1s DT WK wksz SPV lo m SAVED hw rank fl wn wt dt rst syb m1).
  Notation X1M fl wn wt dt hw' rank' m1 := (x1m DT WK wksz SPV lo m SAVED fl wn wt dt hw' rank' m1).
  Notation FLB :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; CB 8 f24; CB 8 f32; CB 8 f40; CB 8 f48; CB 8 f56; CB 8 f64; CB 8 f72;
     CB 8 f80; CB 8 f88; C8 (Z_to_bv 64 WK); CB 8 f104; CB 8 f112; CB 8 f120].
  Notation FLS :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); CB 8 f32; CB 8 f40; C8 (Z_to_bv 64 DT); CB 8 f56; CB 8 f64;
     C8 (Z_to_bv 64 (tl + 1)); CB 8 f80; CB 8 f88; C8 (Z_to_bv 64 WK); CB 8 f104; CB 8 f112; CB 8 f120].
  Notation FLF cur sym c104 c112 :=
    [C8 (Z_to_bv 64 876); C8 flags; CB 8 f16; C8 (Z_to_bv 64 r0); C8 (Z_to_bv 64 ux1_K32); C8 (Z_to_bv 64 (DT + 20));
     C8 (Z_to_bv 64 DT); C8 (Z_to_bv 64 (tl + 1)); C8 (Z_to_bv 64 (- (WK + 1))); C8 (Z_to_bv 64 (tl + 1));
     C8 (Z_to_bv 64 cur); C8 (Z_to_bv 64 sym); C8 (Z_to_bv 64 WK); c104; c112; C8 (Z_to_bv 64 ux1_K120)].

  Ltac open_x1s I := unfold x1s in I; destruct I as (DTC & DTLEN & DTBY & HWC & RK & RST & RSTLEN & STS & SYC & SYLEN & WKR & F0 & F0SZ & NSC & FSAV & STK & MI & MU & WM);
                     unfold HUF_TBL_STACK, HUF_DTABLE_BYTES in *.
  Ltac close_x1s := unfold x1s, HUF_TBL_STACK, HUF_DTABLE_BYTES; repeat (split; [eassumption|]); eassumption.
  Ltac kchk K := exfalso; rewrite ?zb_lxor_ones, ?swrap32_small, ?signed_lit in K by lia; repeat (rewrite Z.mod_small in K by lia); lia.
  Ltac chk := let K := fresh "K" in zstep; if_cases K; zify_cond K; [kchk K|]; try clear K.
  Ltac kfalse K := exfalso; revert K; repeat match goal with |- context [?a <? ?b] => destruct (Z.ltb_spec a b) end;
                   cbn; intro K; first [discriminate K | lia].
  Ltac zk K := zify_cond K; rewrite ?swrap32_small, ?signed_lit in K by lia; repeat (rewrite Z.mod_small in K by lia).

  Notation N52 := (Z_to_bv 64 (Z.lxor (WK + 52) 18446744073709551615)).
  Notation N980 := (Z_to_bv 64 (Z.lxor (WK + 980) 18446744073709551615)).
  Notation N1236 := (Z_to_bv 64 (Z.lxor (WK + 1236) 18446744073709551615)).

  Lemma modneg : forall z b, 0 < b -> - b <= z < 0 -> z mod b = z + b.
  Proof. intros z b Hb Hz. rewrite <- (Z.mod_add z 1 b) by lia. rewrite Z.mod_small by lia. lia. Qed.

  Notation ws := (firstn (Z.to_nat nbs) hw).
  Lemma ws_len : FseNCount.Zlength ws = nbs.
  Proof. unfold FseNCount.Zlength. rewrite length_firstn. lia. Qed.
  Lemma ws_nth : forall i, 0 <= i < nbs -> Znth i ws = Znth i hw.
  Proof.
    intros i Hi. unfold Znth. rewrite <- (firstn_skipn (Z.to_nat nbs) hw) at 2.
    rewrite app_nth1 by (rewrite length_firstn; lia). reflexivity.
  Qed.

  Definition SORT (i : Z) (rst : list Z) : Prop :=
    forall v, 0 <= v <= tl -> Znth v rst = xsym rank v + hcount (firstn (Z.to_nat i) ws) v.

  Definition KS (wn wt : word) (dt : list Z) : Prop :=
    forall m2 rst' syb' y1 y5 y6 y7 y8 y9 y10 y11 y12 y14 y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
      X1S FLS wn wt dt rst' syb' m2 ->
      evt usegs POST (STF 0x1ecc0 m2 y1 y5 y6 y7 y8 y9 y10 y11 y12 (Z_to_bv 64 (WK + 980)) y14 (Z_to_bv 64 tl) y16 y17 y18 (Z_to_bv 64 (DT + 4)) y20
                           y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31).

  Ltac close_cur I' wn wt dt :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with RS : u32arr _ mm (WK + 52) (map _ ?r), SY : u8arr _ mm (WK + 980) ?s |- _ =>
        assert (I' : X1S FLS wn wt dt r s mm) by close_x1s
      end
    end.

  Lemma x1_sort_tail : forall j m1 dt rst syb wn wt i x1 x6 x7 x8 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KS wn wt dt -> Z.to_nat (nbs - i) = j -> X1S FLS wn wt dt rst syb m1 -> 0 <= i < nbs -> SORT i rst ->
    evt usegs POST (STF 0x1ec6c m1 x1 N52 x6 x7 x8 (Z_to_bv 64 (WK + 1236)) N980 (Z_to_bv 64 13) (Z_to_bv 64 i) (Z_to_bv 64 (WK + 980))
                         (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 255) x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK)
                         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KF EJ I IR INV; [exfalso; lia|].
    open_x1s I. pose proof STOK as (TLR & _).
    destruct (sort_slot _ _ _ STOK i (Znth i hw) ltac:(rewrite ws_len; lia) (ws_nth i IR)) as (WR & SLOT). rewrite ws_len in SLOT.
    pose proof (sort_step _ _ _ STOK i (Znth i hw) rst ltac:(rewrite ws_len; lia) (ws_nth i IR) ltac:(unfold FseNCount.Zlength; lia) INV) as INV'.
    rewrite <- (INV (Znth i hw) WR) in SLOT.
    remember (Znth i hw) as w eqn:EW.
    zstep. chk.
    zstep. zstep. zstep. zstep.
    zstep. if_cases K; zify_cond K; [rewrite lxor_sign_small in K by lia; kfalse K|]. try clear K.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u8_znth usegs m1 (WK + 1236) hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end.
    rewrite <- EW in RD.
    zstep. cbv beta. rewrite (byte_lit w) by lia. clear RD.
    chk.
    zstep. replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia).
    chk.
    zstep.
    lazymatch goal with |- _ => let a := cur_mem_addr in
      pose proof (u32_znth usegs m1 (WK + 52) rst w a RST ltac:(lia) ltac:(addr_tac)) as RD2 end.
    zstep. rewrite (sx32w_small (Znth w rst)) by lia. clear RD2.
    zstep.
    u32st2 RST w (Znth w rst + 1) (Znth w rst + 1).
    change (upd_nat (Z.to_nat w) (Znth w rst + 1) rst) with (Zupd w (Znth w rst + 1) rst) in RST.
    assert (RSTLEN' : Z.of_nat (length (Zupd w (Znth w rst + 1) rst)) = 13) by (rewrite Zupd_length; exact RSTLEN).
    chk. chk.
    zstep.
    outst SYC SYLEN.
    zstep.
    close_cur I' wn wt dt.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH _ dt _ _ wn wt (i + 1)); [exact KF | lia | exact I' | lia | exact INV'].
    - eapply KF. exact I'.
  Qed.

  Lemma x1_sort_tail0 : forall m1 dt rst syb wn wt i x1 x6 x7 x8 x10 x11 x17 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    KS wn wt dt -> X1S FLS wn wt dt rst syb m1 -> 0 <= i < nbs -> SORT i rst ->
    evt usegs POST (STF 0x1ec60 m1 x1 N52 x6 x7 x8 (Z_to_bv 64 (WK + 1236)) x10 x11 (Z_to_bv 64 i) (Z_to_bv 64 (WK + 980))
                         (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 52)) x17 x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK)
                         x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros KF I IR INV.
    zstep. zstep. zstep.
    eapply (x1_sort_tail (Z.to_nat (nbs - i)) m1 dt rst syb wn wt i); [exact KF | reflexivity | exact I | lia | exact INV].
  Qed.

  Tactic Notation "sort_facts" constr(INV) constr(i) ident(w) ident(WR) ident(SLOT) ident(INV') ident(EW) :=
    lazymatch type of INV with SORT _ ?rs =>
      destruct (sort_slot _ _ _ STOK i (Znth i hw) ltac:(rewrite ws_len; lia) (ws_nth i ltac:(lia))) as (WR & SLOT); rewrite ws_len in SLOT;
      pose proof (sort_step _ _ _ STOK i (Znth i hw) rs ltac:(rewrite ws_len; lia) (ws_nth i ltac:(lia))
                    ltac:(unfold FseNCount.Zlength; rewrite ?Zupd_length; lia) INV) as INV';
      change (SORT (i + 1) (Zupd (Znth i hw) (Znth (Znth i hw) rs + 1) rs)) in INV';
      rewrite <- (INV (Znth i hw) WR) in SLOT;
      remember (Znth i hw) as w eqn:EW
    end.

  Tactic Notation "usort" hyp(HWC) hyp(RST) hyp(SYC) hyp(SYLEN) constr(i) constr(w) hyp(EW) integer(k) :=
    let RD := fresh "RD" in let RD2 := fresh "RD" in
    lazymatch type of HWC with u8arr _ ?mm _ _ =>
      (lazymatch goal with |- _ => let a := cur_mem_addr in
        pose proof (u8_znth usegs mm (WK + 1236) hw i a HWC ltac:(lia) ltac:(addr_tac)) as RD end);
      rewrite <- EW in RD;
      zstep; cbv beta; rewrite (byte_lit w) by lia; clear RD;
      chk;
      zstep; replace (w ≪ 2) with (4 * w) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
      chk;
      zstep;
      lazymatch type of RST with u32arr _ _ _ (map _ ?rs) =>
        (lazymatch goal with |- _ => let a := cur_mem_addr in
          pose proof (u32_znth usegs mm (WK + 52) rs w a RST ltac:(rewrite ?Zupd_length; lia) ltac:(addr_tac)) as RD2 end);
        zstep; rewrite (sx32w_small (Znth w rs)) by lia; clear RD2;
        zstep;
        u32st2 RST w (Znth w rs + 1) (Znth w rs + 1);
        change (upd_nat (Z.to_nat w) (Znth w rs + 1) rs) with (Zupd w (Znth w rs + 1) rs) in RST;
        chk; chk;
        do k zstep;
        outst SYC SYLEN;
        let rsn := fresh "rst" in let ER := fresh "ER" in let RL := fresh "RSTLEN" in
        remember (Zupd w (Znth w rs + 1) rs) as rsn eqn:ER;
        assert (RL : Z.of_nat (length rsn) = 13) by (subst rsn; rewrite Zupd_length; assumption);
        clear ER
      end
    end.

  Lemma x1_sort4 : forall j m1 dt rst syb wn wt i x1 x8 x12 x18 x21 x22 x23 x24 x25 x26 x27 x29 x30 x31,
    KS wn wt dt -> (Z.to_nat (nbs - i) <= j)%nat -> X1S FLS wn wt dt rst syb m1 -> 0 <= i -> i + 3 < nbs -> SORT i rst ->
    evt usegs POST (STF 0x1eb48 m1 x1 N52 (Z_to_bv 64 13) (Z_to_bv 64 255) x8 (Z_to_bv 64 (WK + 1236)) N980 N1236 x12 (Z_to_bv 64 (WK + 980))
                         (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 52)) (Z_to_bv 64 (nbs + -4)) x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK)
                         x21 x22 x23 x24 x25 x26 x27 (Z_to_bv 64 i) x29 x30 x31).
  Proof.
    induction j as [|j IH]; intros until x31; intros KF EJ I I0 I3 INV; [exfalso; lia|].
    open_x1s I. pose proof STOK as (TLR & _).
    chk.
    zstep. zstep.
    sort_facts INV i w0 WR0 SLOT0 INV1 EW0.
    usort HWC RST SYC SYLEN i w0 EW0 1.
    chk.
    sort_facts INV1 (i + 1) w1 WR1 SLOT1 INV2 EW1.
    usort HWC RST SYC SYLEN (i + 1) w1 EW1 3.
    chk.
    sort_facts INV2 (i + 1 + 1) w2 WR2 SLOT2 INV3 EW2.
    usort HWC RST SYC SYLEN (i + 1 + 1) w2 EW2 2.
    chk.
    sort_facts INV3 (i + 1 + 1 + 1) w3 WR3 SLOT3 INV4 EW3.
    usort HWC RST SYC SYLEN (i + 1 + 1 + 1) w3 EW3 4.
    replace (i + 1 + 1 + 1 + 1) with (i + 4) in INV4 by lia.
    setreg 12 (Z_to_bv 64 (i + 4)) ltac:(f_equal; rewrite ?swrap32_small by lia; lia).
    setreg 31 (Z_to_bv 64 i) ltac:(f_equal; rewrite ?swrap32_small by lia; lia).
    chk.
    zstep. zstep.
    setreg 28 (Z_to_bv 64 (i + 4)) ltac:(f_equal; lia).
    close_cur I' wn wt dt.
    zstep. if_cases KB; zk KB.
    - eapply (IH _ dt _ _ wn wt (i + 4)); [exact KF | lia | exact I' | lia | lia | exact INV4].
    - zstep. if_cases KC; zk KC.
      + eapply (x1_sort_tail0 _ dt _ _ wn wt (i + 4)); [exact KF | exact I' | lia | exact INV4].
      + zstep. eapply KF. exact I'.
  Qed.


  Lemma x1_sort : forall m1 dt rst syb wn wt x1 x5 x6 x7 x8 x10 x11 x12 x13 x18 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31,
    X1S FLS wn wt dt rst syb m1 -> (forall v, 0 <= v <= tl -> Znth v rst = xsym rank v) ->
    (forall m2 rst' syb' y1 y5 y6 y7 y8 y9 y10 y11 y12 y14 y16 y17 y18 y20 y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31,
       X1S FLS wn wt dt rst' syb' m2 ->
       evt usegs POST (STF 0x1ecc0 m2 y1 y5 y6 y7 y8 y9 y10 y11 y12 (Z_to_bv 64 (WK + 980)) y14 (Z_to_bv 64 tl) y16 y17 y18 (Z_to_bv 64 (DT + 4)) y20
                            y21 y22 y23 y24 y25 y26 y27 y28 y29 y30 y31)) ->
    evt usegs POST (STF 0x1eb24 m1 x1 x5 x6 x7 x8 (Z_to_bv 64 (WK + 1236)) x10 x11 x12 x13 (Z_to_bv 64 nbs) (Z_to_bv 64 tl) (Z_to_bv 64 (WK + 52))
                         (Z_to_bv 64 (nbs + -4)) x18 (Z_to_bv 64 (DT + 4)) (Z_to_bv 64 WK) x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).
  Proof.
    intros until x31; intros I RS0 KONT.
    assert (KF : KS wn wt dt) by exact KONT.
    assert (INV : SORT 0 rst) by (intros v Hv; rewrite (RS0 v Hv); change (Z.to_nat 0) with 0%nat; cbn [firstn]; rewrite hcount_nil; lia).
    pose proof I as J. open_x1s J.
    zstep. zstep. zstep. zstep. if_cases KA; zify_cond KA.
    - zstep. zstep. if_cases KB; zify_cond KB; [kfalse KB|]. try clear KB.
      eapply (x1_sort_tail0 m1 dt rst syb wn wt 0); [exact KF | exact I | lia | exact INV].
    - assert (N4 : 4 <= nbs) by (destruct (Z_lt_le_dec nbs 4) as [LT|]; [rewrite modneg in KA by lia; lia | lia]).
      zstep. zstep. zstep. zstep. zstep.
      eapply (x1_sort4 (Z.to_nat (nbs - 0)) m1 dt rst syb wn wt 0); [exact KF | lia | exact I | lia | lia | exact INV].
  Qed.
End X1.
