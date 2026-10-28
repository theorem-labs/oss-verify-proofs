(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_x2_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Lemma x8fw_hi16 : forall X v, X / 65536 = v -> (Z.shiftr X 16) mod 2^16 = v mod 2^16.
Proof.
  intros X v H. rewrite Z.shiftr_div_pow2 by lia. change (2^16) with 65536. rewrite H. reflexivity.
Qed.

Lemma x8fw_al : forall D q, D mod 2 = 0 -> Z.land (D + 4 + 4 * q) 1 = 0.
Proof.
  intros D q H. change 1 with (Z.ones 1). rewrite Z.land_ones by lia. change (2^1) with 2.
  Z.div_mod_to_equations. lia.
Qed.
Lemma x8fw_lor16 : forall a b, 0 <= a < 65536 -> 0 <= b < 65536 -> 0 <= Z.lor a b < 65536.
Proof.
  intros a b Ha Hb. assert (N : 0 <= Z.lor a b) by (apply Z.lor_nonneg; lia). split; [exact N|].
  destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [lia|].
  change 65536 with (2^16). apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) 16 ltac:(lia))).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - destruct (Z.eq_dec a 0) as [->|NA]; [cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 a 16 ltac:(lia))). change (2^16) with 65536. lia.
  - destruct (Z.eq_dec b 0) as [->|NB]; [cbn; lia|].
    apply (proj1 (Z.log2_lt_pow2 b 16 ltac:(lia))). change (2^16) with 65536. lia.
Qed.

Lemma x8fw_lo2 : forall sv bs M, 0 <= sv < 256 -> 0 <= bs < 65536 -> M = 2^64 -> 0 <= Z.lor ((Z.shiftl sv 8) mod M) bs < 65536.
Proof.
  intros sv bs M Hs Hb EM. subst M. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256.
  rewrite Z.mod_small by (change (2^64) with 18446744073709551616; lia). apply x8fw_lor16; lia.
Qed.

Lemma x8fw_lo2n : forall sv bs, 0 <= sv < 256 -> 0 <= bs < 65536 -> 0 <= Z.lor (Z.shiftl sv 8) bs < 65536.
Proof.
  intros sv bs Hs Hb. rewrite Z.shiftl_mul_pow2 by lia. change (2^8) with 256. apply x8fw_lor16; lia.
Qed.

Lemma x8fw_or_r : forall lo v, 0 <= lo < 65536 -> 0 <= v < 65536 ->
  0 <= Z.lor (v * 65536) lo < 4294967296 /\ Z.lor (v * 65536) lo / 65536 = v.
Proof.
  intros lo v Hl Hv. replace (v * 65536) with (v * 2^16) by reflexivity.
  rewrite lor_disj_add by ((try change (2^16) with 65536); lia).
  change (2^16) with 65536. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Lemma x8fw_or_l : forall lo v, 0 <= lo < 65536 -> 0 <= v < 65536 ->
  0 <= Z.lor lo (v * 65536) < 4294967296 /\ Z.lor lo (v * 65536) / 65536 = v.
Proof. intros lo v Hl Hv. rewrite Z.lor_comm. apply x8fw_or_r; assumption. Qed.

Lemma x8fw_rep_core : forall X v, 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= X * 4294967296 + X < 2^64
  /\ (Z.shiftr (X * 4294967296 + X) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (X * 4294967296 + X) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X v XR XV VR. subst v. rewrite !Z.shiftr_div_pow2 by lia.
  change (2^64) with 18446744073709551616. change (2^16) with 65536. change (2^48) with 281474976710656.
  split; [lia|]. split; Z.div_mod_to_equations; lia.
Qed.

Lemma x8fw_e1 : forall X, 0 <= X < 4294967296 -> Z.lor ((Z.shiftl X 32) mod 2^64) X = X * 4294967296 + X.
Proof.
  intros X XR. rewrite Z.shiftl_mul_pow2 by lia.
  rewrite (Z.mod_small (X * 2^32)) by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; lia).
  rewrite lor_disj_add by ((try change (2^32) with 4294967296); lia). reflexivity.
Qed.

Lemma x8fw_rep : forall X M v, M = 2^64 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) X < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) X) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) X) 48) mod 2^16 = v mod 2^16.
Proof. intros X M v EM XR XV VR. subst M. rewrite (x8fw_e1 X XR). apply x8fw_rep_core; assumption. Qed.

Lemma x8fw_rep_m : forall X M K v, M = 2^64 -> K = 2^32 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) (X mod K) < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (X mod K)) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (X mod K)) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X M K v EM EK XR XV VR. subst K. rewrite (Z.mod_small X (2^32)) by (change (2^32) with 4294967296; lia).
  apply x8fw_rep; assumption.
Qed.

Lemma x8fw_rep_s : forall X M M' v, M = 2^64 -> M' = 2^64 -> 0 <= X < 4294967296 -> X / 65536 = v -> 0 <= v < 65536 ->
  0 <= Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32) < 2^64
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32)) 16) mod 2^16 = v mod 2^16
  /\ (Z.shiftr (Z.lor ((Z.shiftl X 32) mod M) (Z.shiftr ((Z.shiftl X 32) mod M') 32)) 48) mod 2^16 = v mod 2^16.
Proof.
  intros X M M' v EM EM' XR XV VR. subst M'.
  replace (Z.shiftr ((Z.shiftl X 32) mod 2^64) 32) with X.
  - apply x8fw_rep; assumption.
  - rewrite Z.shiftl_mul_pow2 by lia.
    rewrite Z.mod_small by (change (2^32) with 4294967296; change (2^64) with 18446744073709551616; lia).
    rewrite Z.shiftr_div_pow2 by lia. rewrite Z.div_mul; [reflexivity | lia].
Qed.
Lemma x8_xlem : forall lo H v, 0 <= lo < 65536 -> 0 <= v < 65536 -> H = v * 65536 ->
  0 <= Z.lor lo H < 4294967296 /\ Z.lor lo H / 65536 = v.
Proof.
  intros lo H v Hl Hv EH. subst H. replace (v * 65536) with (v * 2^16) by reflexivity.
  rewrite Z.lor_comm. rewrite lor_disj_add by (try change (2^16) with 65536; lia).
  change (2^16) with 65536. split; [lia|]. Z.div_mod_to_equations. lia.
Qed.

Section L1.
  Variables (ra gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP DT SYM : Z) (m0 : fmem) (cw0 : list Z)
            (syb : list byte) (pos bg en nb bs : Z) (Q : machine_state -> Prop) (lv : Z).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTE : DT mod 2 = 0.
  Hypothesis SYL : 4096 <= SYM.  Hypothesis SYH : SYM + zlen syb < 2^47.
  Hypothesis SEP : DT + HUF_DTABLE_BYTES <= SYM \/ SYM + zlen syb <= DT.
  Hypothesis BGR : 0 <= bg <= en.  Hypothesis ENR : en <= zlen syb.  Hypothesis POSR : 0 <= pos.
  Hypothesis NBR : 0 <= nb <= 12.  Hypothesis BSR : 0 <= bs < 2^16.  Hypothesis LVR : lv = 1 \/ lv = 2.

  Notation ST pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition KE1 (n : Z) : Prop :=
    forall m' cw' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
      mem_inv usegs m' -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m' -> wmono usegs m0 m' ->
      x2_cells m' DT cw' -> cells_written cw0 cw' pos n (nb + 256 * lv) ->
      evt usegs Q (ST 0x259ec m' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).
  Ltac x8_uck :=
    let K := fresh "UK" in
    first [ if_cases K; zify_cond K; [exfalso; lia | clear K]
          | if_cases K; zify_cond K; [clear K | exfalso; lia] ].
  Ltac x8_ck := zstep; lazymatch goal with |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) => x8_uck | |- _ => idtac end.
  Ltac x8_byte :=
    first [ lia
          | match goal with |- context [bv_unsigned ?b] =>
              let BRG := fresh "BRG" in pose proof (bv_unsigned_in_range _ b) as BRG; unfold bv_modulus in BRG; cbn in BRG; lia end ].
  Ltac x8_lo :=
    first [ lia
          | apply x8fw_lo2; [lia | lia | reflexivity]
          | apply x8fw_lo2n; lia ].
  Ltac x8_xf :=
    lazymatch goal with |- 0 <= Z.lor ?lo ?H < _ /\ _ =>
      apply (x8_xlem lo H); [x8_lo | lia | lia] end.
  Ltac x8_df :=
    first [ apply x8fw_rep_m; first [reflexivity | assumption | lia]
          | apply x8fw_rep; first [reflexivity | assumption | lia]
          | apply x8fw_rep_s; first [reflexivity | assumption | lia] ].
  Ltac x8_st_lo CW i r := let w := reg_val r in lazymatch w with Z_to_bv 64 ?x => u16st CW i x; [reflexivity|] end.
  Ltac x8_st_hi CW i D16 D48 := u16st CW i (nb + 256 * lv); [first [exact D16 | exact D48]|].

  Lemma x2_l1_len8_k : forall j k m cw (A0 A1 A2 A3 HI : Z) (x8 x9 x18 x19 x20 x30 x31 : word),
    KE1 (8 * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + 8 * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (8 * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + 8 * k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A3 = 0 ->
    HI = lv * 2^24 + nb * 2^16 ->
    evt usegs Q (ST 0x256d8 m (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (-1)) x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 A3) (Z_to_bv 64 1) (Z_to_bv 64 bs) (Z_to_bv 64 lv) (Z_to_bv 64 (-9)) x18 x19 x20
                   (Z_to_bv 64 HI) (Z_to_bv 64 (-33)) x30 x31).
  Proof using All.
    unfold KE1. unfold HUF_DTABLE_BYTES in *.
    induction j as [|j IH]; intros k m cw A0 A1 A2 A3 HI x8 x9 x18 x19 x20 x30 x31 KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EA3 EHI;
      [exfalso; lia|].
    subst A0 A1 A2 A3.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 8 * k)) + 0)) by (f_equal; lia).
    remember (2 * (pos + 8 * k)) as b eqn:EB.
    lbyte SYB.
    lazymatch goal with |- _ => let v := reg_val 30 in lazymatch v with Z_to_bv 64 ?e =>
      assert (SVR : 0 <= e < 256) by x8_byte; remember e as sv eqn:ESV; clear ESV end end.
    zstep. if_cases KL; zify_cond KL; [assert (LV : lv = 1) by lia | assert (LV : lv = 2) by lia; zstep; zstep].
    all: x8_ck.
    all: zstep.
    all: lazymatch goal with |- _ => let v := reg_val 30 in lazymatch v with Z_to_bv 64 ?e =>
           assert (XF : 0 <= e < 4294967296 /\ e / 65536 = nb + 256 * lv) by x8_xf; remember e as X eqn:EX; clear EX end end.
    all: destruct XF as (XR & XV).
    all: zstep. all: zstep. all: zstep.
    all: lazymatch goal with |- _ => let v := reg_val 31 in lazymatch v with Z_to_bv 64 ?e =>
           assert (DF : 0 <= e < 2^64 /\ (Z.shiftr e 16) mod 2^16 = (nb + 256 * lv) mod 2^16 /\
                        (Z.shiftr e 48) mod 2^16 = (nb + 256 * lv) mod 2^16) by x8_df;
           remember e as D eqn:ED; clear ED end end.
    all: destruct DF as (DR & D16 & D48).
    all: zstep. all: zstep. all: zstep.
    all: x8_st_lo CW b 31. all: x8_st_hi CW (b + 1) D16 D48. all: x8_st_lo CW (b + 2) 8. all: x8_st_hi CW (b + 3) D16 D48.
    all: x8_ck.
    all: x8_st_lo CW (b + 4) 31. all: x8_st_hi CW (b + 5) D16 D48. all: x8_st_lo CW (b + 6) 8. all: x8_st_hi CW (b + 7) D16 D48.
    all: x8_ck.
    all: x8_st_lo CW (b + 8) 31. all: x8_st_hi CW (b + 9) D16 D48. all: x8_st_lo CW (b + 10) 8. all: x8_st_hi CW (b + 11) D16 D48.
    all: x8_ck.
    all: x8_st_lo CW (b + 12) 31. all: x8_st_hi CW (b + 13) D16 D48. all: x8_st_lo CW (b + 14) 8. all: x8_st_hi CW (b + 15) D16 D48.
    all: lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    all: assert (RND : cells_written cw cw' (pos + 8 * k) 8 (nb + 256 * lv)) by (subst cw' b; cw_round).
    all: pose proof (cells_written_app cw0 cw cw' pos (8 * k) 8 (nb + 256 * lv) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    all: assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    all: clear ECW' RND.
    all: x8_ck. all: x8_ck.
    all: zstep. all: zstep.
    all: zstep. all: if_cases KB; zify_cond KB.
    all: first
      [ assert (KX : k + 1 = en - bg) by lia; zstep;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (KE mm cw') end;
        [ exact MI | exact MU | exact WM | split; assumption | replace (8 * (en - bg)) with (8 * k + 8) by lia; exact CWR' ]
      | replace (8 * k + 8) with (8 * (k + 1)) in CWR' by lia;
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => eapply (IH (k + 1) mm cw') end;
        first [ eassumption | split; eassumption | reflexivity | lia ] ].
  Qed.

End L1.
