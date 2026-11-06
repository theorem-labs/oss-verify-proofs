(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Plain Require Import PImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Section L1.
  Variables (gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 : word) (F : bvmap 5 word) (fc : bv 32) (SPF DT SYM : Z) (m0 : fmem) (cw0 : list Z).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + 16388 < 2^47.
  Hypothesis SYML : 4096 <= SYM.  Hypothesis SYMH : SYM + 256 < 2^47.
  Hypothesis SEP : DT + 16388 <= SYM \/ SYM + 256 <= DT.
  Variables (syb : list byte) (pos cnt bg nb : Z).
  Hypothesis SYLEN : Z.of_nat (length syb) = 256.
  Hypothesis POSR : 0 <= pos.  Hypothesis BGR : 0 <= bg.  Hypothesis BGH : bg + cnt <= 256.  Hypothesis NBR : 0 <= nb <= 12.

  Notation ST pc mm x1 x5 x7 x8 x9 x10 x11 x12 x13 x14 x16 x17 x21 x22 x25 x26 x27 x28 x29 :=
    (MS (mkR x1 (Z_to_bv 64 SPF) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom psegs)).

  (* [comment removed for export] *)
  Lemma x2_l1_len1 : forall j m cw s x1 x5 x7 x8 x9 x13 x17 x21 x22 x25 x26 x27 x28 x29,
    Z.to_nat (cnt - s) = j -> 0 <= s < cnt -> pos + cnt <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos s (nb + 256) ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos cnt (nb + 256))
      (ST 0x1d91c m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + s))) x13
          (Z_to_bv 64 (cnt - s)) (Z_to_bv 64 (nb + 256)) x17 x21 x22 x25 x26 x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ SR PH MI MU WM (CW & CWL) SYB CWR; [exfalso; lia|].
    lbyte SYB.
    u16st CW (2 * (pos + s) + 1) (nb + 256); [reflexivity|].
    zstep.
    lazymatch goal with |- _ => let v := reg_val 17 in lazymatch v with Z_to_bv 64 ?e => remember e as sq eqn:ESQ; clear ESQ end end.
    u16st CW (2 * (pos + s)) sq; [reflexivity|].
    zstep. zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + s) 1 (nb + 256)) by (subst cw'; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos s 1 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (SYM + bg + s + 1)) with (Z_to_bv 64 (SYM + bg + (s + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (cnt - s + -1)) with (Z_to_bv 64 (cnt - (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 12 in replace v with (Z_to_bv 64 (DT + 4 + 4 * (pos + (s + 1)))) by (f_equal; lia) end.
      eapply (IH m cw' (s + 1)); try eassumption; try lia. split; assumption.
    - zstep. apply evt_done. unfold x2_l1_post. do 19 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace cnt with (s + 1) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len2 : forall j m cw s x1 x5 x7 x8 x9 x13 x16 x17 x21 x22 x25 x26 x27 x28 x29,
    Z.to_nat (cnt - s) = j -> 0 <= s < cnt -> pos + 2 * cnt <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos (2 * s) (nb + 256) ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (2 * cnt) (nb + 256))
      (ST 0x1d2c8 m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + 2 * s))) x13
          (Z_to_bv 64 (cnt - s)) x16 x17 x21 x22 x25 x26 x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ SR PH MI MU WM (CW & CWL) SYB CWR; [exfalso; lia|].
    lbyte SYB. zstep. zstep. zstep.
    replace ((nb * 65536 + 16777216) ≫ 16) with (nb + 256) by (rewrite Z.shiftr_div_pow2 by lia; change (2^16) with 65536; Z.div_mod_to_equations; lia).
    lazymatch goal with |- _ => let v := reg_val 16 in lazymatch v with Z_to_bv 64 ?e => remember e as sq eqn:ESQ; clear ESQ end end.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 2 * s))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 2 * s)) + 0)) by (f_equal; lia).
    u16st CW (2 * (pos + 2 * s)) sq; [reflexivity|].
    u16st CW (2 * (pos + 2 * s) + 1) (nb + 256); [reflexivity|].
    u16st CW (2 * (pos + 2 * s) + 2) sq; [reflexivity|].
    u16st CW (2 * (pos + 2 * s) + 3) (nb + 256); [reflexivity|].
    zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 2 * s) 2 (nb + 256)) by (subst cw'; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (2 * s) 2 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (SYM + bg + s + 1)) with (Z_to_bv 64 (SYM + bg + (s + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (cnt - s + -1)) with (Z_to_bv 64 (cnt - (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 12 in replace v with (Z_to_bv 64 (DT + 4 + 4 * (pos + 2 * (s + 1)))) by (f_equal; lia) end.
      replace (2 * s + 2) with (2 * (s + 1)) in CWR' by lia.
      eapply (IH m cw' (s + 1)); try eassumption; try lia. split; assumption.
    - zstep. apply evt_done. unfold x2_l1_post. do 19 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace (2 * cnt) with (2 * s + 2) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len4 : forall j m cw s x1 x5 x7 x8 x9 x13 x16 x17 x21 x22 x25 x26 x27 x28 x29,
    Z.to_nat (cnt - s) = j -> 0 <= s < cnt -> pos + 4 * cnt <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos (4 * s) (nb + 256) ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (4 * cnt) (nb + 256))
      (ST 0x1d954 m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * s))) x13
          (Z_to_bv 64 (cnt - s)) x16 x17 x21 x22 x25 x26 x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ SR PH MI MU WM (CW & CWL) SYB CWR; [exfalso; lia|].
    lbyte SYB. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (BR : 0 <= nb * 65536 + 16777216 < 4294967296) by lia.
    assert (BH : (nb * 65536 + 16777216) / 65536 = nb + 256) by (Z.div_mod_to_equations; lia).
    rewrite (wrap32_small (nb * 65536 + 16777216)) by lia.
    replace ((nb * 65536 + 16777216) ≫ 16) with (nb + 256) by (rewrite Z.shiftr_div_pow2 by lia; exact (eq_sym BH)).
    rewrite (swrap32_small (nb + 256)) by lia.
    lazymatch goal with |- _ => let v := reg_val 16 in lazymatch v with Z_to_bv 64 ?e =>
      assert (X0 : 0 <= e) by (apply Z.lor_nonneg; split; [lia | apply bv_unsigned_in_range]);
      remember e as sq eqn:ESQ; clear ESQ end end.
    pose proof (x2_t0_word sq (nb * 65536 + 16777216) X0 BR) as T0W. rewrite BH in T0W.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => remember e as t0v eqn:ET0; clear ET0 end end.
    replace ((nb + 256) mod 2^16) with (nb + 256) in T0W by (rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]).
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * s))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 4 * s)) + 0)) by (f_equal; lia).
    remember (2 * (pos + 4 * s)) as b eqn:EB.
    u16st CW b sq; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 2) sq; [reflexivity|].
    u16st CW (b + 3) (nb + 256); [reflexivity|].
    u16st CW (b + 4) sq; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 6) sq; [reflexivity|].
    u16st CW (b + 7) (nb + 256); [reflexivity|].
    zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 4 * s) 4 (nb + 256)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (4 * s) 4 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND T0W.
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (SYM + bg + s + 1)) with (Z_to_bv 64 (SYM + bg + (s + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (cnt - s + -1)) with (Z_to_bv 64 (cnt - (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 12 in replace v with (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * (s + 1)))) by (f_equal; lia) end.
      replace (4 * s + 4) with (4 * (s + 1)) in CWR' by lia.
      eapply (IH m cw' (s + 1)); try eassumption; try lia. split; assumption.
    - zstep. apply evt_done. unfold x2_l1_post. do 19 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace (4 * cnt) with (4 * s + 4) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len8 : forall j m cw s x1 x5 x7 x8 x9 x13 x16 x17 x21 x22 x25 x26 x27 x28 x29,
    Z.to_nat (cnt - s) = j -> 0 <= s < cnt -> pos + 8 * cnt <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos (8 * s) (nb + 256) ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (8 * cnt) (nb + 256))
      (ST 0x1d474 m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * s))) x13
          (Z_to_bv 64 (cnt - s)) x16 x17 x21 x22 x25 x26 x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros EJ SR PH MI MU WM (CW & CWL) SYB CWR; [exfalso; lia|].
    lbyte SYB. zstep. zstep. zstep. zstep. zstep. zstep.
    assert (BR : 0 <= nb * 65536 + 16777216 < 4294967296) by lia.
    assert (BH : (nb * 65536 + 16777216) / 65536 = nb + 256) by (Z.div_mod_to_equations; lia).
    rewrite (wrap32_small (nb * 65536 + 16777216)) by lia.
    replace ((nb * 65536 + 16777216) ≫ 16) with (nb + 256) by (rewrite Z.shiftr_div_pow2 by lia; exact (eq_sym BH)).
    rewrite (swrap32_small (nb + 256)) by lia.
    lazymatch goal with |- _ => let v := reg_val 16 in lazymatch v with Z_to_bv 64 ?e =>
      assert (X0 : 0 <= e) by (apply Z.lor_nonneg; split; [lia | apply bv_unsigned_in_range]);
      remember e as sq eqn:ESQ; clear ESQ end end.
    pose proof (x2_t0_word sq (nb * 65536 + 16777216) X0 BR) as T0W. rewrite BH in T0W.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => remember e as t0v eqn:ET0; clear ET0 end end.
    replace ((nb + 256) mod 2^16) with (nb + 256) in T0W by (rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]).
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * s))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 8 * s)) + 0)) by (f_equal; lia).
    remember (2 * (pos + 8 * s)) as b eqn:EB.
    u16st CW b sq; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 2) sq; [reflexivity|].
    u16st CW (b + 3) (nb + 256); [reflexivity|].
    u16st CW (b + 4) sq; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 6) sq; [reflexivity|].
    u16st CW (b + 7) (nb + 256); [reflexivity|].
    u16st CW (b + 8) sq; [reflexivity|].
    u16st CW (b + 9) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 10) sq; [reflexivity|].
    u16st CW (b + 11) (nb + 256); [reflexivity|].
    u16st CW (b + 12) sq; [reflexivity|].
    u16st CW (b + 13) (nb + 256); [rewrite T0W; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 14) sq; [reflexivity|].
    u16st CW (b + 15) (nb + 256); [reflexivity|].
    zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 8 * s) 8 (nb + 256)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (8 * s) 8 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND T0W.
    zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (SYM + bg + s + 1)) with (Z_to_bv 64 (SYM + bg + (s + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (cnt - s + -1)) with (Z_to_bv 64 (cnt - (s + 1))) by (f_equal; lia).
      lazymatch goal with |- _ => let v := reg_val 12 in replace v with (Z_to_bv 64 (DT + 4 + 4 * (pos + 8 * (s + 1)))) by (f_equal; lia) end.
      replace (8 * s + 8) with (8 * (s + 1)) in CWR' by lia.
      eapply (IH m cw' (s + 1)); try eassumption; try lia. split; assumption.
    - zstep. apply evt_done. unfold x2_l1_post. do 19 eexists. exists m, cw'.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [split; assumption|].
      replace (8 * cnt) with (8 * s + 8) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Definition KS1 (len s off : Z) : Prop :=
    forall m' cw' x1 x5 x7 x8 x9 x13 x16 x17 x21 x22 x25 x27 x28 x29,
      mem_inv psegs m' -> munch [(DT + 4, DT + 16388)] m0 m' -> wmono psegs m0 m' ->
      x2_cells m' DT cw' -> bytes_at psegs m' SYM syb -> cells_written cw0 cw' pos (off + len) (nb + 256) ->
      evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (len * cnt) (nb + 256))
        (ST 0x1d8f8 m' x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + off + len))) x13
            (Z_to_bv 64 (4 * len)) x16 x17 x21 x22 x25 (Z_to_bv 64 (SYM + bg + cnt)) x27 x28 x29).

  Lemma x2_l1_def_in : forall j m cw len s off q Q D x1 x5 x7 x8 x9 x13 x21 x22 x25 x27 x28 x29,
    KS1 len s off -> len = 8 * Q -> Z.to_nat (Q - q) = j -> 0 <= q < Q -> 0 <= off -> pos + off + len <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos (off + 8 * q) (nb + 256) ->
    0 <= D < 18446744073709551616 -> (D ≫ 16) mod 2^16 = nb + 256 -> (D ≫ 48) mod 2^16 = nb + 256 ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (len * cnt) (nb + 256))
      (ST 0x1d8a4 m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + off + len))) x13
          (Z_to_bv 64 (4 * len)) (Z_to_bv 64 (DT + 4 + 4 * (pos + off + 8 * q))) (Z_to_bv 64 D) x21 x22 x25 (Z_to_bv 64 (SYM + bg + cnt)) x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros KS L8 EJ QR OFF0 OFFH MI MU WM (CW & CWL) SYB CWR DR W1 W3; [exfalso; lia|].
    hide W1. hide W3.
    zstep. zstep. zstep.
    remember (4 * (pos + off + 8 * q)) as b4 eqn:EB4.
    replace (Z_to_bv 64 (DT + 4 + b4)) with (Z_to_bv 64 (DT + 4 + 2 * (b4 / 2) + 0)) by (f_equal; subst b4; Z.div_mod_to_equations; lia).
    assert (EBW : b4 / 2 = 2 * (pos + off + 8 * q)) by (subst b4; Z.div_mod_to_equations; lia).
    remember (b4 / 2) as b eqn:EB. clear EB EB4.
    remember (D mod 2^16) as sq0 eqn:ESQ0. remember ((D ≫ 32) mod 2^16) as sq2 eqn:ESQ2.
    clear ESQ0 ESQ2 sq0 sq2.
    u16st CW b D; [reflexivity|].
    u16st CW (b + 1) (nb + 256); [unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 2) (D ≫ 32); [reflexivity|].
    u16st CW (b + 3) (nb + 256); [unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 4) D; [reflexivity|].
    u16st CW (b + 5) (nb + 256); [unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 6) (D ≫ 32); [reflexivity|].
    u16st CW (b + 7) (nb + 256); [unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 8) D; [reflexivity|].
    u16st CW (b + 9) (nb + 256); [unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 10) (D ≫ 32); [reflexivity|].
    u16st CW (b + 11) (nb + 256); [unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 12) D; [reflexivity|].
    u16st CW (b + 13) (nb + 256); [unfold hidden in W1; rewrite W1; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    u16st CW (b + 14) (D ≫ 32); [reflexivity|].
    u16st CW (b + 15) (nb + 256); [unfold hidden in W3; rewrite W3; rewrite Z.mod_small; [reflexivity | change (2^16) with 65536; lia]|].
    zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + off + 8 * q) 8 (nb + 256)) by (subst cw'; rewrite EBW; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (off + 8 * q) 8 (nb + 256) POSR ltac:(lia) ltac:(lia) CWR ltac:(replace (pos + (off + 8 * q)) with (pos + off + 8 * q) by lia; exact RND)) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. if_cases KB; zify_cond KB.
    - lazymatch goal with |- _ => let v := reg_val 16 in replace v with (Z_to_bv 64 (DT + 4 + 4 * (pos + off + 8 * (q + 1)))) by (f_equal; lia) end.
      replace (off + 8 * q + 8) with (off + 8 * (q + 1)) in CWR' by lia.
      unfold hidden in W1, W3.
      eapply (IH m cw' len s off (q + 1) Q D); try eassumption; try lia. split; assumption.
    - replace (off + 8 * q + 8) with (off + len) in CWR' by lia.
      eapply KS; try eassumption. split; assumption.
  Qed.

  Lemma x2_l1_def : forall j m cw len s off Q x1 x5 x7 x8 x9 x13 x16 x17 x21 x22 x25 x27 x28 x29,
    len = 8 * Q -> 1 <= Q -> off = len * s -> Z.to_nat (cnt - s) = j -> 0 <= s < cnt -> pos + len * cnt <= 4096 ->
    mem_inv psegs m -> munch [(DT + 4, DT + 16388)] m0 m -> wmono psegs m0 m ->
    x2_cells m DT cw -> bytes_at psegs m SYM syb -> cells_written cw0 cw pos off (nb + 256) ->
    evt psegs (x2_l1_post gp tp x6 x15 x18 x19 x20 x23 x24 x30 x31 F fc SPF DT m0 cw0 pos (len * cnt) (nb + 256))
      (ST 0x1d88c m x1 x5 x7 x8 x9 (Z_to_bv 64 (SYM + bg + s)) (Z_to_bv 64 (nb * 65536 + 16777216)) (Z_to_bv 64 (DT + 4 + 4 * (pos + off))) x13
          (Z_to_bv 64 (4 * len)) x16 x17 x21 x22 x25 (Z_to_bv 64 (SYM + bg + cnt)) x27 x28 x29).
  Proof.
    induction j as [|j IH]; intros until x29; intros L8 Q1 EOFF EJ SR PH MI MU WM (CW & CWL) SYB CWR; [exfalso; lia|].
    assert (OFFR : 0 <= off /\ pos + off + len <= 4096).
    { assert (len * (s + 1) <= len * cnt) by (apply Z.mul_le_mono_nonneg_l; lia).
      split; [rewrite EOFF; apply Z.mul_nonneg_nonneg; lia | rewrite EOFF; lia]. }
    lbyte SYB. zstep. zstep. zstep. zstep. zstep.
    lazymatch goal with |- context [bv_unsigned (nth ?k syb ?d)] =>
      assert (SVR : 0 <= bv_unsigned (nth k syb d) < 65536) by (pose proof (bv_unsigned_in_range 8 (nth k syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth k syb d)) as sv eqn:ESV; clear ESV end.
    replace (nb * 65536 + 16777216) with ((nb + 256) * 65536) by lia.
    destruct (x2_X_val (nb + 256) sv ltac:(lia) SVR) as (EX & XH & XR). rewrite EX.
    remember ((nb + 256) * 65536 + sv) as X eqn:EXV.
    pose proof (x2_D_words X XR) as (DR & W1 & W3). cbv zeta in DR, W1, W3. rewrite XH in W1, W3.
    lazymatch goal with |- _ => let v := reg_val 17 in lazymatch v with Z_to_bv 64 ?e => remember e as D eqn:ED; clear ED end end.
    replace ((nb + 256) * 65536) with (nb * 65536 + 16777216) by lia.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + off) + 4 * len)) with (Z_to_bv 64 (DT + 4 + 4 * (pos + off + len))) by (f_equal; lia).
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + off))) with (Z_to_bv 64 (DT + 4 + 4 * (pos + off + 8 * 0))) by (f_equal; lia).
    eapply (x2_l1_def_in (Z.to_nat (Q - 0)) m cw len s off 0 Q D); try eassumption; try lia.
    3:{ replace (off + 8 * 0) with off by lia. exact CWR. }
    2:{ split; assumption. }
    (* [comment removed for export] *)
    clear W1 W3 DR. unfold KS1. intros m' cw' y1 y5 y7 y8 y9 y13 y16 y17 y21 y22 y25 y27 y28 y29 MI' MU' WM' CWS' SYB' CWR'.
    zstep. zstep. if_cases KB; zify_cond KB.
    - replace (Z_to_bv 64 (SYM + bg + s + 1)) with (Z_to_bv 64 (SYM + bg + (s + 1))) by (f_equal; lia).
      replace (Z_to_bv 64 (DT + 4 + 4 * (pos + off + len))) with (Z_to_bv 64 (DT + 4 + 4 * (pos + (off + len)))) by (f_equal; lia).
      eapply (IH m' cw' len (s + 1) (off + len) Q); try eassumption; try lia.
    - zstep. apply evt_done. unfold x2_l1_post. destruct CWS' as (CW' & CWL'). do 19 eexists. exists m', cw'.
      split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [split; assumption|].
      replace (len * cnt) with (off + len); [exact CWR'|]. rewrite EOFF. replace cnt with (s + 1) by lia. ring.
  Qed.
End L1.
