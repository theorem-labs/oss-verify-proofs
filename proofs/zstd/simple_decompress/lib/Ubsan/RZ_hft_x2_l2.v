(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Spec Require Import FseNCount FseLemmas ZdFrame ZdHufStats ZdHufX1 ZdHufX2.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac Arr Bytes ZBridge.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Common Require Import StrFun STRW_tac WStr FseWalkKit FseWalkMem FseRdKit MemRange ZdCellKit ZdWalkKit ZdSeqBuildW ZdHufW ZdHufWM ZdHufWR ZdHufWX ZdHufWY.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import UImg RZ_huf_iface RZ_hft_iface RZ_hft_bdt_defs RZ_hft_x2_defs.
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require Import frame_kit.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Lemma x2_l2_seq : forall sv bs nb, 0 <= sv < 256 -> 0 <= bs < 2^16 -> 0 <= nb <= 12 ->
  0 <= Z.lor (sv ≪ 8) (bs + nb * 65536 + 33554432) < 4294967296 /\ Z.lor (sv ≪ 8) (bs + nb * 65536 + 33554432) / 65536 = nb + 512.
Proof.
  intros sv bs nb Hs Hb Hn.
  replace (bs + nb * 65536 + 33554432) with ((nb + 512) * 2^16 + bs) by (change (2^16) with 65536; ring).
  rewrite <- (lor_disj_add (nb + 512) bs 16) by lia.
  rewrite Z.lor_assoc, (Z.lor_comm (sv ≪ 8) ((nb + 512) * 2^16)), <- Z.lor_assoc.
  assert (S8 : 0 <= sv ≪ 8 < 2^16) by (rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; change (2^16) with 65536; lia).
  assert (LB : 0 <= Z.lor (sv ≪ 8) bs < 2^16).
  { assert (M : Z.lor (sv ≪ 8) bs mod 2^16 = Z.lor (sv ≪ 8) bs).
    { rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
    rewrite <- M. apply Z.mod_pos_bound. lia. }
  rewrite lor_disj_add by lia.
  change (2^16) with 65536 in *.
  split; [lia|].
  rewrite Z.div_add_l by lia. rewrite Z.div_small by lia. lia.
Qed.

Section L2.
  Variables (ra gp tp s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (SP DT SYM : Z) (m0 : fmem) (cw0 : list Z)
            (syb : list byte) (pos bg en nb bs : Z) (Q : machine_state -> Prop).
  Hypothesis DTL : 4096 <= DT.  Hypothesis DTH : DT + HUF_DTABLE_BYTES < 2^47.  Hypothesis DTE : DT mod 2 = 0.
  Hypothesis SYL : 4096 <= SYM.  Hypothesis SYH : SYM + zlen syb < 2^47.
  Hypothesis SEP : DT + HUF_DTABLE_BYTES <= SYM \/ SYM + zlen syb <= DT.
  Hypothesis BGR : 0 <= bg <= en.  Hypothesis ENR : en <= zlen syb.  Hypothesis POSR : 0 <= pos.
  Hypothesis NBR : 0 <= nb <= 12.  Hypothesis BSR : 0 <= bs < 2^16.

  Notation ST pc mm x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31 :=
    (MS (mkR ra (Z_to_bv 64 (SP + -48)) gp tp x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 s5 s6 s7 s8 s9 s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 pc) fc None mm (seg_rom usegs)).

  Definition KE2 (n : Z) : Prop :=
    forall m' cw' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31,
      mem_inv usegs m' -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m' -> wmono usegs m0 m' ->
      x2_cells m' DT cw' -> cells_written cw0 cw' pos n (nb + 512) ->
      evt usegs Q (ST 0x259ec m' x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x28 x29 x30 x31).

  (* [comment removed for export] *)
  Lemma x2_l2_len1 : forall j k m cw (A0 A1 A2 A7 HB T1 : Z) (x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word),
    KE2 (en - bg) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos k (nb + 512) ->
    A0 = DT + 4 + 4 * (pos + k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A7 = DT + 4 + 4 * (pos + k) ->
    HB = bs + nb * 2^16 + 2^25 -> T1 = nb + 512 ->
    evt usegs Q (ST 0x25948 m x5 x6 x7 x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 HB) (Z_to_bv 64 4) (Z_to_bv 64 T1) (Z_to_bv 64 (-1)) (Z_to_bv 64 A7) x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction j as [|j IH]; intros k m cw A0 A1 A2 A7 HB T1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31
      KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EA7 EHB ET1; [exfalso; lia|].
    subst A0 A1 A2 A7 HB T1. unfold HUF_DTABLE_BYTES in *.
    zstep. zstep. fck.
    lbyte SYB.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + k)) + 0)) by (f_equal; lia).
    u16st CW (2 * (pos + k) + 1) (nb + 512); [reflexivity|].
    zstep. zstep.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => remember e as sq eqn:ESQ; clear ESQ end end.
    u16st CW (2 * (pos + k)) sq; [reflexivity|].
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + k) 1 (nb + 512)) by (subst cw'; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos k 1 (nb + 512) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. fck.
    zstep. zstep.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH (k + 1) _ cw'); try eassumption; try lia. split; assumption.
    - zstep. unfold KE2 in KE. eapply (KE _ cw'); try eassumption; [split; assumption|].
      replace (en - bg) with (k + 1) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l2_len4 : forall j k m cw (A0 A1 A2 A3 HB : Z) (x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word),
    KE2 (4 * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + 4 * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (4 * k) (nb + 512) ->
    A0 = DT + 4 + 4 * (pos + 4 * k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A3 = 0 ->
    HB = bs + nb * 2^16 + 2^25 ->
    evt usegs Q (ST 0x25990 m x5 x6 x7 x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 A3) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-1)) (Z_to_bv 64 HB) (Z_to_bv 64 (-17)) x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction j as [|j IH]; intros k m cw A0 A1 A2 A3 HB x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31
      KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EA3 EHB; [exfalso; lia|].
    subst A0 A1 A2 A3 HB. unfold HUF_DTABLE_BYTES in *.
    zstep. fck.
    lbyte SYB. do 7 zstep.
    lazymatch goal with |- context [bv_unsigned (nth ?i syb ?d)] =>
      assert (SVR : 0 <= bv_unsigned (nth i syb d) < 256) by (pose proof (bv_unsigned_in_range 8 (nth i syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth i syb d)) as sv eqn:ESV; clear ESV end.
    assert (SH8 : (sv ≪ 8) mod 18446744073709551616 = sv ≪ 8) by (apply Z.mod_small; rewrite Z.shiftl_mul_pow2 by lia; change (2^8) with 256; lia).
    rewrite SH8.
    destruct (x2_l2_seq sv bs nb SVR BSR NBR) as (XR & XH).
    remember (Z.lor (sv ≪ 8) (bs + nb * 65536 + 33554432)) as X eqn:EXV.
    pose proof (x2_D_words X XR) as (DR & W1 & W3). cbv zeta in DR, W1, W3. rewrite XH in W1, W3.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 4 * k)) + 0)) by (f_equal; lia).
    remember (2 * (pos + 4 * k)) as b eqn:EB.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => u16st CW b e end end; [reflexivity|].
    u16st CW (b + 1) (nb + 512); [rewrite W1; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    lazymatch goal with |- _ => let v := reg_val 7 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 2) e end end; [reflexivity|].
    u16st CW (b + 3) (nb + 512); [rewrite W3; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    zstep. fck.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 4) e end end; [reflexivity|].
    u16st CW (b + 5) (nb + 512); [rewrite W1; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    lazymatch goal with |- _ => let v := reg_val 7 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 6) e end end; [reflexivity|].
    u16st CW (b + 7) (nb + 512); [rewrite W3; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    zstep. fck.
    zstep. fck.
    zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 4 * k) 4 (nb + 512)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (4 * k) 4 (nb + 512) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND W1 W3 DR.
    replace (4 * k + 4) with (4 * (k + 1)) in CWR' by lia.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH (k + 1) _ cw'); try eassumption; try lia. split; assumption.
    - unfold KE2 in KE. eapply (KE _ cw'); try eassumption; [split; assumption|].
      replace (4 * (en - bg)) with (4 * (k + 1)) by lia. exact CWR'.
  Qed.
End L2.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
