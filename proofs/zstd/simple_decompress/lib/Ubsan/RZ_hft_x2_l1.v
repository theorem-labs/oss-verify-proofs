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
From OssFuzzTheorems.Proofs.zstd.simple_decompress.lib.Ubsan Require huf42_3_kit_x2l1_len8 huf42_3_kit_x2l1_def.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

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

  (* [comment removed for export] *)
  Lemma x2_l1_len1 : forall j k m cw (A0 A1 A2 A7 HI T1 : Z) (x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word),
    lv = 1 ->
    KE1 (en - bg) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos k (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A7 = DT + 4 + 4 * (pos + k) ->
    HI = lv * 2^24 + nb * 2^16 -> T1 = nb + 256 * lv ->
    evt usegs Q (ST 0x2587c m x5 x6 x7 x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 HI) (Z_to_bv 64 5) (Z_to_bv 64 T1) (Z_to_bv 64 (-1)) (Z_to_bv 64 A7) x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction j as [|j IH]; intros k m cw A0 A1 A2 A7 HI T1 x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31
      LV1 KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EA7 EHI ET1; [exfalso; lia|].
    subst A0 A1 A2 A7 HI T1. unfold HUF_DTABLE_BYTES in *.
    zstep. zstep. fck.
    lbyte SYB.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + k)) + 0)) by (f_equal; lia).
    u16st CW (2 * (pos + k) + 1) (nb + 256 * lv); [reflexivity|].
    zstep.
    lazymatch goal with |- _ => let v := reg_val 5 in lazymatch v with Z_to_bv 64 ?e => remember e as sq eqn:ESQ; clear ESQ end end.
    u16st CW (2 * (pos + k)) sq; [reflexivity|].
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + k) 1 (nb + 256 * lv)) by (subst cw'; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos k 1 (nb + 256 * lv) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND.
    zstep. fck.
    zstep. zstep.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH (k + 1) _ cw'); try eassumption; try lia. split; assumption.
    - zstep. unfold KE1 in KE. eapply (KE _ cw'); try eassumption; [split; assumption|].
      replace (en - bg) with (k + 1) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len2 : forall j k m cw (A0 A1 A2 HI T1 : Z) (x8 x9 x18 x19 x20 x28 x29 x30 x31 : word),
    KE1 (2 * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + 2 * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (2 * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + 2 * k) -> A1 = SYM + bg + k -> A2 = SYM + en ->
    HI = lv * 2^24 + nb * 2^16 -> T1 = nb + 256 * lv ->
    evt usegs Q (ST 0x25658 m (Z_to_bv 64 HI) (Z_to_bv 64 T1) (Z_to_bv 64 (-9)) x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 1) (Z_to_bv 64 (-5)) (Z_to_bv 64 bs) (Z_to_bv 64 lv) (Z_to_bv 64 (-1)) x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction j as [|j IH]; intros k m cw A0 A1 A2 HI T1 x8 x9 x18 x19 x20 x28 x29 x30 x31
      KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EHI ET1; [exfalso; lia|].
    subst A0 A1 A2 HI T1. unfold HUF_DTABLE_BYTES in *.
    assert (LORB : forall a b, 0 <= a < 2^16 -> 0 <= b < 2^16 -> 0 <= Z.lor a b < 2^16).
    { intros a b Ha Hb. assert (M : Z.lor a b mod 2^16 = Z.lor a b).
      { rewrite <- Z.land_ones by lia. rewrite Z.land_lor_distr_l. rewrite !Z.land_ones by lia. rewrite !Z.mod_small by lia. reflexivity. }
      rewrite <- M. apply Z.mod_pos_bound. lia. }
    assert (HSQ : forall lo, 0 <= lo < 2^16 ->
      0 <= Z.lor lo ((nb + 256 * lv) * 2^16) < 2^32 /\ Z.lor lo ((nb + 256 * lv) * 2^16) ≫ 16 = nb + 256 * lv).
    { intros lo Hl. rewrite Z.lor_comm. rewrite lor_disj_add by lia. rewrite Z.shiftr_div_pow2 by lia.
      split; [lia|]. Z.div_mod_to_equations. lia. }
    lbyte SYB.
    lazymatch goal with |- context [bv_unsigned (nth ?i syb ?d)] =>
      assert (SVR : 0 <= bv_unsigned (nth i syb d) < 256) by (pose proof (bv_unsigned_in_range 8 (nth i syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth i syb d)) as sv eqn:ESV; clear ESV end.
    zstep. if_cases KL; zify_cond KL;
      [ assert (LOR : 0 <= sv < 2^16) by lia
      | zstep; zstep;
        rewrite ?(Z.mod_small (sv ≪ 8)) by (rewrite Z.shiftl_mul_pow2 by lia; lia);
        assert (LOR : 0 <= Z.lor (sv ≪ 8) bs < 2^16) by (apply LORB; [rewrite Z.shiftl_mul_pow2 by lia; lia | exact BSR]) ].
    all: lazymatch type of LOR with 0 <= ?e < _ => set (lo := e) in *; clearbody lo end.
    all: zstep.
    all: lazymatch goal with |- _ => let v := reg_val 28 in lazymatch v with Z_to_bv 64 (Z.lor ?l ?h) =>
      assert (SQ : 0 <= Z.lor l h < 2^32 /\ Z.lor l h ≫ 16 = nb + 256 * lv)
        by (replace h with ((nb + 256 * lv) * 2^16) by lia; apply HSQ; exact LOR);
      set (sq := Z.lor l h) in *; clearbody sq end end.
    all: destruct SQ as (SQR & SQH).
    all: replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 2 * k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 2 * k)) + 0)) by (f_equal; lia).
    all: remember (2 * (pos + 2 * k)) as b eqn:EB.
    all: u16st CW b sq; [reflexivity|].
    all: u16st CW (b + 1) (nb + 256 * lv); [reflexivity|].
    all: zstep; fck.
    all: zstep. all: rewrite SQH.
    all: u16st CW (b + 2) sq; [reflexivity|].
    all: u16st CW (b + 3) (nb + 256 * lv); [reflexivity|].
    all: zstep; fck.
    all: zstep; fck.
    all: zstep; zstep.
    all: lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    all: assert (RND : cells_written cw cw' (pos + 2 * k) 2 (nb + 256 * lv)) by (subst cw' b; cw_round).
    all: pose proof (cells_written_app cw0 cw cw' pos (2 * k) 2 (nb + 256 * lv) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    all: assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    all: clear ECW' RND.
    all: replace (2 * k + 2) with (2 * (k + 1)) in CWR' by lia.
    all: zstep; if_cases KB; zify_cond KB;
      [ eapply (IH (k + 1) _ cw'); try eassumption; try lia; split; assumption
      | zstep; unfold KE1 in KE; eapply (KE _ cw'); try eassumption; [split; assumption|];
        replace (2 * (en - bg)) with (2 * (k + 1)) by lia; exact CWR' ].
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len4 : forall j k m cw (A0 A1 A2 A3 HI : Z) (x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31 : word),
    lv = 1 ->
    KE1 (4 * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + 4 * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (4 * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + 4 * k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A3 = 0 ->
    HI = lv * 2^24 + nb * 2^16 ->
    evt usegs Q (ST 0x258d8 m x5 x6 x7 x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 A3) (Z_to_bv 64 (-9)) (Z_to_bv 64 (-1)) (Z_to_bv 64 HI) (Z_to_bv 64 (-17)) x18 x19 x20 x28 x29 x30 x31).
  Proof using All.
    induction j as [|j IH]; intros k m cw A0 A1 A2 A3 HI x5 x6 x7 x8 x9 x18 x19 x20 x28 x29 x30 x31
      LV1 KE EJ KR PH MI MU WM (CW & CWL) SYB CWR EA0 EA1 EA2 EA3 EHI; [exfalso; lia|].
    assert (EHI' : HI = (nb + 256) * 2^16) by lia. clear EHI.
    subst A0 A1 A2 A3 HI. unfold HUF_DTABLE_BYTES in *.
    zstep. fck.
    lbyte SYB. do 6 zstep.
    lazymatch goal with |- context [bv_unsigned (nth ?i syb ?d)] =>
      assert (SVR : 0 <= bv_unsigned (nth i syb d) < 256) by (pose proof (bv_unsigned_in_range 8 (nth i syb d)) as X; unfold bv_modulus in X; cbn in X; lia);
      remember (bv_unsigned (nth i syb d)) as sv eqn:ESV; clear ESV end.
    lazymatch goal with |- context [Z.lor ((?Y ≪ 32) mod _) ?Y] => remember Y as X eqn:EXV end.
    assert (XV : X = (nb + 256) * 65536 + sv).
    { rewrite EXV. change 65536 with (2^16). rewrite <- (lor_disj_add (nb + 256) sv 16) by lia.
      first [f_equal; lia | rewrite Z.lor_comm; f_equal; lia]. }
    clear EXV.
    assert (XR : 0 <= X < 4294967296) by lia.
    assert (XH : X / 65536 = nb + 256 * lv) by (rewrite XV, Z.div_add_l by lia; rewrite Z.div_small by lia; lia).
    pose proof (x2_D_words X XR) as (DR & W1 & W3). cbv zeta in DR, W1, W3. rewrite XH in W1, W3.
    replace (Z_to_bv 64 (DT + 4 + 4 * (pos + 4 * k))) with (Z_to_bv 64 (DT + 4 + 2 * (2 * (pos + 4 * k)) + 0)) by (f_equal; lia).
    remember (2 * (pos + 4 * k)) as b eqn:EB.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => u16st CW b e end end; [reflexivity|].
    u16st CW (b + 1) (nb + 256 * lv); [rewrite W1; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    lazymatch goal with |- _ => let v := reg_val 7 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 2) e end end; [reflexivity|].
    u16st CW (b + 3) (nb + 256 * lv); [rewrite W3; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    zstep. fck.
    lazymatch goal with |- _ => let v := reg_val 6 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 4) e end end; [reflexivity|].
    u16st CW (b + 5) (nb + 256 * lv); [rewrite W1; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    lazymatch goal with |- _ => let v := reg_val 7 in lazymatch v with Z_to_bv 64 ?e => u16st CW (b + 6) e end end; [reflexivity|].
    u16st CW (b + 7) (nb + 256 * lv); [rewrite W3; symmetry; apply Z.mod_small; change (2^16) with 65536; lia|].
    zstep. fck.
    zstep. fck.
    zstep. zstep.
    lazymatch type of CW with u8arr _ _ _ (u16s (map _ ?l)) => remember l as cw' eqn:ECW' end.
    assert (RND : cells_written cw cw' (pos + 4 * k) 4 (nb + 256 * lv)) by (subst cw' b; cw_round).
    pose proof (cells_written_app cw0 cw cw' pos (4 * k) 4 (nb + 256 * lv) POSR ltac:(lia) ltac:(lia) CWR RND) as CWR'.
    assert (CWL' : Z.of_nat (length cw') = 8192) by (subst cw'; rewrite !Zupd_length; exact CWL).
    clear ECW' RND W1 W3 DR.
    replace (4 * k + 4) with (4 * (k + 1)) in CWR' by lia.
    zstep. if_cases KB; zify_cond KB.
    - eapply (IH (k + 1) _ cw'); try eassumption; try lia. split; assumption.
    - zstep. unfold KE1 in KE. eapply (KE _ cw'); try eassumption; [split; assumption|].
      replace (4 * (en - bg)) with (4 * (k + 1)) by lia. exact CWR'.
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_len8 : forall j k m cw (A0 A1 A2 A3 HI : Z) (x8 x9 x18 x19 x20 x30 x31 : word),
    KE1 (8 * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + 8 * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (8 * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + 8 * k) -> A1 = SYM + bg + k -> A2 = SYM + en -> A3 = 0 ->
    HI = lv * 2^24 + nb * 2^16 ->
    evt usegs Q (ST 0x256d8 m (Z_to_bv 64 (-17)) (Z_to_bv 64 (-25)) (Z_to_bv 64 (-1)) x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 A3) (Z_to_bv 64 1) (Z_to_bv 64 bs) (Z_to_bv 64 lv) (Z_to_bv 64 (-9)) x18 x19 x20
                   (Z_to_bv 64 HI) (Z_to_bv 64 (-33)) x30 x31).
  Proof using All.
    exact (huf42_3_kit_x2l1_len8.x2_l1_len8_k ra gp tp s5 s6 s7 s8 s9 s10 s11 F fc SP DT SYM m0 cw0 syb pos bg en nb bs Q lv
             DTL DTH DTE SYL SYH SEP BGR ENR POSR NBR BSR LVR).
  Qed.

  (* [comment removed for export] *)
  Lemma x2_l1_def : forall j k m cw (L A0 A1 A2 HI T3 T4 : Z) (x8 x9 x18 x19 x20 x31 : word),
    16 <= L <= 4096 -> L mod 8 = 0 ->
    KE1 (L * (en - bg)) -> Z.to_nat (en - bg - k) = j -> 0 <= k < en - bg -> pos + L * (en - bg) <= 4096 ->
    mem_inv usegs m -> munch [(DT + 4, DT + HUF_DTABLE_BYTES)] m0 m -> wmono usegs m0 m ->
    x2_cells m DT cw -> bytes_at usegs m SYM syb -> cells_written cw0 cw pos (L * k) (nb + 256 * lv) ->
    A0 = DT + 4 + 4 * (pos + L * k) -> A1 = SYM + bg + k -> A2 = SYM + en ->
    HI = lv * 2^24 + nb * 2^16 -> T3 = 4 * L -> T4 = 4 * L ->
    evt usegs Q (ST 0x257a4 m (Z_to_bv 64 (-25)) (Z_to_bv 64 (-33)) (Z_to_bv 64 HI) x8 x9 (Z_to_bv 64 A0) (Z_to_bv 64 A1) (Z_to_bv 64 A2)
                   (Z_to_bv 64 1) (Z_to_bv 64 (-9)) (Z_to_bv 64 bs) (Z_to_bv 64 lv) (Z_to_bv 64 (-17)) x18 x19 x20
                   (Z_to_bv 64 T3) (Z_to_bv 64 T4) (Z_to_bv 64 (-1)) x31).
  Proof using All.
    exact (huf42_3_kit_x2l1_def.x2_l1_def_k ra gp tp s5 s6 s7 s8 s9 s10 s11 F fc SP DT SYM m0 cw0 syb pos bg en nb bs Q lv
             DTL DTH DTE SYL SYH SEP BGR ENR POSR NBR BSR LVR).
    (* [comment removed for export] *)
  Qed.

End L1.
