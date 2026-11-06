(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.fast_float.from_chars.images Require Import AsanUbsan.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec StoreOk FxLin FxCore FxSound FxMem FxSubst FxEnt.
From OSSVerify.Proofs.fast_float.from_chars.lib.MAX Require Import AxMng.
From OSSVerify.Proofs.fast_float.from_chars.lib.FXC Require Import FxBacking FxChDen FxChLib FxChSep FxWvC.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAXB Require Import AXG_put AXG_np AXG_nf1 AXG_npf.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcAst AcPri AcHA.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriSepOk AcConvA AcNPop.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep AcPriStep2 NqStepZ.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep2 OSSVerify.Proofs.fast_float.from_chars.lib.AACB.NqStepZ.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma INV_Az_qnew2 : forall pz m0 m0' sz, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) ->
  z_qn pz = 0 -> z_j pz 24 = 0 ->
  q_inv m0' (z_ca pz - 128) (z_sb pz) (z_j pz 24) 1 (sz + 8192) ->
  INV_Co m0' (z_ca pz) (z_sb pz) 24 (sz_tbl 24) (mc_tbl 24 / 2) (262144 / sz_tbl 24) (z_j pz 24 + 1) ->
  POP_C m0' (z_sb pz) (z_sh pz) 24 (sz_tbl 24) (z_j pz 24 + 1) -> STATS m0' (z_ca pz) ->
  wr m0' (z_ca pz - 128) 2720 ->
  (forall i, In i CLS -> i <> 24 ->
     (rd m0' (z_ca pz + 80 * i + 4) 4 (mc_tbl i) /\ rd m0' (z_ca pz + 80 * i + 8) 8 (sz_tbl i)) \/ (forall x, icc (z_ca pz) i x -> m0' (wa x) = m0 (wa x))) ->
  (forall x, pri_foot_z pz x -> ~ owned_C (z_ca pz) (z_sb pz) 24 x -> (forall i, 1 <= i <= 31 -> i <> 24 -> ~ icc (z_ca pz) i x) ->
     ~ (z_sh pz + 536870912 * 24 <= x < z_sh pz + 536870912 * 24 + 32768) ->
     ~ (z_sh pz + 536870912 * 24 + 469762048 <= x < z_sh pz + 536870912 * 24 + 469762048 + 32768) ->
     ~ (z_ca pz - 128 <= x < z_ca pz - 96) -> m0' (wa x) = m0 (wa x)) ->
  INV_Az (qz_new pz sz) m0'.
Proof.
  intros pz m0 m0' sz HI Hdisj Hqn0 Hj0 HQ HIo HPo HSt HWC HIC HF. destruct (q_seps pz m0 HI Hdisj) as (T1 & S1 & S2 & B0).
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  assert (P0 : z_ca pz + 3888 <= 65536 \/ 6537424 <= z_ca pz) by (clear - Hca; lia).
  assert (Nic : forall x, ~ (z_ca pz - 128 <= x < z_ca pz + 2592) -> forall i, 1 <= i <= 31 -> i <> 24 -> ~ icc (z_ca pz) i x).
  { intros x Hx i Hir _ Hc0. unfold icc in Hc0. clear - Hx Hc0 Hir. lia. }
  constructor; rewrite ?(qnew_sb pz sz Hlen), ?(qnew_sh pz sz Hlen), ?(qnew_ca pz sz Hlen), ?(qnew_pg pz sz Hlen), ?(qnew_tg pz sz Hlen),
    ?(qnew_qj pz sz Hlen), ?(qnew_qn pz sz Hlen), ?(qnew_qb pz sz Hlen), ?(qnew_gn pz sz Hlen), ?(qnew_gl pz sz Hlen), ?(qnew_gb pz sz Hlen); try assumption.
  - exact (qnew_len pz sz Hlen).
  - (* [comment removed for export] *)
    split; [exact HQ|]. intros _. rewrite (qnew_j24 pz sz Hlen). clear. lia.
  - (* [comment removed for export] *)
    destruct Hgq as [Hg Hgl]. split; [|intros Hgn; rewrite (qnew_j24 pz sz Hlen); specialize (Hgl Hgn); clear - Hgl; lia].
    apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(clear - B0; lia) ltac:(clear - B0; lia)); [|exact Hg].
    intros x [Hx|(Hg1 & Hx)].
    + apply HF; [right; right; left; exact Hx | unfold owned_C; clear - Hx P0 B0; lia | apply Nic; clear - Hx P0 B0; lia | clear - Hx S1; lia | clear - Hx S1; lia | clear - Hx P0; lia].
    + exfalso. assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]).
      specialize (Hgl Hg1). clear - Hgl Gl Hj0. lia.
  - (* [comment removed for export] *)
    intros c Hc. pose proof (in_cls_rng c Hc) as Hcr.
    destruct (Z.eq_dec c 24) as [->|Hne].
    + rewrite (qnew_j24 pz sz Hlen), (qnew_z24 pz sz Hlen). right.
      split; [clear - Hj0; lia|]. split; [reflexivity|]. split; [rewrite Hj0; vm_compute; discriminate|]. split; [exact HIo | exact HPo].
    + rewrite (qnew_j_other pz sz Hlen c Hcr Hne), (qnew_z_other pz sz Hlen c Hcr Hne).
      destruct (cls_jb pz m0 HI c Hc) as (K0 & _ & _ & Kz).
      assert (Kz0 : 0 <= z_z pz c <= 262144) by (clear - Kz; lia).
      apply (cls_inv_frame_ic m0 m0' _ _ _ c _ _ Hc); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0
        | clear - T1 B0; lia | clear - S2; lia | exact Kz0 | | exact (HIC c Hc Hne) | | exact (Hcls c Hc)].
      * intros x Hx Hnic. unfold cls_foot in Hx.
        assert (D : c <= 23 \/ 25 <= c) by (clear - Hne; lia).
        assert (Nic' : z_ca pz + 80 * c <= x < z_ca pz + 80 * c + 80 -> forall i, 1 <= i <= 31 -> i <> 24 -> ~ icc (z_ca pz) i x).
        { intros Hxr i Hir _ Hc0. destruct (Z.eq_dec i c) as [->|Hn']; [exact (Hnic Hc0)|]. unfold icc in Hc0. clear - Hxr Hc0 Hn' Hir Hcr. lia. }
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
        -- apply HF; [left; clear - Hx Hcr; lia | unfold owned_C; clear - Hx D T1 B0 Hcr; lia | exact (Nic' Hx) | clear - Hx S2 Hcr; lia | clear - Hx S2 Hcr; lia | clear - Hx Hcr; lia].
        -- apply HF; [right; left; clear - Hx Hcr; lia | unfold owned_C; clear - Hx D T1 B0 Hcr; lia | apply Nic; clear - Hx T1 B0 Hcr; lia | clear - Hx S1 B0 Hcr; lia | clear - Hx S1 B0 Hcr; lia
                   | clear - Hx T1 B0 Hcr; lia].
        -- apply HF; [right; right; right; exists c; split; [exact Hc|]; left; exact Hx | unfold owned_C; clear - Hx Kz0 T1 B0 Hcr; lia | apply Nic; clear - Hx Kz0 T1 B0 Hcr; lia
                   | clear - Hx Kz0 S1 B0 Hcr; lia | clear - Hx Kz0 S1 B0 Hcr; lia | clear - Hx Kz0 T1 B0 Hcr; lia].
        -- apply HF; [right; right; right; exists c; split; [exact Hc|]; right; left; exact Hx | unfold owned_C; clear - Hx Kz0 T1 B0 Hcr; lia | apply Nic; clear - Hx Kz0 T1 B0 Hcr; lia
                   | clear - Hx Kz0 S1 B0 Hcr; lia | clear - Hx Kz0 S1 B0 Hcr; lia | clear - Hx Kz0 T1 B0 Hcr; lia].
        -- apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; left; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr; lia | apply Nic; clear - Hx S2 Hcr; lia
                   | clear - Hx D Hcr; lia | clear - Hx D Hcr; lia | clear - Hx S2 Hcr; lia].
        -- apply HF; [right; right; right; exists c; split; [exact Hc|]; right; right; right; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr; lia | apply Nic; clear - Hx S2 Hcr; lia
                   | clear - Hx D Hcr; lia | clear - Hx D Hcr; lia | clear - Hx S2 Hcr; lia].
      * apply wr_bytes; [clear - B0 Hcr; lia | clear - B0 Hcr; lia|]. intros x Hx.
        exact (wr_byte m0' (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) HWC ltac:(clear - Hx Hcr; lia)).
Qed.
(* [comment removed for export] *)
