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
From OSSVerify.Proofs.fast_float.from_chars.lib.AACB Require AcPriStep.
Import OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcAst OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPri OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcHA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk.AcPriSep OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriSepOk OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcConvA OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcNPop OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.AcNPopApp OSSVerify.Proofs.fast_float.from_chars.lib.AACB.AcPriStep.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Lemma mc_tbl_even : forall c, In c CLS -> 2 * (mc_tbl c / 2) = mc_tbl c.
Proof.
  intros c H. unfold CLS in H. cbn [In] in H.
  repeat (destruct H as [<-|H]; [vm_compute; reflexivity|]). destruct H.
Qed.

(* [comment removed for export] *)
Definition icc (CA i x : Z) : Prop := CA + 80 * i + 4 <= x < CA + 80 * i + 16.

(* [comment removed for export] *)
Lemma cls_inv_frame_ic : forall (m0 m0' : word -> option byte) CA SB SH c j z, In c CLS ->
  0 <= CA -> CA + 4096 <= 2^63 -> 0 <= SB -> SB + 137438953472 + 4096 <= 2^63 -> 0 <= SH -> SH + 17179869184 <= 2^63 -> 0 <= j ->
  (CA + 2592 <= SB \/ SB + 137438953472 + 4096 <= CA) -> (CA + 2592 <= SH \/ SH + 17179869184 <= CA) -> 0 <= z <= 262144 ->
  (forall x, cls_foot CA SB SH c z x -> ~ icc CA c x -> m0' (wa x) = m0 (wa x)) ->
  ((rd m0' (CA + 80 * c + 4) 4 (mc_tbl c) /\ rd m0' (CA + 80 * c + 8) 8 (sz_tbl c)) \/ (forall x, icc CA c x -> m0' (wa x) = m0 (wa x))) ->
  wr m0' (CA + 80 * c) 80 ->
  cls_inv m0 CA SB SH c j z -> cls_inv m0' CA SB SH c j z.
Proof.
  intros m0 m0' CA SB SH c j z Hc H1 H2 H3 H4 H5 H6 Hj0 Hs1 Hs2 Hz HF HIC HW Hcl. pose proof (in_cls_rng c Hc) as Hcr.
  destruct HIC as [[Rmc Rsz]|Hsame].
  2:{ apply (cls_inv_frame m0 m0' CA SB SH c j z Hc H1 H2 H3 H4 H5 H6 Hj0); [|exact Hcl].
      intros x Hx. destruct (Z_lt_le_dec x (CA + 80 * c + 4)) as [L1|L1]; [apply (HF x Hx); unfold icc; lia|].
      destruct (Z_lt_le_dec x (CA + 80 * c + 16)) as [L2|L2]; [apply Hsame; unfold icc; lia | apply (HF x Hx); unfold icc; lia]. }
  destruct (cls_tbl c Hc) as (Hsz & Hs8 & Hs8r & Hnw & Hnm & Hmc).
  destruct Hcl as [(J0 & Z0 & HV & HSW)|(J1 & Z1 & Jb & HI & HP)]; [left | right].
  - split; [exact J0|]. split; [exact Z0|]. split.
    + destruct HV as [A B C F G]. constructor.
      * apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact A].
      * right. split; [exact Rmc | exact Rsz].
      * intros i Hi. apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact (C i Hi)].
      * exact HW.
      * apply (wr_frame m0 m0'); [lia | lia | intros x Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact G].
    + destruct HSW as [W1 W2]. split.
      * apply (wr_frame m0); [lia | lia | | exact W1]. intros x Hx. apply HF; [unfold cls_foot; lia | unfold icc; lia].
      * apply (wr_frame m0); [lia | lia | | exact W2]. intros x Hx. apply HF; [unfold cls_foot; lia | unfold icc; lia].
  - split; [exact J1|]. split; [exact Z1|]. split; [exact Jb|]. split.
    + destruct HI as [A D E F G H I J K M N].
      pose proof (cnt_of_range (mc_tbl c / 2) j ltac:(lia) ltac:(lia)) as Hcnt. pose proof (b_of_pos (mc_tbl c / 2) j ltac:(lia) ltac:(lia)) as Hb.
      assert (Hnb : 0 <= 262144 / sz_tbl c - mc_tbl c / 2 * b_of (mc_tbl c / 2) j <= 262144 / sz_tbl c) by (pose proof (b_of_bounds (mc_tbl c / 2) j ltac:(lia) ltac:(lia)); nia).
      constructor; try assumption.
      * apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact D].
      * rewrite (mc_tbl_even c Hc). exact Rmc.
      * intros i Hi. apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact (G i Hi)].
      * apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact H].
      * apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact I].
      * destruct J as (na & Hna & Rna). exists na. split; [exact Hna|].
        apply (rd_frame m0 m0'); [lia | cbn; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact Rna].
      * intros k Hk. apply (rd_frame m0 m0'); [clear - H3 Hcr Hk; lia | cbn; clear - H4 Hcr Hk Hnb Hnw; lia | intros x Hx; cbn in Hx; apply HF; [unfold cls_foot; rewrite Z1; clear - Hx Hk Hnb Hnw; lia | unfold icc; clear - Hx Hk Hnb Hnw Hs1 Hcr; lia] | exact (K k Hk)].
      * apply (wr_frame m0 m0'); [lia | lia | intros x Hx; apply HF; [unfold cls_foot; lia | unfold icc; lia] | exact N].
    + apply (POP_C_frame m0); [| nia | exact HP].
      intros x Hx. unfold RBX, SHX in Hx. assert (0 <= sz_tbl c * j) by nia. assert (0 <= sz_tbl c / 8 * j) by nia.
      apply HF; [unfold cls_foot; rewrite Z1; lia | unfold icc; lia].
Qed.

(* [comment removed for export] *)
Lemma INV_Az_step2 : forall pz m0 m0' c, INV_Az pz m0 -> (z_tg pz + 4096 <= z_pg pz \/ z_pg pz + PG_SIZE <= z_tg pz) -> In c CLS ->
  z_j pz c + 1 + mc_tbl c / 2 <= 262144 / sz_tbl c ->
  INV_Co m0' (z_ca pz) (z_sb pz) c (sz_tbl c) (mc_tbl c / 2) (262144 / sz_tbl c) (z_j pz c + 1) ->
  POP_C m0' (z_sb pz) (z_sh pz) c (sz_tbl c) (z_j pz c + 1) -> STATS m0' (z_ca pz) ->
  wr m0' (z_ca pz - 128) 2720 ->
  (forall i, In i CLS -> i <> c ->
     (rd m0' (z_ca pz + 80 * i + 4) 4 (mc_tbl i) /\ rd m0' (z_ca pz + 80 * i + 8) 8 (sz_tbl i)) \/ (forall x, icc (z_ca pz) i x -> m0' (wa x) = m0 (wa x))) ->
  (forall x, pri_foot_z pz x -> ~ owned_C (z_ca pz) (z_sb pz) c x -> (forall i, 1 <= i <= 31 -> i <> c -> ~ icc (z_ca pz) i x) ->
     ~ (z_sh pz + 536870912 * c <= x < z_sh pz + 536870912 * c + 32768) ->
     ~ (z_sh pz + 536870912 * c + 469762048 <= x < z_sh pz + 536870912 * c + 469762048 + 32768) -> m0' (wa x) = m0 (wa x)) ->
  INV_Az (pz_step pz c) m0'.
Proof.
  intros pz m0 m0' c HI Hdisj Hc Hjb HIo HPo HSt HWC HIC HF. pose proof (az_geo pz m0 HI) as G. pose proof (in_cls_rng c Hc) as Hcr.
  pose proof HI as HI0. destruct HI0 as [Hlen Hsb Hsh Hca Hpg Htg Hnsh Hst Hwc Hq Hgq Hcls].
  destruct (cls_jb pz m0 HI c Hc) as (J0 & _).
  unfold PG_SIZE in Hpg, Hdisj.
  assert (T1 : z_ca pz + 2592 <= z_pg pz \/ z_pg pz + 137439023104 <= z_ca pz - 128) by (clear - Hdisj Htg; lia).
  assert (S1 : 2199291686912 + 2147450880 <= z_sh pz /\ z_sh pz + 17179869184 <= z_pg pz) by (clear - G; lia).
  assert (S2 : z_ca pz + 2592 <= z_sh pz \/ z_sh pz + 17179869184 <= z_ca pz - 128) by (clear - G S1 Htg; lia).
  assert (B0 : 4096 <= z_ca pz - 208 /\ z_ca pz + 3888 <= 2^47 /\ z_pg pz <= z_sb pz /\ z_sb pz + 137438953472 + 4096 <= z_pg pz + 137439023104 /\
               z_pg pz + 137439023104 <= 2^47 /\ 17594333495296 <= z_pg pz) by (clear - G; lia).
  assert (P0 : z_ca pz + 3888 <= 65536 \/ 6537424 <= z_ca pz) by (clear - Hca; lia).
  clear G Hsb Hsh Hca Hpg Htg Hnsh Hdisj.
  (* [comment removed for export] *)
  assert (Nic : forall x, ~ (z_ca pz - 128 <= x < z_ca pz + 2592) -> forall i, 1 <= i <= 31 -> i <> c -> ~ icc (z_ca pz) i x).
  { intros x Hx i Hir _ Hc0. unfold icc in Hc0. clear - Hx Hc0 Hir. lia. }
  (* [comment removed for export] *)
  assert (HQC : forall x, z_ca pz - 128 <= x < z_ca pz - 96 -> m0' (wa x) = m0 (wa x)).
  { intros x Hx. apply HF; [left; clear - Hx; lia | unfold owned_C; clear - Hx Hcr T1 B0; lia | | clear - Hx S2 Hcr; lia | clear - Hx S2 Hcr; lia].
    intros i Hir _ Hc0. unfold icc in Hc0. clear - Hx Hc0 Hir. lia. }
  constructor; rewrite ?(step_sb pz c Hlen Hcr), ?(step_sh pz c Hlen Hcr), ?(step_ca pz c Hlen Hcr), ?(step_pg pz c Hlen Hcr), ?(step_tg pz c Hlen Hcr),
    ?(step_qj pz c Hlen Hcr), ?(step_qn pz c Hlen Hcr), ?(step_qb pz c Hlen Hcr), ?(step_gn pz c Hlen Hcr), ?(step_gl pz c Hlen Hcr), ?(step_gb pz c Hlen Hcr); try assumption.
  - exact (step_len pz c Hlen).
  - exact (iz_sb _ _ HI).
  - exact (iz_sh _ _ HI).
  - exact (iz_ca _ _ HI).
  - exact (iz_pg _ _ HI).
  - exact (iz_tg _ _ HI).
  - exact (iz_nsh _ _ HI).
  - (* [comment removed for export] *)
    destruct Hq as [(Hqb & Rqb & Hq) Hqj]. split.
    + split; [exact Hqb|]. split.
      { apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact Rqb]. }
      destruct Hq as [(Q0 & Qb0 & R0)|(Q1 & Q2 & R1 & R1b & R2 & R3 & R4 & W1)]; [left | right].
      * split; [exact Q0|]. split; [exact Qb0|]. apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R0].
      * assert (Z24 : z_z pz 24 = 262144).
        { destruct (Hcls 24 in_cls_24) as [(J24 & _)|(_ & Z1 & _)]; [specialize (Hqj ltac:(clear - Q1; lia)); clear - Hqj J24 Q2; lia | exact Z1]. }
        assert (HB : forall x, z_sb pz + 103079215104 + 8192 * z_qj pz <= x < z_sb pz + 103079215104 + 8192 * z_qj pz + 8192 -> m0' (wa x) = m0 (wa x)).
        { intros x Hx. apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Q2; lia | unfold owned_C; clear - Hx Q2 T1 B0 Hcr; lia
                                 | apply Nic; clear - Hx Q2 T1 B0; lia | clear - Hx Q2 S1 B0 Hcr; lia | clear - Hx Q2 S1 B0 Hcr; lia]. }
        split; [exact Q1|]. split; [exact Q2|]. split; [|split; [|split; [|split; [|split]]]].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R1].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R1b].
        -- apply (rd_frame m0); [clear - B0; lia | cbn; clear - B0; lia | intros x Hx; cbn in Hx; apply HQC; clear - Hx; lia | exact R2].
        -- apply (rd_frame m0); [clear - B0 Q2; lia | cbn; clear - B0 Q2; lia | intros x Hx; cbn in Hx; apply HB; clear - Hx; lia | exact R3].
        -- apply (rd_frame m0); [clear - B0 Q2; lia | cbn; clear - B0 Q2; lia | intros x Hx; cbn in Hx; apply HB; clear - Hx; lia | exact R4].
        -- apply (wr_frame m0); [clear - B0 Q2; lia | clear - B0 Q2; lia | intros x Hx; apply HB; clear - Hx; lia | exact W1].
    + intros Hqn. specialize (Hqj Hqn). destruct (Z.eq_dec c 24) as [->|Hne].
      * rewrite (step_j_same pz 24 Hlen ltac:(lia)). clear - Hqj. lia.
      * rewrite (step_j_other pz c Hlen Hcr 24 ltac:(lia) ltac:(congruence)). exact Hqj.
  - (* [comment removed for export] *)
    destruct Hgq as [Hg Hgl]. split.
    + apply (gq_inv_o_frame m0 m0' (z_sb pz) (z_gn pz) (z_gl pz) (z_gb pz) ltac:(clear - B0; lia) ltac:(clear - B0; lia)); [|exact Hg].
      intros x [Hx|(Hg1 & Hx)].
      * apply HF; [right; right; left; exact Hx | unfold owned_C; clear - Hx P0 B0 Hcr; lia | apply Nic; clear - Hx P0 B0; lia | clear - Hx S1 Hcr; lia | clear - Hx S1 Hcr; lia].
      * assert (Z24 : z_z pz 24 = 262144).
        { destruct (Hcls 24 in_cls_24) as [(J24 & _)|(_ & Z1 & _)]; [specialize (Hgl Hg1); destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | clear - Hgl J24 G1; lia] | exact Z1]. }
        assert (Gl : 0 <= z_gl pz < 32) by (destruct Hg as (_ & _ & _ & _ & _ & _ & _ & _ & [(G0 & _)|(_ & G1 & _)]); [clear - G0 Hg1; lia | exact G1]).
        apply HF; [right; right; right; exists 24; split; [exact in_cls_24|]; left; rewrite Z24; clear - Hx Gl; lia | unfold owned_C; clear - Hx Gl T1 B0 Hcr; lia
                 | apply Nic; clear - Hx Gl T1 B0; lia | clear - Hx Gl S1 B0 Hcr; lia | clear - Hx Gl S1 B0 Hcr; lia].
    + intros Hgn. specialize (Hgl Hgn). destruct (Z.eq_dec c 24) as [->|Hne].
      * rewrite (step_j_same pz 24 Hlen ltac:(lia)). clear - Hgl. lia.
      * rewrite (step_j_other pz c Hlen Hcr 24 ltac:(lia) ltac:(congruence)). exact Hgl.
  - (* [comment removed for export] *)
    intros c' Hc'. pose proof (in_cls_rng c' Hc') as Hcr'. destruct (Z.eq_dec c' c) as [->|Hne].
    + rewrite (step_j_same pz c Hlen Hcr), (step_z_same pz c Hlen Hcr). right.
      split; [clear - J0; lia|]. split; [reflexivity|]. split; [clear - Hjb; lia|]. split; [exact HIo | exact HPo].
    + rewrite (step_j_other pz c Hlen Hcr c' Hcr' Hne), (step_z_other pz c Hlen Hcr c' Hcr' Hne).
      destruct (cls_jb pz m0 HI c' Hc') as (K0 & _ & _ & Kz).
      assert (Kz0 : 0 <= z_z pz c' <= 262144) by (clear - Kz; lia).
      apply (cls_inv_frame_ic m0 m0' _ _ _ c' _ _ Hc'); [clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - B0; lia | clear - S1; lia | clear - S1 B0; lia | exact K0
        | clear - T1 B0; lia | clear - S2; lia | exact Kz0 | | exact (HIC c' Hc' Hne) | | exact (Hcls c' Hc')].
      * intros x Hx Hnic. unfold cls_foot in Hx.
        assert (D : c' <= c - 1 \/ c + 1 <= c') by (clear - Hne; lia).
        assert (Kz' : 0 <= z_z pz c' <= 262144) by (clear - Kz; lia).
        assert (Nic' : z_ca pz - 128 <= x < z_ca pz + 2592 -> z_ca pz + 80 * c' <= x < z_ca pz + 80 * c' + 80 -> forall i, 1 <= i <= 31 -> i <> c -> ~ icc (z_ca pz) i x).
        { intros _ Hxr i Hir _ Hc0. destruct (Z.eq_dec i c') as [->|Hn']; [exact (Hnic Hc0)|]. unfold icc in Hc0. clear - Hxr Hc0 Hn' Hir Hcr'. lia. }
        destruct Hx as [Hx|[Hx|[Hx|[Hx|[Hx|Hx]]]]].
        -- apply HF; [left; clear - Hx Hcr'; lia | unfold owned_C; clear - Hx D T1 B0 Hcr Hcr'; lia | apply Nic'; [clear - Hx Hcr'; lia | exact Hx] | clear - Hx S2 Hcr Hcr'; lia | clear - Hx S2 Hcr Hcr'; lia].
        -- apply HF; [right; left; clear - Hx Hcr'; lia | unfold owned_C; clear - Hx D T1 B0 Hcr Hcr'; lia | apply Nic; clear - Hx T1 B0 Hcr'; lia | clear - Hx S1 B0 Hcr Hcr'; lia | clear - Hx S1 B0 Hcr Hcr'; lia].
        -- apply HF; [right; right; right; exists c'; split; [exact Hc'|]; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr Hcr'; lia | apply Nic; clear - Hx Kz' T1 B0 Hcr'; lia
                   | clear - Hx Kz' S1 B0 Hcr Hcr'; lia | clear - Hx Kz' S1 B0 Hcr Hcr'; lia].
        -- apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; left; exact Hx | unfold owned_C; clear - Hx Kz' T1 B0 Hcr Hcr'; lia | apply Nic; clear - Hx Kz' T1 B0 Hcr'; lia
                   | clear - Hx Kz' S1 B0 Hcr Hcr'; lia | clear - Hx Kz' S1 B0 Hcr Hcr'; lia].
        -- apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; right; left; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr Hcr'; lia | apply Nic; clear - Hx S2 Hcr'; lia
                   | clear - Hx D Hcr Hcr'; lia | clear - Hx D Hcr Hcr'; lia].
        -- apply HF; [right; right; right; exists c'; split; [exact Hc'|]; right; right; right; exact Hx | unfold owned_C; clear - Hx S1 S2 B0 Hcr Hcr'; lia | apply Nic; clear - Hx S2 Hcr'; lia
                   | clear - Hx D Hcr Hcr'; lia | clear - Hx D Hcr Hcr'; lia].
      * apply wr_bytes; [clear - B0 Hcr'; lia | clear - B0 Hcr'; lia|]. intros x Hx.
        exact (wr_byte m0' (z_ca pz - 128) 2720 x ltac:(clear - B0; lia) ltac:(clear - B0; lia) HWC ltac:(clear - Hx Hcr'; lia)).
Qed.
(* [comment removed for export] *)
