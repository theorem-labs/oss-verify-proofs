(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.zstd.simple_decompress.lib.Lib Require Import Tac.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition zsep (x1 x2 y1 y2 : Z) : Prop := x2 <= y1 \/ y2 <= x1.
Definition zimp (P Q : Prop) : Prop := P -> Q.

Lemma disjoint_from_sub : forall W a n a' n', disjoint_from W a n -> a <= a' -> a' + n' <= a + n -> disjoint_from W a' n'.
Proof.
  induction W as [|[l hh] W IH]; cbn; intros a n a' n' D L1 L2; [exact I|].
  destruct D as [D1 D2]. split; [lia|]. eapply IH; eauto.
Qed.

Ltac dj_atom := first [ left; lia | right; lia | lia ].
Ltac dj_one :=
  first [ dj_atom
        | match goal with S : zsep _ _ _ _ |- _ =>
            let S' := fresh "S'" in pose proof S as S'; unfold zsep in S'; destruct S' as [S'|S']; dj_atom end ].
Ltac dj_solve := cbn [disjoint_from]; simpl_sizes; repeat split; first [ exact I | dj_one ].

(* [comment removed for export] *)
Ltac zd_bundle_transport segs m m' MU WM MI' := idtac.

Ltac zd_transport segs m m' MU WM :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport segs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_transport segs m m' A2 n2) in H; [ | exact WM ]
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport segs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk segs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_disjoint segs W m m' loq hiq) in H; [ | exact MU | exact WM | dj_solve ]
            | idtac "note: dropping stk (not provably disjoint from callee footprint):" H; clear H ]
  | H : wmono segs ?mq m |- _ => apply (wmono_trans segs mq m m') in H; [ | exact WM ]
  end.

Ltac post_callk segs m :=
  let ms' := fresh "ms'" in let PO := fresh "POST" in
  intros ms' PO;
  destruct_exs PO;
  let E := fresh "E" in let MUc := fresh "MUc" in let WMc := fresh "WMc" in let MIc := fresh "MI" in
  destruct PO as [E [MUc [WMc PO]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms';
  lazymatch type of MUc with
  | munch ?Wc m ?m' =>
      zd_bundle_transport segs m m' MUc WMc MIc;
      repeat match goal with
      | H : munch ?Wq ?mq m |- _ =>
          let SF := fresh "SF" in
          assert (SF : sub_fp Wc Wq) by (first [ eassumption | unfold sub_fp; cbn [outside]; intros; slia ]);
          apply (munch_trans Wq mq m m') in H; [ | eapply (munch_weaken Wc Wq m m'); [ exact SF | exact MUc ] ]; clear SF
      end;
      zd_transport segs m m' MUc WMc;
      clear MUc WMc;
      try match goal with H : mem_inv segs m |- _ => clear H end;
      try clear m
  end;
  try destruct_ands PO;
  try (lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end).
Tactic Notation "callk" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callk segs m ]
  end.

(* [comment removed for export] *)
Ltac zd_transport_chunks segs m a bs :=
  repeat match goal with
  | H : bytes_at segs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_write_other segs m a bs A2 bs2) in H; [ | lia | simpl_sizes; slia | simpl_sizes; dj_one ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_write segs m A2 n2 (wa a) bs) in H
  | H : rw_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; dj_one ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  | H : ro_cells segs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_frame segs m A2 cs2 a bs) in H; [ | lia | simpl_sizes; slia | simpl_sizes; dj_one ]
            | idtac "note: dropping hypothesis (not provably disjoint from store):" H; clear H ]
  end.
