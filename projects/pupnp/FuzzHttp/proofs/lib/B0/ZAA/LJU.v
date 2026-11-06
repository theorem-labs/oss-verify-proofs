(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Arr Bytes ZBridge Frame Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Http Require Import HttpRep HttpTac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAW Require Import Segs Shadow Contracts ATac.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.B0.ZAA Require Import LJ.
Import ListNotations.
Open Scope Z_scope.

Lemma wmono_but_weaken : forall U W m m', sub_fp U W -> wmono_but U m m' -> wmono_but W m m'.
Proof. intros U W m m' S B x O Hx. exact (B x (S _ O) Hx). Qed.

Lemma wmono_but_refl : forall U m, wmono_but U m m.
Proof. intros U m x _ Hx. exact Hx. Qed.

Lemma wmono_but_wmono_l : forall U m1 m2 m3, wmono asegs m1 m2 -> wmono_but U m2 m3 -> wmono_but U m1 m3.
Proof. intros U m1 m2 m3 A B x O Hx. exact (B x O (A x Hx)). Qed.

Lemma wmono_but_wmono_r : forall U m1 m2 m3, wmono_but U m1 m2 -> wmono asegs m2 m3 -> wmono_but U m1 m3.
Proof. intros U m1 m2 m3 A B x O Hx. exact (B x (A x O Hx)). Qed.

Lemma wmono_but_join : forall U1 U2 m1 m2 m3, wmono_but U1 m1 m2 -> wmono_but U2 m2 m3 -> wmono_but (U1 ++ U2) m1 m3.
Proof. intros U1 U2 m1 m2 m3 A B x O Hx. apply outside_app in O as [O1 O2]. exact (B x O2 (A x O1 Hx)). Qed.

Section But.
Variables (W : list (Z * Z)) (m m' : word -> option byte).
Hypothesis MU : munch W m m'.
Hypothesis WB : wmono_but W m m'.

#[using="WB"] Lemma wr_at_transport_but : forall A n, wr_at asegs m A n -> disjoint_from W A n -> wr_at asegs m' A n.
Proof.
  intros A n (Ha & Hn & Hw) D. split; [exact Ha|]. split; [exact Hn|]. intros i Hi.
  apply WB; [| apply Hw; exact Hi]. eapply disjoint_outside; [exact D|]. rewrite wa_unsigned by lia. lia.
Qed.

#[using="MU WB"] Lemma rw_cells_transport_but : forall A cs,
  rw_cells asegs m A cs -> disjoint_from W A (Z.of_nat (cells_size cs)) -> rw_cells asegs m' A cs.
Proof.
  intros A cs [[Hwf Hb] Hw] D. split; [split; [exact Hwf|]|].
  - eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite cells_bytes_length by assumption. exact D.
  - apply wr_at_transport_but; assumption.
Qed.

#[using="MU WB"] Lemma u8arr_transport_but : forall A bs, u8arr asegs m A bs -> disjoint_from W A (Z.of_nat (length bs)) -> u8arr asegs m' A bs.
Proof. intros A bs [Hb Hw] D. split; [eapply bytes_at_transport; eauto| apply wr_at_transport_but; assumption]. Qed.

#[using="MU WB"] Lemma u32arr_transport_but : forall A ws, u32arr asegs m A ws -> disjoint_from W A (4 * Z.of_nat (length ws)) -> u32arr asegs m' A ws.
Proof.
  intros A ws [Hb Hw] D. split; [| apply wr_at_transport_but; assumption].
  eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u32s_length, Nat2Z.inj_mul. exact D.
Qed.

#[using="MU WB"] Lemma u64arr_transport_but : forall A ws, u64arr asegs m A ws -> disjoint_from W A (8 * Z.of_nat (length ws)) -> u64arr asegs m' A ws.
Proof.
  intros A ws [Hb Hw] D. split; [| apply wr_at_transport_but; assumption].
  eapply bytes_at_transport; [exact Hb| exact MU|]. rewrite u64s_length, Nat2Z.inj_mul. exact D.
Qed.

#[using="MU WB"] Lemma stk_transport_but : forall lo hi, stk asegs m lo hi -> disjoint_from W lo (hi - lo) -> stk asegs m' lo hi.
Proof.
  intros lo hi (H1 & H2 & Hs) D. split; [exact H1|]. split; [exact H2|]. intros a Ha.
  assert (O : outside W (bv_unsigned (wa a))) by (rewrite wa_unsigned by lia; eapply disjoint_outside; [exact D| lia]).
  destruct (Hs a Ha) as [Hw (b & Hb)]. split; [exact (WB _ O Hw)|].
  exists b. unfold mrd in *. rewrite (MU _ O). exact Hb.
Qed.
End But.

Ltac transport_after_call_but m m' MU WB :=
  let W := lazymatch type of MU with munch ?W _ _ => W end in
  repeat match goal with
  | H : bytes_at asegs m ?A2 ?bs2 |- _ =>
      first [ apply (bytes_at_transport asegs W m m' A2 bs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : wr_at asegs m ?A2 ?n2 |- _ =>
      first [ apply (wr_at_transport_but W m m' WB A2 n2) in H; [ | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : rw_cells asegs m ?A2 ?cs2 |- _ =>
      first [ apply (rw_cells_transport_but W m m' MU WB A2 cs2) in H; [ | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : ro_cells asegs m ?A2 ?cs2 |- _ =>
      first [ apply (ro_cells_transport asegs W m m' A2 cs2) in H; [ | exact MU | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u8arr asegs m ?A2 ?xs |- _ =>
      first [ apply (u8arr_transport_but W m m' MU WB A2 xs) in H; [ | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u32arr asegs m ?A2 ?xs |- _ =>
      first [ apply (u32arr_transport_but W m m' MU WB A2 xs) in H; [ | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : u64arr asegs m ?A2 ?xs |- _ =>
      first [ apply (u64arr_transport_but W m m' MU WB A2 xs) in H; [ | dj_solve ]
            | idtac "note: dropping hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : stk asegs m ?loq ?hiq |- _ =>
      first [ apply (stk_transport_but W m m' MU WB loq hiq) in H; [ | dj_solve ]
            | idtac "note: dropping stk hypothesis (not provably disjoint from callee footprint):" H; clear H ]
  | H : munch ?Wq ?mq m |- _ =>
      first [ apply (munch_trans Wq mq m m') in H; [ | refine (munch_weaken W Wq m m' _ MU); sub_fp_solve ]
            | fail 100 "callee footprint not inside the declared footprint" ]
  | H : wmono asegs ?mq m |- _ => apply (fun Hw => wmono_but_wmono_l W mq m m' Hw WB) in H
  | H : wmono_but ?Uq ?mq m |- _ =>
      first [ apply (fun Hw => wmono_but_trans Uq mq m m' Hw (wmono_but_weaken W Uq m m' ltac:(sub_fp_solve) WB)) in H
            | fail 100 "callee footprint not inside the declared wmono_but exception list" ]
  end.

Lemma dj_of_Forall : forall W a n,
  Forall (fun iv : Z * Z => a + n <= fst iv \/ snd iv <= a) W -> disjoint_from W a n.
Proof.
  induction W as [|[lo hi] W IH]; intros a n F; cbn; [exact I|].
  inversion F; subst. cbn in *. split; [lia| apply IH; assumption].
Qed.

Ltac frame_cell_but C MU WB F :=
  eapply rw_cells_transport_but; [exact MU| exact WB| exact C|
    apply dj_of_Forall; eapply Forall_impl; [| exact F]; intros [lo' hi'] Hiv'; cbn in Hiv' |- *; lia].

Lemma outside_or_above : forall W x, Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0xaa000 <= fst iv) W ->
  outside W x \/ x < 0x10000 \/ 0xaa000 <= x.
Proof.
  induction W as [|[lo' hi'] W IH]; intros x Fa; cbn; [left; exact I|].
  apply Forall_cons_iff in Fa as [Fa1 Fa2]; cbn in Fa1. destruct (IH x Fa2) as [O|A]; [| right; exact A].
  destruct (Z_lt_le_dec x lo'); [left; split; [lia| exact O]|].
  destruct (Z_lt_le_dec x hi'); [right; lia| left; split; [lia| exact O]].
Qed.
Lemma mem_inv_munch_above : forall W (m0 m' : word -> option byte),
  mem_inv asegs m0 -> munch W m0 m' -> Forall (fun iv : Z * Z => snd iv <= 0x10000 \/ 0xaa000 <= fst iv) W -> mem_inv asegs m'.
Proof.
  intros W m0 m' MI0 MU0 Fa xa b Hb.
  destruct (outside_or_above W (bv_unsigned xa) Fa) as [O|A].
  - rewrite (MU0 xa O) in Hb. exact (MI0 xa b Hb).
  - apply a0_ro_addr_false. lia.
Qed.

Ltac lia1u :=
  first [ assumption
        | match goal with h : ~ (Z.le _ _ /\ Z.lt _ _) |- _ =>
            solve [ repeat match goal with h' : ~ (Z.le _ _ /\ Z.lt _ _) |- _ => lazymatch h' with h => fail | _ => clear h' end end; lia ] end
        | lia ].
Ltac sub_fp_solve1 :=
  unfold sub_fp; cbn [outside List.app]; let xo := fresh "xo" in let Ho := fresh "Ho" in intros xo Ho; destruct_ands Ho;
  repeat split; lia1u.

Ltac hideU h := lazymatch type of h with id _ => idtac | ?P => change (id P) in h end.
Ltac unhideU h := lazymatch type of h with id ?P => change P in h | _ => idtac end.

Ltac post_callA_but segs m :=
  let a := fresh "r" in let H' := fresh "H'" in let ms' := fresh "ms'" in let PO := fresh "POST" in let MC := fresh "MC" in
  intros a H' ms' [PO MC];
  destruct_exs PO;
  let E := fresh "E" in let EH := fresh "EH" in let MUc := fresh "MUc" in let WBc := fresh "WBc" in let MIc := fresh "MI" in
  destruct PO as [E [EH [MUc [WBc PO]]]];
  first [ destruct PO as [MIc PO] | rename PO into MIc ];
  subst ms'; subst H'; clean_ms_mem MC;
  try destruct_ands PO;
  lazymatch type of MUc with
  | munch ?W m ?m' =>
      let WBw := fresh "WBw" in
      assert (WBw : wmono_but W m m') by (eapply wmono_but_weaken; [| exact WBc]; sub_fp_solve);
      absorb_footprint MUc m;

      repeat match goal with
             | Hq : wmono asegs ?mq m |- _ => apply (fun Hw => wmono_but_wmono_l _ mq m m' Hw WBc) in Hq
             | Hq : wmono_but ?Uq ?mq m |- _ => apply (fun Hw => wmono_but_join Uq _ mq m m' Hw WBc) in Hq; cbn [List.app] in Hq
             end;
      transport_after_call_but m m' MUc WBw;
      clear MUc WBc WBw;
      try match goal with Hh : mem_inv segs m |- _ => clear Hh end;
      try clear m
  end;
  lz_cont MC;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?n)) _ _ _ _) =>
           replace (ret_pc (Z_to_bv 64 n)) with (Z_to_bv 64 n) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
       end).

Tactic Notation "callAb" uconstr(SPEC) :=
  lz_here;
  lazymatch goal with
  | |- ITreeLZ.implL ?segs _ _ _ _ _ (MS _ _ _ _ _ ?m _) =>
      let C := find_mclean m in
      eapply implA_ebind; [ eapply implA_mclean; [ exact C | eapply SPEC ] | clear C; post_callA_but segs m ]
  end.
