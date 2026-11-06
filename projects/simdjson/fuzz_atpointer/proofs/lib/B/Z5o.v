(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.AS Require Import Zp7 Z1b.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS Z10q FP Z119.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Spec Require Import Prelim StrFun Z3o.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.Sj Require Import SjTape Zpk.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.P Require Import Z10v Zpp Zvw.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.A Require Import Shadow.
From OSSVerify.Proofs.simdjson.fuzz_atpointer.lib.B Require Import Layout Zks Zkt D_defs D_kit D_clx Z87 Sj_rtf Zpm Zpl Zq2
     Z45 Z5k Z5q Z60 Z63 Z65.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Record objI : Type := mkOI {
  oi_q : Z; oi_dd : Z; oi_out : Z; oi_node : Z; oi_P : Z; oi_f : Z; oi_ptr : list Z; oi_i : Z; oi_e : Z; oi_c : Z;
  oi_ra : word; oi_gp : word; oi_s0 : word; oi_s1 : word; oi_s2 : word; oi_s3 : word; oi_s4 : word; oi_s5 : word; oi_s6 : word; oi_s7 : word;
  oi_s8 : word; oi_s9 : word; oi_s10 : word; oi_s11 : word; oi_m0 : mem; oi_jH : list byte }.
Definition oi_b (I : objI) : Z := oi_q I + -256 - oi_dd I.
Definition oi_L (I : objI) : Z := zlength (oi_ptr I).

Definition obj_hdrB : list cell := [C8 (Z_to_bv 64 0x41b58ab3); C8 (Z_to_bv 64 0x131f8); C8 (Z_to_bv 64 0x99a84)].

Section ObjCtxDefs.
Variable RT : rt_sig.
Variable E : aenvA.
Variable d : nat.
Variables (Σ Σ1 : rts RT) (I : objI).

Record octx : Prop := mkOC {
  oc_dd : oi_dd I = 0 \/ oi_dd I = 16;
  oc_b32 : oi_b I mod 32 = 0;
  oc_q16 : oi_q I mod 16 = 0;
  oc_lor : ae_lo E + obj_needA d <= oi_q I;
  oc_qhi : oi_q I <= ae_hi E;
  oc_node : oi_q I <= oi_node I /\ oi_node I + 16 <= ae_hi E /\ oi_node I mod 8 = 0;
  oc_out : oi_q I <= oi_out I /\ oi_out I + 24 <= ae_hi E /\ oi_out I mod 8 = 0;
  oc_no : oi_node I + 16 <= oi_out I \/ oi_out I + 24 <= oi_node I;
  oc_lv : a_live RT Σ E;
  oc_pat : ptr_atA E (oi_P I) (oi_ptr I);
  oc_ty : ty (ae_T E) (oi_i I) = t_obj;
  oc_nxt : tnext (ae_T E (oi_i I)) = oi_e I + 1;
  oc_end : ae_T E (oi_e I) = tword t_obj_end (oi_i I);
  oc_tiles : tiles (field (ae_T E) (ae_S E) (ae_sn E) (elem (ae_T E) (ae_S E) (ae_sn E) ck_any d)) (oi_i I + 1) (oi_e I) (oi_c I);
  oc_i0 : 0 <= oi_i I;
  oc_en : oi_e I + 1 <= ae_n E - 1;
  oc_frames1 : rt_frames RT Σ1 = (oi_f I, 1%nat) :: rt_frames RT Σ;
  oc_live1 : rt_live RT Σ1 = rt_live RT Σ;
  oc_sp01 : rt_sp0 RT Σ1 = rt_sp0 RT Σ;
  oc_credit1 : rt_credit RT Σ1 = rt_credit RT Σ - 1;
  oc_frb : (length (rt_frames RT Σ) + S d <= FRAMES_MAX2)%nat;
  oc_crb : obj_costA d (oi_L I) <= rt_credit RT Σ;
  oc_lvb : Z.of_nat (length (rt_live RT Σ)) + 1 <= LIVE_MAX /\ lposA (rt_live RT Σ);
  oc_f0 : 0 < oi_f I;
  oc_f64 : oi_f I mod 64 = 0;
  oc_ftop : oi_f I + 128 < USTACK_TOP;
  oc_flo : 0x676000 <= oi_f I;
  oc_fhi : oi_f I + 120 <= ae_lo E;
  oc_fsh : oi_f I + 128 <= shad (oi_f I) \/ shad (oi_f I) + 16 <= oi_f I;
  oc_s0 : 0 <= shad (oi_f I);
  oc_shi : shad (oi_f I) + 16 <= ae_lo E }.

Definition obaseK (Σc : rts RT) (m : mem) : Prop :=
  mem_inv bsegs m /\ ART RT Σc m /\ AINV_A E m
  /\ rw_cells bsegs m (oi_q I + -104) (obj_saved (oi_ra I) (oi_s0 I) (oi_s1 I) (oi_s2 I) (oi_s3 I) (oi_s4 I) (oi_s5 I) (oi_s6 I) (oi_s7 I) (oi_s8 I) (oi_s9 I) (oi_s10 I) (oi_s11 I))
  /\ rw_cells bsegs m (oi_b I + 152) [CB (Z.to_nat (oi_dd I)) (oi_jH I)]
  /\ rw_cells bsegs m (oi_f I) obj_hdrB
  /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) [(oi_out I, oi_out I + 24)] (oi_m0 I) m.

Definition obase (Σc : rts RT) (m : mem) : Prop := obaseK Σc m /\ stk bsegs m (ae_lo E) (oi_b I).

Definition Kpost (PMc : Model -> Prop) : config -> Prop :=
  fun cf => lvl_postA RT E Σ PMc (oi_ra I) (oi_q I) (oi_gp I) (oi_s0 I) (oi_s1 I) (oi_s2 I) (oi_s3 I) (oi_s4 I) (oi_s5 I) (oi_s6 I) (oi_s7 I) (oi_s8 I) (oi_s9 I) (oi_s10 I) (oi_s11 I)
              (oi_out I) (oi_m0 I) (obj_costA d (oi_L I)) cf /\ cfrm0 cf.
End ObjCtxDefs.

Lemma obase_K : forall RT E Σ I Σc m, obase RT E Σ I Σc m -> obaseK RT E Σ I Σc m.
Proof. intros RT E Σ I Σc m [H _]. exact H. Qed.
Lemma obase_stk : forall RT E Σ I Σc m, obase RT E Σ I Σc m -> stk bsegs m (ae_lo E) (oi_b I).
Proof. intros RT E Σ I Σc m [_ H]. exact H. Qed.
Lemma obase_of_K : forall RT E Σ I Σc m, obaseK RT E Σ I Σc m -> stk bsegs m (ae_lo E) (oi_b I) -> obase RT E Σ I Σc m.
Proof. intros RT E Σ I Σc m H1 H2. exact (conj H1 H2). Qed.

Ltac lia_prep :=
  repeat match goal with
  | H : forall x : ?T, _ |- _ => lazymatch type of T with Prop => fail | _ => clear H end
  | H : atp_elem_cpsA _ _ _ |- _ => clear H
  | H : atp_obj_cpsA _ _ _ |- _ => clear H
  | H : atp_arr_cpsA _ _ _ |- _ => clear H
  | H : rt_contracts2 _ |- _ => clear H
  | H : rt_contracts _ |- _ => clear H
  | H : art_facts _ |- _ => clear H
  | H : rw_cells _ _ _ _ |- _ => clear H
  | H : ro_cells _ _ _ _ |- _ => clear H
  | H : bytes_at _ _ _ _ |- _ => clear H
  | H : munch _ _ _ |- _ => clear H
  | H : wmono _ _ _ |- _ => clear H
  | H : mem_inv _ _ |- _ => clear H
  | H : ART _ _ _ |- _ => clear H
  | H : AINV_A _ _ |- _ => clear H
  | H : octx _ _ _ _ _ _ |- _ => clear H
  | H : obase _ _ _ _ _ _ |- _ => clear H
  | H : obaseK _ _ _ _ _ _ |- _ => clear H
  | H : tiles _ _ _ _ |- _ => clear H
  | H : elem _ _ _ _ _ _ _ |- _ => clear H
  | H : ptr_atA _ _ _ |- _ => clear H
  | H : a_live _ _ _ |- _ => clear H
  | H : agree_on _ _ _ |- _ => clear H
  | H : shz _ _ _ |- _ => clear H
  | H : Forall _ _ |- _ => clear H
  | H : aenvA_ok _ |- _ => clear H
  | H : frm0 _ |- _ => clear H
  | H : In _ _ |- _ => clear H
  | H : _ \/ _ |- _ => clear H
  | H : _ mod _ = _ |- _ => clear H
  end.
Ltac flia := lia_prep; lia.

Ltac xport_core H AG tac :=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of AG with agree_on _ _ ?m' =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m')
        by (eapply agree_sub; [exact AG|]; intros ? Hx; cbn [cells_size csize Nat.add length obj_hdrB obj_saved atkey_frame atkey_saved app] in Hx; cbv beta; tac Hx);
      apply (fun X => rw_cells_agree_nw bsegs m m' A cs X Q) in H; clear Q
    end end.

Tactic Notation "xport_stack" hyp(H) constr(AG) :=
  xport_core H AG ltac:(fun Hx => split; [left; unfold USTACK_TOP in *; flia| flia]).
Tactic Notation "xport_stack" hyp(H) constr(AG) "sz" constr(SZ) :=
  xport_core H AG ltac:(fun Hx => rewrite SZ in Hx; split; [left; unfold USTACK_TOP in *; flia| flia]).
Tactic Notation "xport_frame" hyp(H) constr(AG) constr(HinF) :=
  xport_core H AG ltac:(fun Hx => split; [right; right; right; left; eexists _, 1%nat; split; [exact HinF| rewrite fs1; flia]| flia]).
Tactic Notation "xport_shadow" hyp(H) constr(AG) constr(HinF) :=
  xport_core H AG ltac:(fun Hx => split; [right; right; right; right; eexists _, 1%nat; split; [exact HinF| rewrite fs1s; flia]| flia]).
Tactic Notation "xport_live" hyp(H) constr(AG) constr(Hin) :=
  xport_core H AG ltac:(fun Hx => split; [right; right; left; eexists _, _; split; [exact Hin| flia]| flia]).

Ltac mport H MU WM :=
  lazymatch type of H with rw_cells bsegs ?m ?A ?cs =>
    lazymatch type of MU with munch ?W m ?m' =>
      let H2 := fresh "MP" in
      pose proof (rw_cells_transport bsegs W m m' A cs H MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_hdrB obj_saved atkey_frame atkey_saved app fst snd]; unfold shad, SHB, atkey_W in *; flia)) as H2;
      clear H; rename H2 into H
    end end.

Section ObjB.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; flia.

  Lemma obj_room : ae_lo E + RT_STACK + 432 <= oi_q I /\ oi_q I + -272 <= oi_b I /\ oi_b I <= oi_q I + -256.
  Proof using CTX OK.
    destruct CTX as [Hdd _ _ LOR _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _]. unfold oi_b.
    assert (0 <= elem_needA d) by (unfold elem_needA, ATP_LEAFB, RT_STACK; lia).
    unfold obj_needA in LOR. split; [ul|]. clear - Hdd; lia.
  Qed.

  Lemma obj_cok : forall (Σc : rts RT) (m : mem) (sp : Z),
    rt_sp0 RT Σc = rt_sp0 RT Σ -> stk bsegs m (ae_lo E) sp -> oi_q I + -432 <= sp <= oi_b I -> sp mod 16 = 0 -> call_ok RT Σc m (wz sp) (ae_lo E).
  Proof using CTX OK.
    intros Σc m sp ES ST SPR S16. pose proof obj_room as (R1 & R2 & R3).
    destruct CTX as [Hdd B32 Q16 LOR QHI (QN & NB & N8) _ _ LV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof LV as (_ & _ & _ & _ & LWIN). pose proof (ok_lo E OK) as LOW. pose proof (ok_hi E OK) as [HL HT].
    unfold call_ok. rewrite unsigned_lit by ul. rewrite ES. split; [exact ST|]. split; [exact LWIN|]. split; [ul|]. split; [ul|].
    clear - S16. Z.div_mod_to_equations. lia.
  Qed.

  Lemma obj_pres_down : forall (Σc : rts RT) (sp dst n : Z) (m m' : mem),
    rt_pres_ex (rt_live RT Σc) (rt_frames RT Σc) sp dst n m m' -> rt_live RT Σc = rt_live RT Σ -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ ->
    sp <= oi_q I -> rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) dst n m m'.
  Proof using CTX.
    intros Σc sp dst n m m' PR EL EF SP a Ha Hd.
    apply PR; [| exact Hd]. rewrite EL, EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| exact SP].
  Qed.

  Lemma obj_split : forall (Σc : rts RT) (m : mem) (a : Z),
    ART RT Σc m -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> oi_q I <= a \/ a < ae_lo E.
  Proof using AF CTX.
    intros Σc m a ART0 EF EL ES Ha. pose proof CTX as CTX'. destruct CTX' as [_ _ _ _ _ _ _ _ LV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    assert (Hac : aclient (rt_live RT Σc) (rt_frames RT Σc) (oi_q I) a).
    { rewrite EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL| intros x Hx; right; exact Hx| lia]. }
    destruct (aclient_split_c RT AF Σc m (oi_q I) a ART0 Hac); [left; lia| right]. rewrite ES in *. lia.
  Qed.

  Lemma obj_mono : forall (Σc : rts RT) (sp a : Z),
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> (forall x, In x (rt_live RT Σ) -> In x (rt_live RT Σc)) -> sp <= oi_q I ->
    aclient (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) a -> aclient (rt_live RT Σc) (rt_frames RT Σc) sp a.
  Proof.
    intros Σc sp a EF EL SP Ha. rewrite EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [exact EL| intros x Hx; right; exact Hx| exact SP].
  Qed.
End ObjB.
