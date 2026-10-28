(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import ShapeAlg AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes ImageA RzCPS StoreFast FP SysStep.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Spec Require Import Prelim StrFun AtpModel.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjTape SjTapeList.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.P Require Import Str_tac Sj_h_arith Sj_stage1_kit Rnd Sj_num_kit Sj_num_walk.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout Shadow RT_iface.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import IcptSpec D_defs D_kit D_clx D_rlkit Sj_rtf Sj_akit Sj_acps Sj_hkit Sj_hkit2 Sj_num_akit Sj_num_amem Sj_num_aframe I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import Atp_defsA Atp_kitA Atp_objdA Atp_objpA Atp_objkA Z6j Atp_objxA.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Notation wz z := (Z_to_bv 64 z) (only parsing).

Section ObjCW.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.

  Lemma obj_w664 : forall (K : machine_state -> Prop) (q b out : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= out < 2^64 ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 out) w120 w128) ->
    K (MS (mkR (wz 0xb67fc) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz out) (wz (b + 160)) (wz 24) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom asegs)) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb67ec) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH OUTR LOCA HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold e_asan_memcpy in *.
    unfold obj_locA in LOCA.

    astep. astep. step. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_w628 : forall (K : machine_state -> Prop) (q b P L0 sl : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x22 x24 x25 x26 x28 x29 x30 x31 : word) (w24 w32 w40 w48 w56 w64 w72 w88 w96 w104 w112 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (j0 : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E -> 0 <= L0 < 2^47 -> 0 < P -> P + 1 + L0 < 2^47 ->
    (sl = 18446744073709551615 \/ 0 <= sl < L0) ->
    rw_cells asegs m b (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 (Z_to_bv 64 sl) w88 w96 w104 w112 w120 w128) ->
    (sl = 18446744073709551615 ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz 18446744073709551615) (wz sl) x12 x13 x14 x15 x16 x17
                  x18 x19 x20 (wz (P + 1)) x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb67ec) fc None m (seg_rom asegs))) ->
    (0 <= sl < L0 ->
       K (MS (mkR (wz 0xb67d4) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 136)) (wz (b + 160)) (wz (P + 1 + sl)) (wz (L0 - sl)) x14 x15 x16 x17
                  x18 x19 x20 (wz (P + 1)) x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz ATP_ELEM_A) fc None m (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 (wz (P + 1)) x22 (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb67b0) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until j0. intros MI LO B0 B1 QH L0R P0 PH SL LOCA KOUT KCH.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT. unfold ATP_ELEM_A in *.
    unfold obj_locA in LOCA.

    astep. step. step. if_cases K0; zify_cond K0.
    - eapply evt_eq; [| apply evt_done; apply KOUT; rewrite ?land64_mod in K0; lia]. atp_st_eq.
    - assert (SLR : 0 <= sl < L0) by (rewrite ?land64_mod in K0; lia).

      step. if_dead1 by SLR L0R. astep. astep. astep. astep. step.
      eapply evt_eq; [| apply evt_done; apply (KCH SLR)]. atp_st_eq.
  Qed.

  Lemma obj_w64c : forall (K : machine_state -> Prop) (q b : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem),
    q + -304 <= b -> b <= q + -288 -> 304 <= q -> q < 2^47 ->
    K (MS (mkR (wz 0xb67e4) (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (wz (b + 160)) (wz (b + 136)) (wz 16) x13 x14 x15 x16 x17
               x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
         F (wz e_asan_memcpy) fc None m (seg_rom asegs)) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb67d4) fc None m (seg_rom asegs)).
  Proof.
    intros until m. intros B0 B1 QL QH HK. unfold e_asan_memcpy in *.
    astep. astep. astep. step.
    eapply evt_eq; [| apply evt_done; apply HK]. atp_st_eq.
  Qed.

  Lemma obj_w65c : forall (K : machine_state -> Prop) (q b : Z)
      (gp x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (m : mem) (jo16 je4 jo4 rb je jt : list byte),
    mem_inv asegs m -> ae_lo E + 304 <= q -> q + -304 <= b -> b <= q + -288 -> q <= ae_hi E ->
    rw_cells asegs m (b + 136) [CB 16 jo16; CB 4 je4; CB 4 jo4] ->
    rw_cells asegs m (b + 160) [CB 16 rb; CB 4 je; CB 4 jt] ->
    (forall (m1 : mem), munch [(b + 160, b + 184)] m m1 -> wmono asegs m m1 -> mem_inv asegs m1 ->
       rw_cells asegs m1 (b + 160) [CB 16 rb; C4 (sext 64 (bv_extract 0 32 (le_bytes_to_word je4))); CB 4 jt] ->
       K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) (sext 64 (bv_extract 0 32 (le_bytes_to_word je4))) x11 x12 x13 x14 x15 x16 x17
                  x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
             F (wz 0xb67ec) fc None m1 (seg_rom asegs))) ->
    evt asegs K (MS (mkR x1 (wz b) gp (wz TPV) x5 x6 x7 (wz q) (wz b) x10 x11 x12 x13 x14 x15 x16 x17
                       x18 x19 x20 x21 x22 x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
                   F (wz 0xb67e4) fc None m (seg_rom asegs)).
  Proof using OK.
    intros until jt. intros MI LO B0 B1 QH COUT REC HK.
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]]. unfold USTACK_TOP in HT.
    pose proof (munch_refl [(b + 160, b + 184)] m) as MU. pose proof (wmono_refl asegs m) as WM.

    step. step. name_mem m1.
    eapply evt_eq; [| apply evt_done; apply (HK m1); [exact MU| exact WM| assumption| ]].
    - atp_st_eq_goal.
    - lazymatch goal with H : rw_cells asegs m1 (b + 160) _ |- _ => exact H end.
  Qed.
End ObjCW.

Record objI : Type := mkOI {
  oi_q : Z; oi_dd : Z; oi_out : Z; oi_node : Z; oi_P : Z; oi_f : Z; oi_ptr : list Z; oi_i : Z; oi_e : Z; oi_c : Z;
  oi_ra : word; oi_gp : word; oi_s0 : word; oi_s1 : word; oi_s2 : word; oi_s3 : word; oi_s4 : word; oi_s5 : word; oi_s6 : word; oi_s7 : word;
  oi_s8 : word; oi_s9 : word; oi_s10 : word; oi_s11 : word; oi_m0 : mem; oi_jH : list byte }.
Definition oi_b (I : objI) : Z := oi_q I + -288 - oi_dd I.
Definition oi_L (I : objI) : Z := zlength (oi_ptr I).

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
  oc_flo : 0x6ca000 <= oi_f I;
  oc_fhi : oi_f I + 120 <= ae_lo E;
  oc_fsh : oi_f I + 128 <= shad (oi_f I) \/ shad (oi_f I) + 16 <= oi_f I;
  oc_s0 : 0 <= shad (oi_f I);
  oc_shi : shad (oi_f I) + 16 <= ae_lo E }.

Definition obase (Σc : rts RT) (m : mem) : Prop :=
  mem_inv asegs m /\ ART RT Σc m /\ stk asegs m (ae_lo E) (oi_b I) /\ AINV_A E m
  /\ rw_cells asegs m (oi_q I + -104) (obj_saved (oi_ra I) (oi_s0 I) (oi_s1 I) (oi_s2 I) (oi_s3 I) (oi_s4 I) (oi_s5 I) (oi_s6 I) (oi_s7 I) (oi_s8 I) (oi_s9 I) (oi_s10 I) (oi_s11 I))
  /\ rw_cells asegs m (oi_b I + 184) [CB (Z.to_nat (oi_dd I)) (oi_jH I)]
  /\ rw_cells asegs m (oi_f I) obj_hdr
  /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) [(oi_out I, oi_out I + 24)] (oi_m0 I) m.

Definition Kpost (PMc : Model -> Prop) : config -> Prop :=
  fun cf => lvl_postA RT E Σ PMc (oi_ra I) (oi_q I) (oi_gp I) (oi_s0 I) (oi_s1 I) (oi_s2 I) (oi_s3 I) (oi_s4 I) (oi_s5 I) (oi_s6 I) (oi_s7 I) (oi_s8 I) (oi_s9 I) (oi_s10 I) (oi_s11 I)
              (oi_out I) (oi_m0 I) (obj_costA d (oi_L I)) cf /\ cfrm0 cf.
End ObjCtxDefs.

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
  lazymatch type of H with rw_cells asegs ?m ?A ?cs =>
    lazymatch type of AG with agree_on _ _ ?m' =>
      let Q := fresh "AGQ" in
      assert (Q : agree_on (fun x => A <= x < A + Z.of_nat (cells_size cs)) m m')
        by (eapply agree_sub; [exact AG|]; intros ? Hx; cbn [cells_size csize Nat.add length obj_locA obj_sh pz obj_hdr obj_hdrR obj_shF obj_saved] in Hx; cbv beta; tac Hx);
      apply (fun X => rw_cells_agree_nw asegs m m' A cs X Q) in H; clear Q
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
  lazymatch type of H with rw_cells asegs ?m ?A ?cs =>
    lazymatch type of MU with munch ?W m ?m' =>
      let H2 := fresh "MP" in
      pose proof (rw_cells_transport asegs W m m' A cs H MU WM
                    ltac:(cbn [disjoint_from cells_size csize Nat.add length obj_locA obj_sh pz obj_hdr obj_hdrR obj_shF obj_saved fst snd]; unfold shad, SHB in *; flia)) as H2;
      clear H; rename H2 into H
    end end.

Section ObjC.
  Variable RT : rt_sig.
  Hypothesis AF : art_facts RT.
  Hypothesis RC2 : rt_contracts2 RT.
  Variable E : aenvA.
  Hypothesis OK : aenvA_ok E.
  Variable d : nat.
  Hypothesis HELEM : atp_elem_cpsA RT E d.
  Variable PMc : Model -> Prop.
  Hypothesis FDO : fdfs_only PMc.
  Hypothesis MST : mat_stable PMc.
  Variables (Σ Σ1 : rts RT) (I : objI).
  Hypothesis CTX : octx RT E d Σ Σ1 I.

  Local Ltac ul := unfold obj_needA, arr_needA, elem_needA, ATP_LEAFB, SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *; flia.

  Local Ltac oname :=
    unfold oi_b, oi_L in *;
    set (q := oi_q I) in *; set (dd := oi_dd I) in *; set (out := oi_out I) in *; set (node := oi_node I) in *; set (P := oi_P I) in *;
    set (f := oi_f I) in *; set (ptr := oi_ptr I) in *; set (i := oi_i I) in *; set (e := oi_e I) in *; set (c := oi_c I) in *;
    set (ra := oi_ra I) in *; set (gp := oi_gp I) in *; set (s0 := oi_s0 I) in *; set (s1 := oi_s1 I) in *; set (s2 := oi_s2 I) in *;
    set (s3 := oi_s3 I) in *; set (s4 := oi_s4 I) in *; set (s5 := oi_s5 I) in *; set (s6 := oi_s6 I) in *; set (s7 := oi_s7 I) in *;
    set (s8 := oi_s8 I) in *; set (s9 := oi_s9 I) in *; set (s10 := oi_s10 I) in *; set (s11 := oi_s11 I) in *; set (m0 := oi_m0 I) in *;
    set (jH := oi_jH I) in *; set (b := q + -288 - dd) in *.

  Local Ltac olia := repeat match goal with x := _ |- _ => cbv delta [x] in *; clear x end; unfold oi_b, oi_L in *; flia.

  Lemma obj_fin : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 : Z) (js4 jo : list byte) (cL cC cR : list cell),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
    rw_cells asegs m (oi_b I) cL -> cells_size cL = 136%nat -> rw_cells asegs m (oi_b I + 136) cC -> cells_size cC = 24%nat ->
    rw_cells asegs m (oi_b I + 160) cR -> cells_size cR = 24%nat ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) x20 x21 (wz (oi_f I)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb67fc) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK.
    intros until cR. intros OB FRM EF EL ES CR LOC SZL COUT SZC REC SZR SH OUT.
    destruct CTX as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_rel1 E OK _ q b f v4 v5 v6 gp x1); [exact MI| exact F64| exact FLO| exact FHI| clear - FSH; lia| exact S0| flia| exact HDR| exact SH|].
    intros m1 MU1 WM1 MI1 HDR1 SH1.
    assert (FP1 : fp_ok RT Σc (ae_lo E) [(f, f + 8); (shad f, shad f + 16)]).
    { constructor; [| constructor; [| constructor]]; cbn [fst snd].
      - right; right; left. exists f, 1%nat. split; [exact HinF| rewrite fs1; flia].
      - right; right; right. exists f, 1%nat. split; [exact HinF|]. rewrite fs1s. flia. }
    pose proof (art_of_munch RT AF Σc m m1 (ae_lo E) _ ART0 ltac:(rewrite ES; exact LWIN) FP1 MU1 WM1) as ART1.

    pose proof (rw_cells_transport asegs _ m m1 _ _ SAVED MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as SAVED1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ HIGH MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as HIGH1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ LOC MU1 WM1 ltac:(cbn; rewrite SZL; unfold shad, SHB in *; flia)) as LOC1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ COUT MU1 WM1 ltac:(cbn; rewrite SZC; unfold shad, SHB in *; flia)) as COUT1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ REC MU1 WM1 ltac:(cbn; rewrite SZR; unfold shad, SHB in *; flia)) as REC1.
    pose proof (rw_cells_transport asegs _ m m1 _ _ OUT MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as OUT1.
    pose proof (stk_transport_disjoint asegs _ m m1 (ae_lo E) b ST MU1 WM1 ltac:(cbn; unfold shad, SHB in *; flia)) as ST1.

    assert (NEWF : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> ~ (f <= a < f + fs_size 1) /\ ~ (shad f <= a < shad (f + fs_size 1))).
    { intros a Ha. exact (newframe_apart RT AF Σ Σc m f 1%nat q a ART0 EF EL ES ltac:(flia) Ha). }
    rewrite fs1s, fs1 in NEWF.
    assert (AG1 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m m1).
    { apply (agree_of_munch _ _ _ _ MU1). intros x Hx. destruct (NEWF x Hx) as [N1 N2]. unfold shad in *. cbn [outside]. flia. }

    destruct (af_frame_release RT AF Σc m1 f 1%nat (rt_frames RT Σ) ART1 EF) as (Σ2 & fl & FLAG & NAC & FL0 & FL1 & LAST & REL).
    rewrite fs1 in LAST. replace (f + 128 - 8) with (f + 120) in LAST by flia. rewrite ES in FL1.
    assert (FLQ : fl < ae_lo E) by ul.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_rel2 _ q b f fl gp x1); [exact MI1| exact FLO| ul| exact FL0| ul| exact LAST| exact FLAG|].
    intros m2 MU2 WM2 MI2 FLAG2.
    destruct (REL m2 MU2 WM2 FLAG2) as (ART2 & EF2 & EL2 & ES2 & EC2 & EA2 & EM2).
    apply (aevt_switch RT PMc Σc Σ2 _ _ EA2 EM2).

    assert (NFL : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> a <> fl).
    { intros a Ha ->. apply NAC. rewrite EL, EF. destruct Ha as [Ha|[Ha|[Ha|[Ha|Ha]]]].
      - exfalso. ul.
      - right; left. exact Ha.
      - right; right; left. exact Ha.
      - right; right; right; left. destruct Ha as (f1 & k1 & Hin & Hr). exists f1, k1. split; [right; exact Hin| exact Hr].
      - right; right; right; right. destruct Ha as (f1 & k1 & Hin & Hr). exists f1, k1. split; [right; exact Hin| exact Hr]. }
    assert (AG2 : agree_on (fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) q a) m1 m2).
    { apply (agree_of_munch _ _ _ _ MU2). intros x Hx. pose proof (NFL x Hx). cbn [outside]. flia. }
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ SAVED1 MU2 WM2 ltac:(cbn; flia)) as SAVED2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ HIGH1 MU2 WM2 ltac:(cbn; flia)) as HIGH2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ LOC1 MU2 WM2 ltac:(cbn; rewrite SZL; flia)) as LOC2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ COUT1 MU2 WM2 ltac:(cbn; rewrite SZC; flia)) as COUT2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ REC1 MU2 WM2 ltac:(cbn; rewrite SZR; flia)) as REC2.
    pose proof (rw_cells_transport asegs _ m1 m2 _ _ OUT1 MU2 WM2 ltac:(cbn; flia)) as OUT2.
    pose proof (stk_transport_disjoint asegs _ m1 m2 (ae_lo E) b ST1 MU2 WM2 ltac:(cbn; flia)) as ST2.

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_epi E OK _ q b dd ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11);
      [exact MI2| flia| flia| exact Hdd| reflexivity| exact ST2| exact LOC2| exact SZL| exact COUT2| exact SZC| exact REC2| exact SZR| exact HIGH2| exact SAVED2|].
    intros STQ. apply (aevt_done RT PMc). intros cf Hc. split.
    2:{ apply (cfrm0_of_asta RT Σ2 PMc _ cf Hc). intros ms <-. exact FRM. }
    eapply (lvl_postA_intro0 RT E Σ Σ2 PMc cf); [exact Hc| exact ART2| exact MI2| exact STQ| | exact OUT2| | rewrite EL2; exact EL| exact EF2| rewrite ES2; exact ES| rewrite EC2; exact CR].
    - eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha _. rewrite (AG2 _ Ha). exact (AG1 _ Ha).
    - apply (AINV_A_agree E m m2 AI). intros x Hx. pose proof (ainv_rng_aclient RT Σ E q (bv_unsigned x) LV OK Hx) as CX. rewrite (AG2 _ CX). exact (AG1 _ CX).
  Qed.

  Lemma obj_cok : forall (Σc : rts RT) (m : mem), rt_sp0 RT Σc = rt_sp0 RT Σ -> stk asegs m (ae_lo E) (oi_b I) -> call_ok RT Σc m (wz (oi_b I)) (ae_lo E).
  Proof using CTX OK.
    intros Σc m ES ST. destruct CTX as [Hdd B32 Q16 LOR (QN & NB & N8) _ _ LV _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    pose proof LV as (_ & _ & _ & _ & LWIN). pose proof (ok_lo E OK) as LOW. pose proof (ok_hi E OK) as [HL HT].
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    unfold call_ok. rewrite unsigned_lit by ul. rewrite ES. split; [exact ST|]. split; [exact LWIN|]. split; [ul|]. split; [ul|].
    Z.div_mod_to_equations. flia.
  Qed.

  Lemma obj_pres_down : forall (Σc : rts RT) (dst n : Z) (m m' : mem),
    rt_pres_ex (rt_live RT Σc) (rt_frames RT Σc) (oi_b I) dst n m m' -> rt_live RT Σc = rt_live RT Σ -> rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ ->
    rt_pres_ex (rt_live RT Σ) (rt_frames RT Σ) (oi_q I) dst n m m'.
  Proof using CTX.
    intros Σc dst n m m' PR EL EF a Ha Hd. destruct CTX as [Hdd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _].
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    apply PR; [| exact Hd]. rewrite EL, EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| flia].
  Qed.

  Lemma obj_copyout : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x21 x23 x24 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 : Z) (js4 jo j0 : list byte) (cC cR : list cell),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 w80 w88 w96 w104 (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) cC -> cells_size cC = 24%nat -> rw_cells asegs m (oi_b I + 160) cR -> cells_size cR = 24%nat ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) x20 x21 (wz (oi_f I)) x23 x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb67ec) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2.
    intros until cR. intros OB FRM EF EL ES CR LOC COUT SZC REC SZR SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (obj_cok Σc m ES ST) as COK.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ _ _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).

    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w664 E OK _ q b out); [exact MI| exact LO| flia| flia| flia| ul| exact LOC|].
    pose proof (rw_cells_bytes_at asegs m _ _ REC) as RB. set (rbs := cells_bytes cR) in RB.
    assert (LRB : length rbs = 24%nat) by (subst rbs; rewrite (cells_bytes_length cR (proj1 (proj1 REC))); exact SZR).
    eapply (aevt_memcpyP RT RC PMc FDO MST Σc _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m out (b + 160) rbs (ae_lo E));
      [reflexivity| reflexivity| rewrite LRB; reflexivity| ul| ul| rewrite LRB; cbn; flia| exact RB| | | rewrite LRB; cbn; flia| exact ART0| exact MI| exact COK|].
    { rewrite LRB. apply (checked_src_stack RT AF Σc m _ (ae_lo E) (b + 160) 24 ART0); [ul| ul| rewrite EU; flia]. }
    { rewrite LRB. apply (checked_dst_stack RT AF Σc m _ out 24 ART0); [ul| ul| rewrite EU; flia| exact (proj2 OUT)]. }
    intros t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' m' (ART' & MI' & WM' & ST') PR' BY'.
    rewrite EU in ST', PR'. rewrite LRB in PR'. change (Z.of_nat 24) with 24 in PR'.
    rewrite (ret_pc_even 0xb67fc) by flia.

    pose proof (agree_of_pres_ex _ _ _ _ _ m m' (fun x => aclient (rt_live RT Σc) (rt_frames RT Σc) b x /\ ~ (out <= x < out + 24)) PR' (fun x H => H)) as AG.
    clear RB. pose proof (proj2 OUT) as WOUT. clear OUT. cbn [cells_size csize Nat.add] in WOUT.
    xport_stack SAVED AG. xport_stack HIGH AG. xport_stack LOC AG. xport_frame HDR AG HinF. xport_shadow SH AG HinF.
    xport_stack COUT AG sz SZC. xport_stack REC AG sz SZR.
    assert (OUT' : rw_cells asegs m' out [CB 24 rbs]).
    { rewrite <- LRB. apply rw_cells_CB_intro; [exact BY'|]. rewrite LRB. exact (wr_at_transport asegs m m' _ _ WOUT WM'). }
    pose proof (obj_pres_down Σc out 24 m m' PR' EL EF) as PRq.
    eapply (obj_fin Σc m'); [| exact FRM| exact EF| exact EL| exact ES| exact CR| exact LOC| reflexivity| exact COUT| exact SZC| exact REC| exact SZR| exact SH| exact OUT'].
    split; [exact MI'|]. split; [exact ART'|]. split; [exact ST'|]. split.
    { exact (AINV_A_pres_ex RT Σ E q out 24 m m' LV OK AI PRq ltac:(flia)). }
    split; [exact SAVED|]. split; [exact HIGH|]. split; [exact HDR|].
    eapply rt_pres_fp_trans; [exact PRES|]. eapply (rt_pres_fp_of_ex _ _ q q out 24); [exact PRq| flia|]. intros a Ha. cbn [outside] in Ha. flia.
  Qed.

  Lemma obj_tails : forall (Σc : rts RT) (m : mem) (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x20 x24 x25 x26 x28 x29 x30 x31 : word)
      (w24 w32 w40 w48 w56 w64 w72 w88 w96 w104 w120 w128 : word)
      (F : bvmap 5 word) (fc : bv 32) (v4 v5 v6 sl L0 vj j' : Z) (rest : list Z) (js4 jo j0 jco jt : list byte),
    obase RT E Σ I Σc m -> frm0 fc ->
    rt_frames RT Σc = (oi_f I, 1%nat) :: rt_frames RT Σ -> rt_live RT Σc = rt_live RT Σ -> rt_sp0 RT Σc = rt_sp0 RT Σ ->
    oi_ptr I = 47 :: rest -> zlength rest = L0 ->
    (sl = 18446744073709551615 /\ rt_credit RT Σ - obj_costA d (oi_L I) <= rt_credit RT Σc) \/
    (0 <= sl < L0 /\ rt_credit RT Σ - obj_costA d (oi_L I) + elem_costA d (L0 - sl) <= rt_credit RT Σc) ->
    elem (ae_T E) (ae_S E) (ae_sn E) ck_any d vj j' -> 0 <= vj -> j' <= ae_n E - 1 ->
    rw_cells asegs m (oi_b I) (obj_locA j0 w24 w32 w40 w48 w56 w64 w72 (Z_to_bv 64 sl) w88 w96 w104 (Z_to_bv 64 (oi_out I)) w120 w128) ->
    rw_cells asegs m (oi_b I + 136) [CB 24 jco] ->
    rw_cells asegs m (oi_b I + 160) [C8 (Z_to_bv 64 (ae_DOC E)); C8 (Z_to_bv 64 vj); C4 (Z_to_bv 64 0); CB 4 jt] ->
    rw_cells asegs m (shad (oi_f I)) (obj_sh v4 v5 v6 js4) -> rw_cells asegs m (oi_out I) [CB 24 jo] ->
    aevt RT PMc Σc (Kpost RT E d Σ I PMc)
      (MS (mkR x1 (wz (oi_b I)) (oi_gp I) (wz TPV) x5 x6 x7 (wz (oi_q I)) (wz (oi_b I)) x10 x11 x12 x13 x14 x15 x16 x17
               (wz (oi_f I)) (wz (shad (oi_f I))) x20 (wz (oi_P I + 1)) (wz (oi_f I)) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31)
          F (wz 0xb67b0) fc None m (seg_rom asegs)).
  Proof using AF CTX FDO MST OK RC2 HELEM.
    intros until jt. intros OB FRM EF EL ES EPTR ZL0 SL ELV VJ0 JN LOC COUT REC SH OUT.
    pose proof (rc2_rt RT RC2) as RC.
    pose proof CTX as CTX'. destruct CTX' as [Hdd B32 Q16 LOR (QN & NB & N8) (QO & OB' & O8) NO LV PAT TY NXT TEND TILES I0 EN EF1 EL1 ES1 EC1 FRB CRB LVB F0 F64 FTOP FLO FHI FSH S0 SHI].
    pose proof OB as OB0. destruct OB as (MI & ART0 & ST & AI & SAVED & HIGH & HDR & PRES).
    pose proof (obj_cok Σc m ES ST) as COK.
    oname. assert (DDR : 0 <= dd <= 16) by (clear - Hdd; lia).
    pose proof OK as OK'. destruct OK' as [_ _ P1F _ _ _ _ _ _ LOW [HL HT]].
    pose proof LV as (_ & _ & _ & _ & LWIN).
    pose proof (af_sp0_range RT AF Σc m ART0) as SP0R. rewrite ES in SP0R.
    assert (LO : ae_lo E + 304 <= q) by ul.
    assert (HinF : In (f, 1%nat) (rt_frames RT Σc)) by (rewrite EF; left; reflexivity).
    assert (EU : bv_unsigned (Z_to_bv 64 b) = b) by (apply unsigned_lit; ul).
    pose proof (ptr_atA_facts E P ptr m OK PAT (proj1 (proj2 (proj2 AI)))) as (PTRB & PTRF & PP0 & PP1 & PL).
    pose proof (lvl_ptr_range E OK P ptr PAT ltac:(rewrite EPTR; discriminate)) as (PB0 & PB1 & PB2 & PB3).
    rewrite EPTR in PL, PB2. rewrite zlength_cons in PL, PB2. pose proof (zlength_nonneg rest) as ZLN.
    apply (aevt_evt RT AF PMc MST).
    eapply (obj_w628 E OK _ q b P L0 sl); [exact MI| exact LO| flia| flia| flia| ul| flia| ul| destruct SL as [[X _]|[X _]]; [left; exact X| right; exact X]| exact LOC| |].
    {
      intros ->. destruct SL as [[_ CR]|[X _]]; [| exfalso; flia].
      eapply (obj_copyout Σc m); [exact OB0| exact FRM| exact EF| exact EL| exact ES| exact CR| exact LOC| exact COUT| reflexivity| exact REC| reflexivity| exact SH| exact OUT]. }

    intros SLR. destruct SL as [[X _]|[_ CR]]; [exfalso; flia|].
    assert (CST : 0 <= elem_costA d (L0 - sl) /\ 0 <= rt_credit RT Σ - obj_costA d (zlength ptr)) by (unfold elem_costA, obj_costA, LVL_C1, DCOST in *; flia).
    set (ptr' := skipn (S (Z.to_nat sl)) ptr).
    assert (ZL' : zlength ptr' = L0 - sl).
    { subst ptr'. rewrite zlength_skipn by (rewrite EPTR; cbn [length]; unfold zlength in ZL0; flia). rewrite EPTR, zlength_cons. flia. }
    assert (PAT' : ptr_atA E (P + 1 + sl) ptr').
    { subst ptr'. replace (P + 1 + sl) with (P + Z.of_nat (S (Z.to_nat sl))) by flia. apply ptr_atA_skip; [exact PAT|].
      rewrite EPTR. cbn [length]. unfold zlength in ZL0. flia. }
    pose proof (a_live_mono RT Σ Σc E LV ltac:(rewrite EL; auto) ltac:(rewrite EF; intros x Hx; right; exact Hx) ES) as LVc.
    apply (proj1 (rw_cells_app asegs m _ [_; _] _)) in REC. destruct REC as [RECN RECE]. cbn [cells_size csize Nat.add] in RECE.
    replace (b + 160 + Z.of_nat 16) with (b + 176) in RECE by flia.
    assert (PRE' : lvl_pre RT E Σc m b (b + 136) (b + 160) vj jco (elem_needA d) (elem_costA d (zlength ptr')) d).
    { unfold lvl_pre. rewrite ZL', EF, EL. split; [exact RECN|]. split; [flia|]. split; [ul|]. split; [Z.div_mod_to_equations; flia|].
      split; [exact COUT|]. split; [flia|]. split; [ul|]. split; [Z.div_mod_to_equations; flia|]. split; [right; flia|].
      split; [exact ART0|]. split; [exact MI|]. split; [exact ST|]. split; [ul|]. split; [Z.div_mod_to_equations; flia|].
      split; [cbn [length]; flia|]. split; [flia| exact LVB]. }
    eapply (aevt_rt RT PMc Σc _ _ _); [| exact FRM|].
    { rewrite <- ZL'. exact (HELEM Σc PMc ptr' vj j' b (b + 136) (b + 160) (P + 1 + sl) (wz 0xb67d4) gp x5 x6 x7 (wz q) (wz b) x14 x15 x16 x17
                                    (wz f) (wz (shad f)) x20 (wz (P + 1)) (wz f) (wz L0) x24 x25 x26 (wz 2147450880) x28 x29 x30 x31 F fc m jco
                                    FDO MST LVc AI PAT' ELV VJ0 JN PRE' FRM). }
    intros cf (Σ' & HA & E1 & E2 & E3 & E4). eexists Σ', _. split; [exact HA|].
    intros ms' (v & m' & RS & (ART' & MI' & ST') & PFP & (jo' & COUT') & AI') FRM'.
    destruct RS as (u0 & u1 & u2 & a1' & a2' & a3' & a4' & a5' & a6' & a7' & u3 & u4 & u5 & u6 & F' & fc' & ->). cbn in FRM'.
    rewrite (ret_pc_even 0xb67d4) by flia. rewrite ZL' in E4.

    assert (AG : agree_on (fun x => aclient (rt_live RT Σc) (rt_frames RT Σc) b x /\ ~ (b + 136 <= x < b + 160)) m m').
    { intros a [Ha Hn]. apply PFP; [exact Ha|]. cbn [outside]. split; [flia| exact Logic.I]. }
    clear COUT. xport_stack SAVED AG. xport_stack HIGH AG. xport_stack LOC AG. xport_frame HDR AG HinF. xport_shadow SH AG HinF.
    xport_stack RECN AG. xport_stack RECE AG. xport_stack OUT AG.
    assert (MONO : forall sp a, sp <= q -> aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> aclient (rt_live RT Σc) (rt_frames RT Σc) sp a).
    { intros sp a Hsp Ha. rewrite EL, EF. apply (aclient_mono _ _ _ _ _ _ _ Ha); [auto| intros x Hx; right; exact Hx| flia]. }
    assert (SPLIT : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) q a -> q <= a \/ a < ae_lo E).
    { intros a Ha. destruct (aclient_split_c RT AF Σc m q a ART0 (MONO q a ltac:(flia) Ha)); [left; flia| right; flia]. }
    assert (PRES' : rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) q [(out, out + 24)] m0 m').
    { eapply rt_pres_fp_trans; [exact PRES|]. intros a Ha Ho. apply PFP; [exact (MONO b _ ltac:(flia) Ha)|].
      cbn [outside]. split; [| exact Logic.I]. destruct (SPLIT _ Ha); flia. }
    clear PFP AG.

    apply (aevt_evt RT AF PMc MST).
    apply (obj_w64c _ q b); [flia| flia| ul| ul|].
    apply (rw_cells_split_CB asegs _ _ [] 24 jo' [] [16; 4; 4]%nat) in COUT'; [| reflexivity]. cbn [mk_CB_cells app] in COUT'.
    repeat match type of COUT' with context [CB ?n ?t] => lazymatch t with firstn _ _ => idtac end; let j := fresh "jc" in set (j := t) in COUT'; clearbody j end.
    pose proof COUT' as CO16. apply (proj1 (rw_cells_app asegs m' _ [_] _)) in CO16. destruct CO16 as [CO16 _].
    pose proof (rw_cells_bytes_at asegs m' _ _ CO16) as RB. cbn [cells_bytes cbytes app] in RB. rewrite app_nil_r in RB.
    lazymatch type of RB with bytes_at _ _ _ ?bs => set (rb := bs) in * end.
    assert (LRB : length rb = 16%nat) by exact (proj1 (proj1 (proj1 CO16))).
    pose proof (obj_cok Σ' m' ltac:(rewrite E3; exact ES) ST') as COK'.
    assert (HinF' : In (f, 1%nat) (rt_frames RT Σ')) by (rewrite E2; exact HinF).
    eapply (aevt_memcpyP RT RC PMc FDO MST Σ' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F' fc' m' (b + 160) (b + 136) rb (ae_lo E));
      [reflexivity| reflexivity| rewrite LRB; reflexivity| ul| ul| rewrite LRB; cbn; flia| exact RB| | | rewrite LRB; cbn; flia| exact ART'| exact MI'| exact COK'|].
    { rewrite LRB. apply (checked_src_stack RT AF Σ' m' _ (ae_lo E) (b + 136) 16 ART'); [rewrite E3; ul| ul| rewrite EU; flia]. }
    { rewrite LRB. apply (checked_dst_stack RT AF Σ' m' _ (b + 160) 16 ART'); [rewrite E3; ul| ul| rewrite EU; flia| exact (proj2 RECN)]. }
    intros t0' t1' t2' b1' b2' b3' b4' b5' b6' b7' t3' t4' t5' t6' F2 m2 (ART2 & MI2 & WM2 & ST2) PR2 BY2.
    rewrite EU in ST2, PR2. rewrite LRB in PR2. change (Z.of_nat 16) with 16 in PR2.
    rewrite (ret_pc_even 0xb67e4) by flia.
    pose proof (agree_of_pres_ex _ _ _ _ _ m' m2 (fun x => aclient (rt_live RT Σ') (rt_frames RT Σ') b x /\ ~ (b + 160 <= x < b + 160 + 16)) PR2 (fun x H => H)) as AG2.
    clear RB CO16. pose proof (proj2 RECN) as WREC. clear RECN. cbn [cells_size csize Nat.add] in WREC.
    xport_stack SAVED AG2. xport_stack HIGH AG2. xport_stack LOC AG2. xport_frame HDR AG2 HinF'. xport_shadow SH AG2 HinF'.
    xport_stack COUT' AG2. xport_stack RECE AG2. xport_stack OUT AG2.
    assert (REC2 : rw_cells asegs m2 (b + 160) [CB 16 rb; C4 (Z_to_bv 64 0); CB 4 jt]).
    { change [CB 16 rb; C4 (Z_to_bv 64 0); CB 4 jt] with ([CB 16 rb] ++ [C4 (Z_to_bv 64 0); CB 4 jt]).
      apply (proj2 (rw_cells_app asegs m2 _ [CB 16 rb] _)). split.
      - rewrite <- LRB. apply rw_cells_CB_intro; [exact BY2|]. rewrite LRB. exact (wr_at_transport asegs m' m2 _ _ WREC WM2).
      - cbn [cells_size csize Nat.add]. replace (b + 160 + Z.of_nat 16) with (b + 176) by flia. exact RECE. }
    pose proof (obj_pres_down Σc (b + 160) 16 m' m2 ltac:(rewrite E1, E2 in PR2; exact PR2) EL EF) as PRq.

    apply (aevt_evt RT AF PMc MST).
    apply (rw_cells_split_CB asegs _ _ [CB 16 rb; C4 (Z_to_bv 64 0)] 4 jt [] [4]%nat) in REC2; [| reflexivity]. cbn [mk_CB_cells app] in REC2.
    eapply (obj_w65c E OK _ q b); [exact MI2| exact LO| flia| flia| flia| exact COUT'| |].
    { eapply rw_cells_recastA; [exact REC2| | cbn [cells_bytes cbytes]; reflexivity]. cbn. destruct REC2 as [[W _] _]. cbn in W. tauto. }
    intros m3 MU3 WM3 MI3 REC3.
    assert (FPb : fp_ok RT Σ' (ae_lo E) [(b + 160, b + 184)]) by (constructor; [left; cbn [fst snd]; ul| constructor]).
    pose proof (art_of_munch RT AF Σ' m2 m3 (ae_lo E) _ ART2 ltac:(rewrite E3, ES; exact LWIN) FPb MU3 WM3) as ART3.
    clear REC2 BY2 RECE.
    mport SAVED MU3 WM3. mport HIGH MU3 WM3. mport LOC MU3 WM3. mport HDR MU3 WM3. mport SH MU3 WM3. mport COUT' MU3 WM3. mport OUT MU3 WM3.
    pose proof (stk_transport_disjoint asegs _ m2 m3 (ae_lo E) b ST2 MU3 WM3 ltac:(cbn; flia)) as ST3.
    eapply (obj_copyout Σ' m3); [| exact FRM'| rewrite E2; exact EF| rewrite E1; exact EL| rewrite E3; exact ES| olia| exact LOC| exact COUT'| reflexivity| exact REC3| reflexivity| exact SH| exact OUT].
    split; [exact MI3|]. split; [exact ART3|]. split; [exact ST3|]. split.
    { apply (AINV_A_munch E _ m2 m3 OK (AINV_A_pres_ex RT Σ E q (b + 160) 16 m' m2 LV OK AI' PRq ltac:(flia)) MU3). constructor; [cbn; flia| constructor]. }
    split; [exact SAVED|]. split; [exact HIGH|]. split; [exact HDR|].
    eapply rt_pres_fp_trans; [exact PRES'|]. intros a Ha Ho. cbn [outside] in Ho. destruct (SPLIT _ Ha) as [Hq|Hq].
    - rewrite (MU3 a) by (cbn [outside]; flia). apply PR2; [| flia]. rewrite E1, E2. exact (MONO b _ ltac:(flia) Ha).
    - rewrite (MU3 a) by (cbn [outside]; flia). apply PR2; [| flia]. rewrite E1, E2. exact (MONO b _ ltac:(flia) Ha).
  Qed.
End ObjC.
