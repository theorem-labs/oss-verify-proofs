(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Image.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import ImageA.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr FP.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.Malloc Require Import MallocKit_AB.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import Layout.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.K5.B15 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_leaf Lept_chain LeptC_leaf Lept_objkit LeptL_kit D_iface D_defs
  Ed_fp Ed_fpkit Gq_numa Numa_kit Ed_statics Ed_tracekit Ed_numa_leaf Ed_numa_ival Gm_iface Gq_gaps Gq_iface Gq_thr_iface Gq_thr2_iface Gq_parse_kit Gq_parse_kit2
  Lept_gmax_defs F_atof_kit Gq_thr2_kit Gq_qtab_defs Gq_qtab_loop Gq_qtab_case
  LeptB_guard LeptB_guard2 Gq_guardx.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

(* [comment removed for export] *)
Definition RA_QTAB_CALLOC : Z := 0xa2118.

(* [comment removed for export] *)
Ltac q_own1 RT tl ff kf F1 F2 clr :=
  try (match goal with OWNx : accok _ _ _ tl 8 |- _ => clear OWNx end);
  lazymatch goal with
  | OWN0x : hid (accok ?lv ?frs ?m0 tl 8), AGFx : agree_on ?P ?m0 ?m1, FINx : In (ff, kf) ?frs |- cps _ (ASTA RT ?S _ _) _ =>
      let N := fresh "OWN" in
      assert (N : accok (rt_live RT S) (rt_frames RT S) m1 tl 8)
        by (unfold hid in OWN0x;
            apply (accok_mono lv frs (rt_live RT S) (rt_frames RT S) m1 tl 8);
            [ apply (accok_keep_P lv frs m0 m1 P tl 8 OWN0x AGFx ltac:(lia));
              let zx := fresh "zx" in let Hzx := fresh "Hzx" in intros zx Hzx;
              change ((8 + 7) / 8) with 1 in Hzx;
              split; [ right; right; right; right; exists ff, kf; split; [exact FINx|];
                       clear - Hzx F1 F2; unfold shad, SHB in *; Z.div_mod_to_equations; lia
                     | clr Hzx; unfold parked in *; cbn [outside]; unfold shad, SHB in *;
                       repeat split; try exact I; Z.div_mod_to_equations; lia ]
            | first [solve [live_sub_tac] | solve [live_add_tac]]
            | solve [frames_sub_tac] ])
  end.

(* [comment removed for export] *)
Ltac at_cut RT AF ivt pft :=
  cps_stop; art_now RT AF ivt;
  lazymatch goal with
  | AGF : agree_on ?PF _ ?mm, MUx : munch _ ?mm _ |- _ => is_var PF; agf_munch AGF MUx pft
  | _ => idtac
  end.
(* [comment removed for export] *)
Ltac q_ivt :=
  cbn [ivls_client]; repeat split; try exact I;
  let zz := fresh "zz" in let Hzz := fresh "Hzz" in intros zz Hzz;
  first [ left; ul
        | fframe_tac
        | lazymatch type of Hzz with (?p <= _ < _)%Z =>
            lazymatch goal with OWNx : hid (accok ?lv ?frs ?mx p 8) |- aclient _ _ ?spx _ =>
              let T := fresh "T" in pose proof OWNx as T; unfold hid in T;
              first [ exact (accok_aclient lv frs mx spx p 8 zz T ltac:(lia))
                    | apply (aclient_mono lv frs spx _ _ spx zz (accok_aclient lv frs mx spx p 8 zz T ltac:(lia)));
                      [ first [solve [live_sub_tac] | solve [live_add_tac]] | solve [frames_sub_tac] | lia ] ]; clear T end end
        | lazymatch type of Hzz with (?p <= _ < ?p + ?n)%Z => right; right; left; exists p, n; split; [solve [in_live_tac] | lia] end ].
(* [comment removed for export] *)
Ltac accp_now RT AF ptab :=
  try (match goal with H : acc asegs _ ptab 8 |- _ => clear H end);
  lazymatch goal with A : ART RT ?S ?mc |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    let N := fresh "ACCP" in
    assert (N : acc asegs mc ptab 8)
      by (apply (af_acc_stack RT AF S mc ptab 8 A);
          [ repeat match goal with E : rt_sp0 RT _ = _ |- _ => rewrite E end; unfold STACK_WIN in *; lia
          | unfold USTACK_TOP in *; lia ]) end.
(* [comment removed for export] *)
Ltac q_pft PFS NFA Hx :=
  cbn [outside]; pose proof (PFS _ Hx); try (destruct (NFA _ Hx) as [?N1 ?N2]);
  repeat match goal with NCx : forall a, _ a -> (a < ?p \/ ?p + _ <= a)%Z |- _ => pose proof (NCx _ Hx); clear NCx end;
  let Ho := fresh "Ho" in destruct Hx as [Hx Ho]; cbn [outside] in Ho; unfold shad, SHB in *;
  repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].

(* [comment removed for export] *)
Ltac nobj_cur NOBJ AGF PML NOBJa :=
  pose proof NOBJ as NOBJa; unfold hid in NOBJa;
  lazymatch type of AGF with agree_on _ ?m0 ?ma =>
    lazymatch type of NOBJa with numa_obj ?lv m0 ?na ?c ?ar ?vs =>
      apply (numa_obj_keep lv m0 ma na c ar vs) in NOBJa;
      [| let b := fresh "b" in let k := fresh "k" in let Hb := fresh "Hb" in let a := fresh "a" in let Ha := fresh "Ha" in
         intros b k Hb a Ha; apply AGF; exact (PML b k _ Hb Ha) ]
    end end.
(* [comment removed for export] *)
Ltac obj_fwd NOBJ MU apart :=
  lazymatch type of MU with munch ?W ?ma ?mb =>
  lazymatch type of NOBJ with numa_obj ?lv ma ?na ?c ?ar ?vs =>
    apply (numa_obj_keep lv ma mb na c ar vs) in NOBJ;
    [| let b := fresh "b" in let k := fresh "k" in let a := fresh "a" in let Hin := fresh "Hin" in let Ha := fresh "Ha" in
       intros b k Hin a Ha; apply MU; apart b k a Hin Ha ]
  end end.
(* [comment removed for export] *)
Ltac art_here RT AF S lo ivt :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mf _) =>
      lazymatch goal with
      | _ : ART RT S mf |- _ => idtac
      | A : ART RT S ?mm, MUx : munch ?W ?mm mf, WMx : wmono asegs ?mm mf |- _ =>
          let N := fresh "ARTh" in
          assert (N : ART RT S mf)
            by (apply (art_client_writes RT AF S mm mf lo W A MUx WMx);
                [ repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | ivt ])
      end
  end.
(* [comment removed for export] *)
Ltac subfp_tac ::= clear; let z := fresh "z" in let Hz := fresh "Hz" in intros z Hz; cbn [outside] in Hz |- *; cbn [outside]; lia.

(* [comment removed for export] *)
Ltac q_gc RT m :=
  lazymatch goal with
  | |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
      repeat match goal with
      | H : ART RT _ ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : mem_inv asegs ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : stk asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : LIBH ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : io_ssp ?m' |- _ => tryif constr_eq m' mc then fail else clear H
      | H : acc asegs ?m' _ _ |- _ => tryif constr_eq m' mc then fail else clear H
      | H : wmono asegs ?ma _ |- _ => tryif constr_eq ma m then fail else clear H
      | H : True |- _ => clear H
      end;
      repeat match goal with x : word |- _ => clear x end;
      repeat match goal with x : bvmap 5 word |- _ => clear x end;
      repeat match goal with x : bv 32 |- _ => clear x end;
      repeat match goal with x : list byte |- _ => clear x end;
      repeat match goal with x : mem |- _ => clear x end
  end.
(* [comment removed for export] *)
Ltac clear_old_states RT Σ :=
  lazymatch goal with |- cps _ (ASTA RT ?S _ _) _ =>
    repeat match goal with
    | X : rts RT |- _ =>
        tryif constr_eq X S then fail else tryif constr_eq X Σ then fail else
        (repeat match goal with H : context [X] |- _ => clear H end; clear X)
    end end.

(* [comment removed for export] *)
Lemma qt_u32arr_agree : forall (m m' : mem) A ws, u32arr asegs m A ws ->
  agree_on (fun x => A <= x < A + 4 * Z.of_nat (length ws)) m m' -> u32arr asegs m' A ws.
Proof.
  intros m m' A ws [Hb Hw] AG. split.
  - apply (bytes_at_agree asegs m m' A (u32s ws) Hb). rewrite u32s_length, Nat2Z.inj_mul. exact AG.
  - exact (wr_at_agree_nw asegs m m' A _ Hw AG).
Qed.
(* [comment removed for export] *)
Ltac ua_call LEM TWL D1 D2 :=
  lazymatch goal with AG : agree_on ?P ?ma ?mb, UAx : u32arr asegs ?ma' ?A ?ws |- _ =>
    let N := fresh "UA" in
    assert (N : u32arr asegs mb A ws)
      by (apply (LEM ma mb A ws UAx); let a := fresh "a" in let Ha := fresh "Ha" in intros a Ha; apply AG; cbv beta;
          rewrite TWL in Ha; split; [ right; right; left; exists A, 1024; split; [solve [in_live_tac] | lia] | cbn [outside]; clear - Ha D1 D2; unfold parked in *; lia ]);
    clear UAx; rename N into UA end.
(* [comment removed for export] *)
Ltac ua_leaf MUl WMl TWL :=
  lazymatch type of MUl with munch ?W ?ma ?mb =>
    lazymatch goal with UAx : u32arr asegs ma ?A ?ws |- _ =>
      let N := fresh "UA" in
      pose proof (u32arr_transport asegs W ma mb A ws UAx MUl WMl ltac:(rewrite TWL; cbn [disjoint_from]; repeat split; try exact I; tlia)) as N;
      clear UAx; rename N into UA end end.

Section QTAB_C0.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis CRE8 : pixcmapCreate8_cps RT.
Hypothesis ADDC : pixcmapAddColor_gray_cps RT.

(* [comment removed for export] *)
Lemma live_out5 : forall (S : rts RT) (m : mem) fr slo usp p1 p2 (live0 : list (Z * Z)) b k x,
  ART RT S m -> In (fr, 0%nat) (rt_frames RT S) -> rt_sp0 RT S - STACK_WIN <= slo ->
  (forall e, In e live0 -> In e (rt_live RT S)) ->
  (forall p n, In (p, n) live0 -> p1 + 8 <= p \/ p + n <= p1) -> (forall p n, In (p, n) live0 -> p2 + 8 <= p \/ p + n <= p2) ->
  In (b, k) live0 -> b <= x < b + k ->
  outside [(slo, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (p1, p1 + 8); (p2, p2 + 8)] x.
Proof using AF.
  intros S m fr slo usp p1 p2 live0 b k x HA FIN SLO LS P1 P2 QIN Hx.
  pose proof (af_live_range RT AF S m b k HA (LS _ QIN)) as (_ & R1 & _).
  pose proof (af_frames_range RT AF S m fr 0%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k (LS _ QIN)).
  pose proof (af_fshadow_apart RT AF S m fr 0%nat HA FIN) as (SA1 & _). specialize (SA1 b k (LS _ QIN)).
  change (fs_size 0) with 64 in *. unfold shad, SHB in SA1. pose proof (P1 b k QIN). pose proof (P2 b k QIN).
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.
Lemma live_out6 : forall (S : rts RT) (m : mem) fr slo usp p1 p2 tab (live0 : list (Z * Z)) b k x,
  ART RT S m -> In (fr, 0%nat) (rt_frames RT S) -> rt_sp0 RT S - STACK_WIN <= slo ->
  (forall e, In e live0 -> In e (rt_live RT S)) ->
  (forall p n, In (p, n) live0 -> p1 + 8 <= p \/ p + n <= p1) -> (forall p n, In (p, n) live0 -> p2 + 8 <= p \/ p + n <= p2) ->
  (forall p n, In (p, n) live0 -> tab + 1024 <= p \/ p + n <= tab) ->
  In (b, k) live0 -> b <= x < b + k ->
  outside [(slo, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (p1, p1 + 8); (p2, p2 + 8); (tab, tab + 1024)] x.
Proof using AF.
  intros S m fr slo usp p1 p2 tab live0 b k x HA FIN SLO LS P1 P2 P3 QIN Hx.
  pose proof (af_live_range RT AF S m b k HA (LS _ QIN)) as (_ & R1 & _).
  pose proof (af_frames_range RT AF S m fr 0%nat HA FIN) as (_ & _ & _ & FLV). specialize (FLV b k (LS _ QIN)).
  pose proof (af_fshadow_apart RT AF S m fr 0%nat HA FIN) as (SA1 & _). specialize (SA1 b k (LS _ QIN)).
  change (fs_size 0) with 64 in *. unfold shad, SHB in SA1. pose proof (P1 b k QIN). pose proof (P2 b k QIN). pose proof (P3 b k QIN).
  cbn [outside]. repeat split; try exact I; first [lia | Z.div_mod_to_equations; lia].
Qed.

(* [comment removed for export] *)
Lemma chain_ok_keep_above : forall ras (m m' : mem) lo f, chain_ok m lo f ras ->
  agree_on (fun a => f - 16 <= a < USTACK_TOP) m m' -> chain_ok m' lo f ras.
Proof.
  induction ras as [|ra1 ras IH]; intros m m' lo f H AG; cbn [chain_ok] in *; [exact H|].
  destruct H as (H1 & H2 & H3 & H4 & fp1 & H5 & H6 & H7).
  split; [exact H1|]. split; [exact H2|]. split; [exact H3|]. split; [exact H4|]. exists fp1. split; [exact H5|]. split.
  - apply (rw_cells_agree_nw asegs m m' _ _ H6). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx.
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx. lia.
  - destruct ras as [|ra2 ras']; [exact H7|].
    assert (LE : f + 16 <= fp1) by (cbn [chain_ok] in H7; destruct H7 as (X & _); exact X).
    apply (IH m m' f fp1 H7). eapply agree_sub; [exact AG|]. cbv beta. intros x Hx. lia.
Qed.

Theorem qtab_c0 : qtab_case RT 0.
Proof using AF GP CRE8 ADDC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo ras na arr ptab pcmap x1 x2
    FDO MST -> -> -> -> -> NOBJ OP1 OP2 PC1 PC2 NE UC TRS ENV RES AL.
  unfold lpost, lpost_f, lenv, lres, keeps, keepsL, optrF, optrS in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OP1 as (PTLOW & PTS0 & S0HI & PT8). destruct OP2 as (OWN2 & PQ0 & PQ8 & PQH & PQS).
  destruct (af_client_consts RT AF Σ m ART0) as (G1 & G2 & G3 & G4).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  unfold entry_st, e_makeGrayQuantTableArb, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address, g_GOT_detect_uar, g_detect_stack_use_after_return in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK, QTAB_COST in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  pose proof ST as (STa & STb & _).
  set (PF := fun a => aclient (rt_live RT Σ) (rt_frames RT Σ) usp a /\ outside [(ptab, ptab + 8); (pcmap, pcmap + 8)] a).
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0 Ha) as [H|H]; [left; exact H| right; unfold STACK_WIN in H; lia]. }
  assert (PFO : forall a, PF a -> (a < ptab \/ ptab + 8 <= a) /\ (a < pcmap \/ pcmap + 8 <= a)).
  { intros a [_ Ho]. cbn [outside] in Ho. lia. }
  (* [comment removed for export] *)
  assert (PT0 : 0 < ptab) by (clear - PTLOW STa LOR; lia).
  assert (PTH : ptab + 8 <= 0x7fff7000 \/ 0x10007fff8000 <= ptab) by (right; clear - PTLOW LOW LOR SP0W; lia).
  assert (PTS : ptab + 8 <= 0x10000 \/ SEGTOP_A <= ptab) by (right; unfold SEGTOP_A; clear - PTLOW LOW LOR SP0W; lia).
  assert (PTHI : ptab + 8 <= rt_sp0 RT Σ) by (clear - PTS0 S0HI; lia).
  assert (FP47 : ptab + 8 <= 2^47) by (clear - PTHI SP0R; lia).
  assert (OWNQ : hid (accok (rt_live RT Σ) (rt_frames RT Σ) m pcmap 8)) by (unfold hid; right; exact OWN2).
  pose proof OWN2 as (ffq & kfq & FINQ & FQ1 & FQ2 & _ & _ & FQ47 & _).
  pose proof (af_frames_range RT AF Σ m ffq kfq ART0 FINQ) as (_ & FQW & _ & FQR).
  assert (PQLO : pcmap + 8 <= lo) by (unfold STACK_WIN in FQW; lia).
  (* [comment removed for export] *)
  assert (PQU : pcmap + 8 <= usp - 208) by lia.
  (* [comment removed for export] *)
  assert (PTL : forall p n, In (p, n) (rt_live RT Σ) -> ptab + 8 <= p \/ p + n <= ptab)
    by (intros p n Hp; pose proof (af_live_range RT AF Σ m p n ART0 Hp) as (_ & R & _); unfold STACK_WIN in R; right; lia).
  assert (PQL : forall p n, In (p, n) (rt_live RT Σ) -> pcmap + 8 <= p \/ p + n <= pcmap) by (intros p n Hp; pose proof (FQR p n Hp); lia).
  pose proof (numa_obj_facts _ _ _ _ _ _ NOBJ) as (_ & NCAP & NA0 & NA16 & AR0 & AR16 & INNA & INAR & NANE).
  pose proof (PTL na 32 INNA) as PTNA. pose proof (PTL arr 200 INAR) as PTAR. pose proof (PQL na 32 INNA) as PQNA. pose proof (PQL arr 200 INAR) as PQAR.
  assert (PTPQ : ptab + 8 <= pcmap \/ pcmap + 8 <= ptab) by (right; clear - FQW FQ2 LOW LOR PTLOW; unfold STACK_WIN in *; lia).
  clear FQW FQR.
  (* [comment removed for export] *)
  assert (PML : forall q k a, In (q, k) (rt_live RT Σ) -> q <= a < q + k -> PF a).
  { intros q k a Hq Ha. split; [right; right; left; exists q, k; split; [exact Hq| lia]|].
    cbn [outside]. pose proof (PTL q k Hq). pose proof (PQL q k Hq). lia. }
  assert (ACCP : acc asegs m ptab 8) by (apply (af_acc_stack RT AF Σ m ptab 8 ART0); [unfold STACK_WIN; clear - PTLOW LOW LOR; lia| unfold USTACK_TOP; clear - PTHI SP0R; lia]).
  assert (ACCQ : acc asegs m pcmap 8) by (apply (accok_acc RT AF Σ m pcmap 8 ART0 ltac:(lia)); right; exact OWN2).
  clear OWN2.
  chunk_facts RT AF GP na 32. chunk_facts RT AF GP arr 200.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  assert (NAR : 0 < na /\ na + 32 < 2^47) by (pose proof (af_sp0_range RT AF Σ m ART0) as XR; clear - NA0 CKR XR; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  assert (ARR : 0 < arr /\ arr + 200 < 2^47) by (pose proof (af_sp0_range RT AF Σ m ART0) as XR; clear - AR0 CKR0 XR; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  (* [comment removed for export] *)
  unfold QTAB_RAS in TRS. pose proof (Forall_inv TRS) as TR1. pose proof (Forall_inv (Forall_inv_tail TRS)) as TR2. cbn beta in TR1, TR2. clear TRS.
  assert (RAV : 4096 <= bv_unsigned ra).
  { revert TR1. clear. generalize (bv_unsigned ra) as r. intros r H.
    vm_compute in H. repeat (destruct H as [H|H]; [first [discriminate | injection H; intros; subst; lia] |]). exact (False_ind _ H). }
  hide TR1. hide TR2. hide UC. hide NOBJ.
  park_disj. carve_frame 192%nat ST.
  walk_to AF MST [(usp - 192, usp)] [e_stack_malloc 0%nat].
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS PFS Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  eapply cps_seq.
  { pose proof (gp_stack_malloc_0 RT GP) as SM0; unfold stack_malloc_contract' in SM0; eapply SM0 with (lo := lo); rt_side idtac. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono _ _ usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  fframe_open RT AF PF (rt_live RT Σ) usp 0%nat 64 ltac:(fun Ha => destruct Ha as [Ha _]; exact Ha).
  fframe_chunk RT AF fr 0%nat 64 na 32. fframe_chunk RT AF fr 0%nat 64 arr 200.
  assert (PTFR : fr + 64 <= ptab) by (clear - FRHI LOW LOR PTLOW; unfold STACK_WIN in *; lia).
  pose proof OWNQ as OWNu; unfold hid in OWNu; fframe_optr RT AF fr 0%nat 64 OWNu usp; clear OWNu.
  (* [comment removed for export] *)
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 192, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8)] [0xa1fbc].
  at_cut RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  clear_acc. refresh RT AF. accp_now RT AF ptab. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  nobj_cur NOBJ AGF PML NOBJa.
  lazymatch goal with MUx : munch _ _ ?mc, FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJa MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S ?mm |- _ =>
        exact (live_out5 S mm fr (usp - 208) usp ptab pcmap (rt_live RT Σ) b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                 ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                 ltac:(intros e He; repeat match goal with E : rt_live _ _ = _ |- _ => rewrite E end; exact He) PTL PQL Hin Ha) end);
    art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S mc na 32 A ltac:(solve [in_live_tac])) as ACCn end.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ ?fc0 None ?mm _) =>
      eapply (numaGetCount_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT Σ) na 50 arr (map ival_w EDGE_VALS)) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJa
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | lazymatch goal with |- ?g => idtac "LEAF SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold numaGetCount_post in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & ?).
  clear NOBJa ACCn.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ _ _) => idtac end;
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  fix_ret_pc.
  cbn [map length EDGE_VALS]. change (Z.of_nat 4) with 4.
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRtop. clear FRrec.
  eapply cps_seq.
  { eapply CRE8 with (lo := lo) (ras := bv_unsigned ra :: ras).
    - exact FDO.
    - exact MST.
    - reflexivity.
    - reflexivity.
    - (* [comment removed for export] *)
      unfold uctx. unfold hid in UC; unfold uctx in UC. rewrite ?unsigned_lit by lia. try change (bv_unsigned sp) with usp.
      lazymatch goal with |- chain_ok ?mc _ _ _ =>
      apply (chain_ok_push mc (usp + -192) usp (bv_unsigned ra) (bv_unsigned s0) ras);
      [ lia | lia | unfold USTACK_TOP; lia
      | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
      | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
      | rewrite !Z_to_bv_bv_unsigned; exact FRtop
      | apply (chain_ok_keep_above ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; unfold USTACK_TOP in Haa;
      split; [left; unfold usp in *; clear - Haa PTLOW PTS0; ul| cbn [outside]; unfold usp in *; clear - Haa PTS0 PQLO LOR PTLOW; lia] ] end.
    - unfold hid in TR1. exact TR1.
    - lenv_tac.
    - lres_tac. }
  clear FRtop.
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia] | exact I]).
  lazymatch goal with H : rt_live RT ?S = (?ca, 1024) :: (?cm, 24) :: _ |- _ => rename H into LV1; rename S into Σ1; rename ca into carr; rename cm into cmap end.
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => rename H into CMO end.
  pose proof CMO as ((cpad & CMC) & (CMIN & CM0 & CM16 & _) & (CAIN & CA0 & CA16 & _) & _ & CANE).
  unfold cmap_cells in CMC. cbn [c_arr c_depth c_nalloc c_n] in CMC, CMIN, CM0, CM16, CAIN, CA0, CA16, CANE. change (4 * 256) with 1024 in CAIN. clear CMO.
  lazymatch goal with H : rt_frames RT Σ1 = rt_frames RT ?Sp |- _ =>
    lazymatch goal with H2 : rt_frames RT Sp = (fr, 0%nat) :: rt_frames RT Σ |- _ => rewrite H2 in H; rename H into FRS1 end end.
  assert (LVS1 : rt_live RT Σ1 = (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (rewrite LV1; repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; reflexivity).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    assert (NCC : forall a, PF a -> a < cmap \/ cmap + 24 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σ1 mm [(carr, 1024)] cmap 24 (rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σ1) usp a A);
          [ rewrite LVS1; reflexivity | intros e He; apply in_or_app; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | destruct Ha as [Ha _]; apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRS1; solve [frames_sub_tac]| lia] ]);
    assert (NCR : forall a, PF a -> a < carr \/ carr + 1024 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σ1 mm [] carr 1024 ((cmap, 24) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σ1) usp a A);
          [ rewrite LVS1; reflexivity | intros e He; cbn [app]; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | destruct Ha as [Ha _]; apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRS1; solve [frames_sub_tac]| lia] ]);
    pose proof (live_apart2 RT AF Σ1 mm cmap 24 carr 1024 A ltac:(solve [in_live_tac]) ltac:(solve [in_live_tac]) ltac:(intros E; inversion E)) as DCA;
    (* [comment removed for export] *)
    pose proof (af_live_range RT AF Σ1 mm cmap 24 A ltac:(solve [in_live_tac])) as (_ & PTCM & _);
    pose proof (af_live_range RT AF Σ1 mm carr 1024 A ltac:(solve [in_live_tac])) as (_ & PTCA & _);
    pose proof (af_frames_range RT AF Σ1 mm ffq kfq A ltac:(rewrite FRS1; right; exact FINQ)) as (_ & _ & _ & R2);
    pose proof (R2 cmap 24 ltac:(solve [in_live_tac])) as PQCM; pose proof (R2 carr 1024 ltac:(solve [in_live_tac])) as PQCA; clear R2 end.
  chunk_facts RT AF GP cmap 24. chunk_facts RT AF GP carr 1024.
  fframe_chunk RT AF fr 0%nat 64 cmap 24. fframe_chunk RT AF fr 0%nat 64 carr 1024.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  assert (CMR : cmap + 24 < 2^47) by (pose proof (af_sp0_range RT AF Σ m ART0) as XR; clear - CKR1 XR; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  assert (CAR : carr + 1024 < 2^47) by (pose proof (af_sp0_range RT AF Σ m ART0) as XR; clear - CKR2 XR; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  (* [comment removed for export] *)
  assert (SP1 : rt_sp0 RT Σ1 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CR1 : rt_credit RT Σ - 1 <= rt_credit RT Σ1) by credit_tac.
  (* [comment removed for export] *)
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in PTCM, PTCA end. unfold STACK_WIN in PTCM, PTCA.
  assert (PTC : ptab + 8 <= cmap \/ cmap + 24 <= ptab) by (right; clear - PTCM LOW LOR PTLOW; lia).
  assert (PTA : ptab + 8 <= carr \/ carr + 1024 <= ptab) by (right; clear - PTCA LOW LOR PTLOW; lia).
  assert (PQC : pcmap + 8 <= cmap \/ cmap + 24 <= pcmap) by (clear - PQCM FQ1 FQ2; lia).
  assert (PQA : pcmap + 8 <= carr \/ carr + 1024 <= pcmap) by (clear - PQCA FQ1 FQ2; lia).
  clear PTCM PTCA PQCM PQCA.
  assert (CMU : cmap + 24 <= usp - 208) by (clear - CKR1 LOW LOR; lia). assert (CAU : carr + 1024 <= usp - 208) by (clear - CKR2 LOW LOR; lia).
  clear_old_states RT Σ. q_gc RT m.
  rename Σ1 into Σc. rename LVS1 into LVc. rename FRS1 into FRSc. rename SP1 into SPc. rename CR1 into CRc.
  try clear IN IN0 IN1 IN2.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; exact INAR).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  accp_now RT AF ptab.
  pose proof FR as FRrec. split_before FRrec (C8 s0) FRtop. clear FRrec.
  lazymatch goal with |- cps _ (ASTA _ _ _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
  assert (UC2 : unwind_okC mc (Z_to_bv 64 RA_QTAB_CALLOC) sp (Z_to_bv 64 (usp + -192))) by
   (exists (bv_unsigned ra :: ras); split; [| unfold RA_QTAB_CALLOC; rewrite unsigned_lit by lia; unfold hid in TR2; exact TR2];
    unfold hid in UC; unfold uctx in UC; rewrite ?unsigned_lit by lia; try change (bv_unsigned sp) with usp;
    apply (chain_ok_push mc (usp + -192) usp (bv_unsigned ra) (bv_unsigned s0) ras);
    [ lia | lia | unfold USTACK_TOP; lia
    | pose proof (bv_unsigned_in_range 64 ra); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | pose proof (bv_unsigned_in_range 64 s0); unfold bv_modulus in *; change (2 ^ Z.of_N 64) with (2^64) in *; lia
    | rewrite !Z_to_bv_bv_unsigned; exact FRtop
    | apply (chain_ok_keep_above ras m mc _ _ UC); intros aa Haa; apply AGF; subst PF; cbv beta; unfold USTACK_TOP in Haa;
      split; [left; unfold usp in *; clear - Haa PTLOW PTS0; ul| cbn [outside]; unfold usp in *; clear - Haa PTS0 PQLO LOR PTLOW; lia] ]) end.
  clear FRtop.
  eapply cps_seq.
  { pose proof (gp_calloc RT GP) as CC; unfold calloc_contract in CC; eapply CC with (lo := lo) (nmemb := 256) (size := 4); rt_side idtac.
    all: lazymatch goal with
         | |- unwind_okC _ _ _ _ => exact UC2
         | |- _ => first [ unfold CALLOC_MAX; lia
                         | rewrite LVc; cbn [length]; unfold LIVE_MAX in *; lia
                         | lazymatch goal with |- ?g => idtac "CALLOC SIDE LEFT:" g end ]
         end. }
  clear UC2.
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx Ho]; apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]).
  change (256 * 4) with 1024 in *. change (Z.to_nat 1024) with 1024%nat in *.
  lazymatch goal with H : rt_live RT ?S = (?p, 1024) :: rt_live RT Σc |- _ => rename H into LV2; rename S into Σ2; rename p into tab end.
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs ?mm tab [CB _ _] |- _ =>
    apply u8arr_of_rw_cells in H; destruct H as [TB TW];
    assert (UA : u32arr asegs mm tab (map (Z_to_bv 64) (repeat 0 256))) by (split; [rewrite u32s_zero256; exact TB| exact TW]);
    clear TB TW end.
  set (zs0 := repeat 0 256) in UA. assert (ZSL : Z.of_nat (length zs0) = 256) by (subst zs0; rewrite repeat_length; reflexivity).
  set (tws := map (Z_to_bv 64) zs0) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  lazymatch goal with H : rt_frames RT Σ2 = rt_frames RT Σc |- _ => rewrite FRSc in H; rename H into FRS2 end.
  assert (LVS2 : rt_live RT Σ2 = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (rewrite LV2, LVc; reflexivity).
  lazymatch goal with A : ART RT Σ2 ?mm |- cps _ (ASTA RT Σ2 _ _) _ =>
    assert (NCT : forall a, PF a -> a < tab \/ tab + 1024 <= a)
      by (intros a Ha; apply (live_chunk_apart RT AF Σ2 mm [] tab 1024 ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) (rt_live RT Σ) (rt_frames RT Σ2) usp a A);
          [ rewrite LVS2; reflexivity | intros e He; cbn [app]; right; right; exact He | reflexivity
          | repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia
          | destruct Ha as [Ha _]; apply (aclient_mono _ _ usp _ _ _ _ Ha); [exact (fun e He => He)| rewrite FRS2; solve [frames_sub_tac]| lia] ]);
    pose proof (af_live_disj RT AF Σ2 mm tab 1024 cmap 24 [] ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) A LVS2 ltac:(cbn [app]; right; left; reflexivity)) as DTC;
    pose proof (af_live_disj RT AF Σ2 mm tab 1024 carr 1024 [] ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) A LVS2 ltac:(cbn [app]; left; reflexivity)) as DTA;
    (* [comment removed for export] *)
    assert (TBL : forall p n, In (p, n) (rt_live RT Σ) -> tab + 1024 <= p \/ p + n <= tab)
      by (intros p n Hp; destruct (af_live_disj RT AF Σ2 mm tab 1024 p n [] ((carr, 1024) :: (cmap, 24) :: rt_live RT Σ) A LVS2 ltac:(cbn [app]; right; right; exact Hp)); lia);
    (* [comment removed for export] *)
    pose proof (af_live_range RT AF Σ2 mm tab 1024 A ltac:(solve [in_live_tac])) as (_ & PTTB & _);
    pose proof (af_frames_range RT AF Σ2 mm ffq kfq A ltac:(rewrite FRS2; right; exact FINQ)) as (_ & _ & _ & R2);
    pose proof (R2 tab 1024 ltac:(solve [in_live_tac])) as PQTB; clear R2 end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in PTTB end. unfold STACK_WIN in PTTB.
  assert (PTT : ptab + 8 <= tab \/ tab + 1024 <= ptab) by (right; clear - PTTB LOW LOR PTLOW; lia).
  assert (PQT : pcmap + 8 <= tab \/ tab + 1024 <= pcmap) by (clear - PQTB FQ1 FQ2; lia).
  clear PTTB PQTB.
  chunk_facts RT AF GP tab 1024.
  assert (T16 : tab mod 16 = 0) by assumption. assert (CA0T : 0 < tab) by assumption.
  fframe_chunk RT AF fr 0%nat 64 tab 1024.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  assert (TBR : tab + 1024 < 2^47) by (clear - CKR3 SP0R1; unfold STACK_WIN, USTACK_TOP, SEGTOP_A in *; lia).
  assert (TBU : tab + 1024 <= usp - 208) by (clear - CKR3 LOW LOR; lia).
  (* [comment removed for export] *)
  assert (SP2 : rt_sp0 RT Σ2 = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity).
  assert (CR2 : rt_credit RT Σ - 1 <= rt_credit RT Σ2) by credit_tac.
  clear INNAc INARc LVSUB.
  clear_old_states RT Σ. q_gc RT m.
  rename Σ2 into Σc. rename LVS2 into LVc. rename FRS2 into FRSc. rename SP2 into SPc. rename CR2 into CRc.
  try clear IN IN0 IN1 IN2 IN3.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  accp_now RT AF ptab.
  (* [comment removed for export] *)
  split_last_CB FRM [8; 4; 20]%nat. split_at FRM 3%nat FRV. split_at FRV 1%nat CVAL. split_at CVAL 1%nat FRV2.
  destruct (cb4_c4 _ _ _ CVAL) as [ov CVALw]. clear CVAL FRV FRV2. rename CVALw into CVAL.
  assert (NINT : numa_ints (map ival_w EDGE_VALS) EDGE_VALS).
  { split; [reflexivity|]. unfold EDGE_VALS. repeat apply Forall_cons; try apply Forall_nil; unfold loc_ok, LOC_LO, LOC_HI; lia. }
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  nobj_cur NOBJ AGF PML NOBJa.
  lazymatch goal with MUx : munch _ _ ?mc, FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJa MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S ?mm |- _ =>
        exact (live_out5 S mm fr (usp - 208) usp ptab pcmap (rt_live RT Σ) b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                 ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                 LVSUB PTL PQL  Hin Ha) end);
    art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S mc na 32 A ltac:(solve [in_live_tac])) as ACCn;
    pose proof (acc_live RT AF S mc arr 200 A ltac:(solve [in_live_tac])) as ACCa;
    lazymatch goal with MI : mem_inv asegs mc |- _ => pose proof (ed_ro_facts mc MI) as RO end end.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCV.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (numaGetIValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT Σ) na 50 arr (map ival_w EDGE_VALS) EDGE_VALS 0 (fr + 32) 45) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJa
         | |- numa_ints _ _ => exact NINT
         | |- nth_error _ _ = _ => reflexivity
         | |- ED_RO _ => exact RO
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LEAF0 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MUl & WMl & ? & ? & CVALn).
  clear CVAL NOBJa RO ACCn ACCa ACCV. rename CVALn into CVAL.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  ua_leaf MUl WMl TWL.
  clear MUl WMl.
  fix_ret_pc.
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 13.
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 8 256 0))
      by (unfold cmap_obj, cmap_ok, chunk; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 256) with 1024;
          split; [eexists; exact CMC
                | split; [split; [exact INCMc| clear - CM0 CM16; lia]
                | split; [split; [exact INCAc| clear - CA0 CA16; lia]
                | split; [split; [cbn; tauto| lia] | exact CANE]]]]) end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 8 256 0) (v := 22).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO CMC.
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  ua_call qt_u32arr_agree TWL DTC DTA.
  fold_ag ltac:(fun Hx => pose proof (NCC _ Hx) as Xc; pose proof (NCR _ Hx) as Xa; destruct Hx as [Hx Ho]; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => destruct H as ((cpad0 & CMC) & _); unfold cmap_cells in CMC; cbn [c_arr c_depth c_nalloc c_n] in CMC end.
  try (lazymatch goal with H : rw_cells asegs _ (carr + _) [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  try (lazymatch goal with H : rw_cells asegs _ carr [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact LVc);
    assert (FRSa : rt_frames RT Sa = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames RT _ = rt_frames RT _ |- _ => rewrite H end; exact FRSc);
    assert (SPa : rt_sp0 RT Sa = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity);
    assert (CRa : rt_credit RT Σ - 1 <= rt_credit RT Sa) by credit_tac;
    clear INNAc INARc INCMc INCAc INTBc LVSUB;
    clear_old_states RT Σ; q_gc RT m;
    rename Sa into Σc; rename LVSa into LVc; rename FRSa into FRSc; rename SPa into SPc; rename CRa into CRc end.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8); (tab, tab + 1024)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  rewrite ?sx32_small by lia.
  
  (* [comment removed for export] *)
  try replace (0 <? tab) with true in * by (symmetry; apply Z.ltb_lt; lia).
  try replace (Z.land tab 3) with 0 in * by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - T16 CA0T; Z.div_mod_to_equations; lia).
  try replace (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in * by reflexivity.
  try change (Z.b2z true) with 1 in *.
  lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (acc_live RT AF S mc tab 1024 A ltac:(solve [in_live_tac])) as ACCT end.
  subst tws. clear TWL.
  eapply evt_cut.
  { eapply (qfill1_loop_j0 45%nat).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact UA
         | |- Z.of_nat (length _) = 256 => exact ZSL
         | |- acc _ _ _ _ => exact ACCT
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LOOP0 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold qfill1_exit in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & UAn).
  clear UA ACCT. rename UAn into UA.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  lazymatch type of UA with u32arr _ _ _ (map _ ?z) => set (zs1 := z) in UA end.
  assert (ZSLn : Z.of_nat (length zs1) = 256) by (subst zs1; rewrite zfill_length; exact ZSL). clear ZSL. rename ZSLn into ZSL.
  set (tws := map (Z_to_bv 64) zs1) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 19; fold_reg 20; fold_reg 22.
  (* [comment removed for export] *)
  nobj_cur NOBJ AGF PML NOBJa.
  lazymatch goal with MUx : munch _ _ ?mc, FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJa MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S ?mm |- _ =>
        exact (live_out6 S mm fr (usp - 208) usp ptab pcmap tab (rt_live RT Σ) b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                 ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                 LVSUB PTL PQL TBL Hin Ha) end);
    art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S mc na 32 A ltac:(solve [in_live_tac])) as ACCn;
    pose proof (acc_live RT AF S mc arr 200 A ltac:(solve [in_live_tac])) as ACCa;
    lazymatch goal with MI : mem_inv asegs mc |- _ => pose proof (ed_ro_facts mc MI) as RO end end.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCV.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (numaGetIValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT Σ) na 50 arr (map ival_w EDGE_VALS) EDGE_VALS 1 (fr + 32) 75) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJa
         | |- numa_ints _ _ => exact NINT
         | |- nth_error _ _ = _ => reflexivity
         | |- ED_RO _ => exact RO
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LEAF1 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MUl & WMl & ? & ? & CVALn).
  clear CVAL NOBJa RO ACCn ACCa ACCV. rename CVALn into CVAL.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  ua_leaf MUl WMl TWL.
  clear MUl WMl.
  fix_ret_pc.
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 13.
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 8 256 1))
      by (unfold cmap_obj, cmap_ok, chunk; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 256) with 1024;
          split; [eexists; exact CMC
                | split; [split; [exact INCMc| clear - CM0 CM16; lia]
                | split; [split; [exact INCAc| clear - CA0 CA16; lia]
                | split; [split; [cbn; tauto| lia] | exact CANE]]]]) end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 8 256 1) (v := 60).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO CMC.
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  ua_call qt_u32arr_agree TWL DTC DTA.
  fold_ag ltac:(fun Hx => pose proof (NCC _ Hx) as Xc; pose proof (NCR _ Hx) as Xa; destruct Hx as [Hx Ho]; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => destruct H as ((cpad1 & CMC) & _); unfold cmap_cells in CMC; cbn [c_arr c_depth c_nalloc c_n] in CMC end.
  try (lazymatch goal with H : rw_cells asegs _ (carr + _) [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  try (lazymatch goal with H : rw_cells asegs _ carr [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact LVc);
    assert (FRSa : rt_frames RT Sa = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames RT _ = rt_frames RT _ |- _ => rewrite H end; exact FRSc);
    assert (SPa : rt_sp0 RT Sa = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity);
    assert (CRa : rt_credit RT Σ - 1 <= rt_credit RT Sa) by credit_tac;
    clear INNAc INARc INCMc INCAc INTBc LVSUB;
    clear_old_states RT Σ; q_gc RT m;
    rename Sa into Σc; rename LVSa into LVc; rename FRSa into FRSc; rename SPa into SPc; rename CRa into CRc end.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8); (tab, tab + 1024)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  rewrite ?sx32_small by lia.
  replace (Z_to_bv 64 (tab + 180)) with (Z_to_bv 64 (tab + 4 * 45)) by (f_equal; lia).
  (* [comment removed for export] *)
  try replace (0 <? tab) with true in * by (symmetry; apply Z.ltb_lt; lia).
  try replace (Z.land tab 3) with 0 in * by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - T16 CA0T; Z.div_mod_to_equations; lia).
  try replace (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in * by reflexivity.
  try change (Z.b2z true) with 1 in *.
  lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (acc_live RT AF S mc tab 1024 A ltac:(solve [in_live_tac])) as ACCT end.
  subst tws. clear TWL.
  eapply evt_cut.
  { eapply (qfill1_loop 30%nat 45).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact UA
         | |- Z.of_nat (length _) = 256 => exact ZSL
         | |- acc _ _ _ _ => exact ACCT
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LOOP1 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold qfill1_exit in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & UAn).
  clear UA ACCT. rename UAn into UA.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  lazymatch type of UA with u32arr _ _ _ (map _ ?z) => set (zs2 := z) in UA end.
  assert (ZSLn : Z.of_nat (length zs2) = 256) by (subst zs2; rewrite zfill_length; exact ZSL). clear ZSL. rename ZSLn into ZSL.
  set (tws := map (Z_to_bv 64) zs2) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 19; fold_reg 20; fold_reg 22.
  (* [comment removed for export] *)
  nobj_cur NOBJ AGF PML NOBJa.
  lazymatch goal with MUx : munch _ _ ?mc, FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJa MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S ?mm |- _ =>
        exact (live_out6 S mm fr (usp - 208) usp ptab pcmap tab (rt_live RT Σ) b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                 ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                 LVSUB PTL PQL TBL Hin Ha) end);
    art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S mc na 32 A ltac:(solve [in_live_tac])) as ACCn;
    pose proof (acc_live RT AF S mc arr 200 A ltac:(solve [in_live_tac])) as ACCa;
    lazymatch goal with MI : mem_inv asegs mc |- _ => pose proof (ed_ro_facts mc MI) as RO end end.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCV.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (numaGetIValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT Σ) na 50 arr (map ival_w EDGE_VALS) EDGE_VALS 2 (fr + 32) 115) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJa
         | |- numa_ints _ _ => exact NINT
         | |- nth_error _ _ = _ => reflexivity
         | |- ED_RO _ => exact RO
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LEAF2 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MUl & WMl & ? & ? & CVALn).
  clear CVAL NOBJa RO ACCn ACCa ACCV. rename CVALn into CVAL.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  ua_leaf MUl WMl TWL.
  clear MUl WMl.
  fix_ret_pc.
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 13.
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 8 256 2))
      by (unfold cmap_obj, cmap_ok, chunk; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 256) with 1024;
          split; [eexists; exact CMC
                | split; [split; [exact INCMc| clear - CM0 CM16; lia]
                | split; [split; [exact INCAc| clear - CA0 CA16; lia]
                | split; [split; [cbn; tauto| lia] | exact CANE]]]]) end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 8 256 2) (v := 95).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO CMC.
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  ua_call qt_u32arr_agree TWL DTC DTA.
  fold_ag ltac:(fun Hx => pose proof (NCC _ Hx) as Xc; pose proof (NCR _ Hx) as Xa; destruct Hx as [Hx Ho]; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => destruct H as ((cpad2 & CMC) & _); unfold cmap_cells in CMC; cbn [c_arr c_depth c_nalloc c_n] in CMC end.
  try (lazymatch goal with H : rw_cells asegs _ (carr + _) [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  try (lazymatch goal with H : rw_cells asegs _ carr [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact LVc);
    assert (FRSa : rt_frames RT Sa = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames RT _ = rt_frames RT _ |- _ => rewrite H end; exact FRSc);
    assert (SPa : rt_sp0 RT Sa = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity);
    assert (CRa : rt_credit RT Σ - 1 <= rt_credit RT Sa) by credit_tac;
    clear INNAc INARc INCMc INCAc INTBc LVSUB;
    clear_old_states RT Σ; q_gc RT m;
    rename Sa into Σc; rename LVSa into LVc; rename FRSa into FRSc; rename SPa into SPc; rename CRa into CRc end.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8); (tab, tab + 1024)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  rewrite ?sx32_small by lia.
  replace (Z_to_bv 64 (tab + 300)) with (Z_to_bv 64 (tab + 4 * 75)) by (f_equal; lia).
  (* [comment removed for export] *)
  try replace (0 <? tab) with true in * by (symmetry; apply Z.ltb_lt; lia).
  try replace (Z.land tab 3) with 0 in * by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - T16 CA0T; Z.div_mod_to_equations; lia).
  try replace (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in * by reflexivity.
  try change (Z.b2z true) with 1 in *.
  lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (acc_live RT AF S mc tab 1024 A ltac:(solve [in_live_tac])) as ACCT end.
  subst tws. clear TWL.
  eapply evt_cut.
  { eapply (qfill1_loop 40%nat 75).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact UA
         | |- Z.of_nat (length _) = 256 => exact ZSL
         | |- acc _ _ _ _ => exact ACCT
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LOOP2 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold qfill1_exit in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & UAn).
  clear UA ACCT. rename UAn into UA.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  lazymatch type of UA with u32arr _ _ _ (map _ ?z) => set (zs3 := z) in UA end.
  assert (ZSLn : Z.of_nat (length zs3) = 256) by (subst zs3; rewrite zfill_length; exact ZSL). clear ZSL. rename ZSLn into ZSL.
  set (tws := map (Z_to_bv 64) zs3) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 19; fold_reg 20; fold_reg 22.
  (* [comment removed for export] *)
  nobj_cur NOBJ AGF PML NOBJa.
  lazymatch goal with MUx : munch _ _ ?mc, FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    obj_fwd NOBJa MUx ltac:(fun b k a Hin Ha =>
      lazymatch goal with A : ART RT S ?mm |- _ =>
        exact (live_out6 S mm fr (usp - 208) usp ptab pcmap tab (rt_live RT Σ) b k (bv_unsigned a) A ltac:(rewrite FRSx; left; reflexivity)
                 ltac:(repeat match goal with E : rt_sp0 _ _ = _ |- _ => rewrite E end; unfold STACK_WIN; lia)
                 LVSUB PTL PQL TBL Hin Ha) end);
    art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) =>
    pose proof (acc_live RT AF S mc na 32 A ltac:(solve [in_live_tac])) as ACCn;
    pose proof (acc_live RT AF S mc arr 200 A ltac:(solve [in_live_tac])) as ACCa;
    lazymatch goal with MI : mem_inv asegs mc |- _ => pose proof (ed_ro_facts mc MI) as RO end end.
  local_acc FSH fr 4%nat 32 FR64 FR0 ACCV.
  eapply evt_cut.
  { lazymatch goal with |- evt _ _ (MS _ ?F0 _ (frm_clear ?fc0) None ?mm _) =>
      eapply (numaGetIValue_evt _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F0 fc0 mm (usp + -192) lo (rt_live RT Σ) na 50 arr (map ival_w EDGE_VALS) EDGE_VALS 3 (fr + 32) 185) end.
    all: lazymatch goal with
         | |- numa_obj _ _ _ _ _ _ => exact NOBJa
         | |- numa_ints _ _ => exact NINT
         | |- nth_error _ _ = _ => reflexivity
         | |- ED_RO _ => exact RO
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- acc _ _ _ _ => assumption
         | |- ro_cells _ _ _ _ => assumption
         | |- stk _ _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LEAF3 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold numaGetIValue_post in PO.
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & -> & MUl & WMl & ? & ? & CVALn).
  clear CVAL NOBJa RO ACCn ACCa ACCV. rename CVALn into CVAL.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    repeat match goal with H : stk asegs ma _ _ |- _ => clear H end;
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  ua_leaf MUl WMl TWL.
  clear MUl WMl.
  fix_ret_pc.
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 13.
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 8 256 3))
      by (unfold cmap_obj, cmap_ok, chunk; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 256) with 1024;
          split; [eexists; exact CMC
                | split; [split; [exact INCMc| clear - CM0 CM16; lia]
                | split; [split; [exact INCAc| clear - CA0 CA16; lia]
                | split; [split; [cbn; tauto| lia] | exact CANE]]]]) end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 8 256 3) (v := 150).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO CMC.
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  ua_call qt_u32arr_agree TWL DTC DTA.
  fold_ag ltac:(fun Hx => pose proof (NCC _ Hx) as Xc; pose proof (NCR _ Hx) as Xa; destruct Hx as [Hx Ho]; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => destruct H as ((cpad3 & CMC) & _); unfold cmap_cells in CMC; cbn [c_arr c_depth c_nalloc c_n] in CMC end.
  try (lazymatch goal with H : rw_cells asegs _ (carr + _) [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  try (lazymatch goal with H : rw_cells asegs _ carr [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact LVc);
    assert (FRSa : rt_frames RT Sa = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames RT _ = rt_frames RT _ |- _ => rewrite H end; exact FRSc);
    assert (SPa : rt_sp0 RT Sa = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity);
    assert (CRa : rt_credit RT Σ - 1 <= rt_credit RT Sa) by credit_tac;
    clear INNAc INARc INCMc INCAc INTBc LVSUB;
    clear_old_states RT Σ; q_gc RT m;
    rename Sa into Σc; rename LVSa into LVc; rename FRSa into FRSc; rename SPa into SPc; rename CRa into CRc end.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8); (tab, tab + 1024)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  rewrite ?sx32_small by lia.
  replace (Z_to_bv 64 (tab + 460)) with (Z_to_bv 64 (tab + 4 * 115)) by (f_equal; lia).
  (* [comment removed for export] *)
  try replace (0 <? tab) with true in * by (symmetry; apply Z.ltb_lt; lia).
  try replace (Z.land tab 3) with 0 in * by (symmetry; change 3 with (Z.ones 2); rewrite Z.land_ones by lia; change (2 ^ 2) with 4; clear - T16 CA0T; Z.div_mod_to_equations; lia).
  try replace (Z.land (Z.b2z (0 <? 1)) (Z.b2z true)) with 1 in * by reflexivity.
  try change (Z.b2z true) with 1 in *.
  lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (acc_live RT AF S mc tab 1024 A ltac:(solve [in_live_tac])) as ACCT end.
  subst tws. clear TWL.
  eapply evt_cut.
  { eapply (qfill1_loop 70%nat 115).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact UA
         | |- Z.of_nat (length _) = 256 => exact ZSL
         | |- acc _ _ _ _ => exact ACCT
         | |- rw_cells _ _ _ [C4 _] => exact CVAL
         | |- mem_inv _ _ => assumption
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | clear - FR64; Z.div_mod_to_equations; lia | lazymatch goal with |- ?g => idtac "LOOP3 SIDE LEFT:" g end ]
         end. }
  intros ms' PO. unfold qfill1_exit in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & UAn).
  clear UA ACCT. rename UAn into UA.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  lazymatch type of UA with u32arr _ _ _ (map _ ?z) => set (zs4 := z) in UA end.
  assert (ZSLn : Z.of_nat (length zs4) = 256) by (subst zs4; rewrite zfill_length; exact ZSL). clear ZSL. rename ZSLn into ZSL.
  set (tws := map (Z_to_bv 64) zs4) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  fold_reg 10; fold_reg 11; fold_reg 12; fold_reg 19; fold_reg 20; fold_reg 22.
  (* [comment removed for export] *)
  at_call RT AF ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  lazymatch goal with |- cps _ (ASTA RT ?S _ (eq (MS _ _ _ _ _ ?mc _))) _ =>
    assert (CMO : cmap_obj (rt_live RT S) mc cmap (mkCmapv carr 8 256 4))
      by (unfold cmap_obj, cmap_ok, chunk; cbn [c_arr c_depth c_nalloc c_n]; change (4 * 256) with 1024;
          split; [eexists; exact CMC
                | split; [split; [exact INCMc| clear - CM0 CM16; lia]
                | split; [split; [exact INCAc| clear - CA0 CA16; lia]
                | split; [split; [cbn; tauto| lia] | exact CANE]]]]) end.
  eapply cps_seq.
  { eapply ADDC with (lo := lo) (cv := mkCmapv carr 8 256 4) (v := 220).
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- cmap_obj _ _ _ _ => exact CMO
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- _ => first [reflexivity | cbn [c_n c_nalloc]; lia | lazymatch goal with |- ?g => idtac "ADDC SIDE LEFT:" g end]
         end. }
  clear CMO CMC.
  after_call RT AF.
  cbn [c_arr c_depth c_nalloc c_n] in *.
  ua_call qt_u32arr_agree TWL DTC DTA.
  fold_ag ltac:(fun Hx => pose proof (NCC _ Hx) as Xc; pose proof (NCR _ Hx) as Xa; destruct Hx as [Hx Ho]; split;
                 [apply (aclient_mono _ _ usp _ _ _ _ Hx); [first [solve [live_sub_tac] | solve [live_add_tac]]| solve [frames_sub_tac]| lia]
                 | cbn [outside]; clear - Xc Xa; lia]).
  lazymatch goal with H : cmap_obj _ _ cmap _ |- _ => destruct H as ((cpad4 & CMC) & _); unfold cmap_cells in CMC; cbn [c_arr c_depth c_nalloc c_n] in CMC end.
  try (lazymatch goal with H : rw_cells asegs _ (carr + _) [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  try (lazymatch goal with H : rw_cells asegs _ carr [C1 _; C1 _; C1 _; C1 _] |- _ => clear H end).
  lazymatch goal with A : ART RT ?Sa ?mm |- cps _ (ASTA RT ?Sa _ (eq (MS _ _ _ _ _ ?mm _))) _ =>
    assert (LVSa : rt_live RT Sa = (tab, 1024) :: (carr, 1024) :: (cmap, 24) :: rt_live RT Σ) by (repeat match goal with H : rt_live RT _ = rt_live RT _ |- _ => rewrite H end; exact LVc);
    assert (FRSa : rt_frames RT Sa = (fr, 0%nat) :: rt_frames RT Σ) by (repeat match goal with H : rt_frames RT _ = rt_frames RT _ |- _ => rewrite H end; exact FRSc);
    assert (SPa : rt_sp0 RT Sa = rt_sp0 RT Σ) by (repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H end; reflexivity);
    assert (CRa : rt_credit RT Σ - 1 <= rt_credit RT Sa) by credit_tac;
    clear INNAc INARc INCMc INCAc INTBc LVSUB;
    clear_old_states RT Σ; q_gc RT m;
    rename Sa into Σc; rename LVSa into LVc; rename FRSa into FRSc; rename SPa into SPc; rename CRa into CRc end.
  assert (INNAc : In (na, 32) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INNA).
  assert (INARc : In (arr, 200) (rt_live RT Σc)) by (rewrite LVc; right; right; right; exact INAR).
  assert (INCMc : In (cmap, 24) (rt_live RT Σc)) by (rewrite LVc; right; right; left; reflexivity).
  assert (INCAc : In (carr, 1024) (rt_live RT Σc)) by (rewrite LVc; right; left; reflexivity).
  assert (INTBc : In (tab, 1024) (rt_live RT Σc)) by (rewrite LVc; left; reflexivity).
  assert (LVSUB : forall e, In e (rt_live RT Σ) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVc; right; right; right; exact He).
  q_own1 RT pcmap ffq kfq FQ1 FQ2 ltac:(fun Hzx => clear - Hzx PTH PQH PTPQ PT8 PQ8 PT0 PQ0 FP47 FQ47).
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  walk_to AF MST [(usp - 208, usp); (fr, fr + 56); (fr / 8 + 2147450880, fr / 8 + 2147450880 + 8); (ptab, ptab + 8); (pcmap, pcmap + 8); (tab, tab + 1024)]
          [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  replace (Z_to_bv 64 (tab + 740)) with (Z_to_bv 64 (tab + 4 * 185)) by (f_equal; lia).
  (* [comment removed for export] *)
  pose proof FR as FRrec. split_before FRrec (C8 (Z_to_bv 64 4)) FRN. clear FRrec. split_at FRN 1%nat FRrest. clear FRrest.
  replace (usp + -136) with (usp + -192 + 56) in FRN by lia.
  lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => art_here RT AF S lo ltac:(q_ivt) end.
  lazymatch goal with A : ART RT ?S ?mc |- evt _ _ (MS _ _ _ _ _ ?mc _) => pose proof (acc_live RT AF S mc tab 1024 A ltac:(solve [in_live_tac])) as ACCT end.
  subst tws. clear TWL.
  eapply evt_cut.
  { eapply (qfill2_loop 71%nat 185) with (nv := 4).
    all: lazymatch goal with
         | |- u32arr _ _ _ _ => exact UA
         | |- Z.of_nat (length _) = 256 => exact ZSL
         | |- acc _ _ _ _ => exact ACCT
         | |- rw_cells _ _ _ [C8 _] => exact FRN
         | |- mem_inv _ _ => assumption
         | |- _ mod 32 = 0 => clear - AL USP0; Z.div_mod_to_equations; lia
         | |- _ => unfold SEGTOP_A; first [ lia | tlia | lazymatch goal with |- ?g => idtac "LOOP5 SIDE LEFT:" g end ]
         end. }
  clear FRN.
  intros ms' PO. unfold qfill2_exit in PO.
  destruct PO as (? & ? & ? & -> & MUl & WMl & ? & UAn).
  clear UA ACCT. rename UAn into UA.
  lazymatch type of MUl with munch _ ?ma ?mb =>
    lazymatch goal with FRSx : rt_frames RT ?S = (fr, 0%nat) :: _ |- _ => loop_art RT AF S mb lo MUl ltac:(q_ivt) end;
    loop_transport ma mb MUl ltac:(fun Hx => repeat split; try exact I; notin_side) end.
  clear MUl WMl.
  lazymatch type of UA with u32arr _ _ _ (map _ ?z) => set (zs5 := z) in UA end.
  assert (ZSLn : Z.of_nat (length zs5) = 256) by (subst zs5; rewrite zfill_length; exact ZSL). clear ZSL. rename ZSLn into ZSL.
  set (tws := map (Z_to_bv 64) zs5) in UA. assert (TWL : Z.of_nat (length tws) = 256) by (subst tws; rewrite length_map; exact ZSL).
  (* [comment removed for export] *)
  awalk [e_numaGetCount; e_pixcmapCreate; e_calloc; e_numaGetIValue; e_pixcmapAddColor; 0xa21c4; 0xa235c; 0xa22a4; 0x90fc4; 0x68bf8; 0x68fb8; 0x68f18; 0xa23c4].
  (* [comment removed for export] *)
  frame_release_g RT AF GP MST Σ fr 0%nat 64 PF AGF PFS usp lo 0xa22ac
    ltac:(q_ivt) ltac:(fun Hx => q_pft PFS NFA Hx) ltac:(fun Hx => exact (proj1 Hx))
    ltac:(fun fl FLN =>
      lazymatch type of FLN with ~ aclient ?lvS ?frsS _ _ =>
        let OP := fresh "OP" in
        match goal with X : (fl + 1 <= _)%Z |- _ =>
          assert (FLPT : fl < ptab \/ ptab + 8 <= fl) by (left; clear - X LOW LOR PTLOW; unfold STACK_WIN in *; lia) end;
        pose proof OWNQ as OP; unfold hid in OP;
        lazymatch type of OP with accok ?lv ?frs ?mo _ _ =>
          pose proof (flag_apart lvS frsS fl pcmap (pcmap + 8) FLN
            ltac:(let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
                  apply (aclient_mono lv frs USTACK_TOP lvS frsS USTACK_TOP x (accok_aclient lv frs mo USTACK_TOP pcmap 8 x OP Hx));
                  [ first [solve [live_sub_tac] | solve [live_add_tac]] | solve [frames_sub_tac] | lia ])) as FLPQ end; clear OP
      end).
  clear_acc. refresh RT AF. lib_refresh RT GP. unfold shad, SHB in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *. park_disj.
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 192, usp)] (@nil Z).
  (* [comment removed for export] *)
  try change (bv_unsigned sp) with usp. awalk (@nil Z).
  try (lazymatch goal with ST' : stk asegs _ lo (usp + -192) |- _ => release_frame FR ST' usp end).
  cps_stop.
  art_now RT AF ltac:(q_ivt).
  lazymatch goal with MUx : munch _ ?mm _ |- _ => agf_munch AGF MUx ltac:(fun Hx => q_pft PFS NFA Hx) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S, tab, cmap, carr end.
  split.
  - eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
    split; [split; [split; [assumption| split; [assumption| split; assumption]]| split; assumption]|].
    split; [intros a Ha Ho; apply AGF; split; assumption|].
    split; [exact PC1|]. split; [exact PC2|].
    split.
    + (* [comment removed for export] *)
      lazymatch type of UA with u32arr _ _ _ ?w => replace (map (Z_to_bv 64) QTAB_VALS) with w by (subst tws zs5 zs4 zs3 zs2 zs1 zs0; vm_compute; reflexivity) end. exact UA.
    + split.
      * (* [comment removed for export] *)
        unfold cmap_obj, cmap_ok, chunk, cmap_cells. cbn [c_arr c_depth c_nalloc c_n]. change (4 * 256) with 1024.
        repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end.
        split; [eexists; exact CMC|].
        split; [split; [solve [in_live_tac]| clear - CM0 CM16; lia]|].
        split; [split; [solve [in_live_tac]| clear - CA0 CA16; lia]|].
        split; [split; [cbn; tauto| lia]| exact CANE].
      * (* [comment removed for export] *)
        unfold hid in NOBJ.
        lazymatch goal with |- numa_obj _ ?mc _ _ _ _ =>
          assert (KL0 : keeps_live (rt_live RT Σ) m mc) by (intros b kk Hb a Ha; apply AGF; exact (PML b kk _ Hb Ha));
          apply (numa_obj_mono (rt_live RT Σ)); [intros e He; repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; right; right; right; exact He|];
          exact (numa_obj_keep _ m mc na 50 arr _ KL0 NOBJ) end.
  - repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
    repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
    repeat split; try reflexivity. credit_tac.
Qed.
End QTAB_C0.
