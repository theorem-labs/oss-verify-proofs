(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import ImageA.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import Layout.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.fhmtgen_fuzzer.lib.K5.A10 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_env LeptC_kit Lept_leaf LeptL_kit Gm_iface Fh_iface Fh_sel_iface Fh_statics Fh_selkit Fh_hm_defs.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section HMSEG.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis BRK : selCreateBrick_cps RT.
Hypothesis SET : selSetElement_cps RT.
Hypothesis ADD : selaAddSel_cps RT.

Lemma hm_seg0 : forall (Σ : rts RT) PMc (ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (m : mem) (lo : Z) (fj : list byte) (sela arr : Z)
    (Q : config -> Prop),
  fdfs_only PMc -> mat_stable PMc -> hm_ctx RT Σ m sp lo sela arr ->
  hm_cont RT PMc Q Σ m (bv_unsigned sp) lo fj s1 s0 ra sela arr gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0xa8a0c 1 ->
  hm_cont RT PMc Q Σ m (bv_unsigned sp) lo fj s1 s0 ra sela arr gp s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 0xa89c8 0.
Proof using AF GP BRK SET ADD.
  intros Σ PMc ra sp gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 m lo fj sela arr Q FDO MST (ENV & RES & NCSA) NEXT.
  intros Σk mc sels ra' t0' t1' t2' s1' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' F' fc'
    (ARTk & MIk & STk & LHk & SSPk & AGF0 & WMk & FRc & SAO & UPTO & LVK & LENK & POSK & FRK & SPK & CRK).
  unfold lenv, lres in ENV, RES. destruct ENV as (_ & _ & ART0 & _ & _ & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  set (usp := bv_unsigned sp) in *.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STDERR_STACK in *. unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  pose proof STk as (STa & STb & _).
  unfold hm_state. unfold hm_cont, hm_state in NEXT.
  pose proof UPTO as (LSEL & _).
  assert (CNT : hm_count 0 = 2 /\ hm_count 1 = 8) by (split; reflexivity). destruct CNT as (CNT & CNT1). rewrite CNT in LENK.
  (* [comment removed for export] *)
  set (PS := fun a => aclient (rt_live RT Σk) (rt_frames RT Σk) usp a).
  set (PF0 := aclient (rt_live RT Σ) (rt_frames RT Σ) usp) in *.
  pose proof (agree_refl PS mc) as AGS.
  assert (PF0S : forall a, PF0 a -> PS a).
  { intros a Ha. apply (aclient_mono _ _ usp _ _ _ _ Ha); [intros e He; rewrite LVK; apply in_or_app; right; exact He| intros e He; rewrite FRK; exact He| lia]. }
  assert (PSS : forall a, PS a -> usp <= a \/ a < lo).
  { intros a Ha. destruct (aclient_split RT AF Σk mc usp a ARTk Ha) as [H|H]; [left; exact H| right; rewrite SPK in H; unfold STACK_WIN in H; lia]. }
  assert (SAIN : forall p n, In (p, n) (sela_live sela arr sels) -> In (p, n) (rt_live RT Σk)) by (intros p n Hp; rewrite LVK; apply in_or_app; left; exact Hp).
  hide LVK.
  refresh RT AF. unfold SHB in *.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 32, usp)] [e_selCreateBrick].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; first [pose proof (PSS _ Hx) | pose proof (PSS _ (PF0S _ Hx))]; split; [lia| exact I]).
  eapply cps_seq.
  { eapply BRK with (lo := lo) (sy := 3) (sx := 3) (cy := 1) (cx := 1) (ty := 2); rt_side idtac.
    all: try lia.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold lres; rewrite FRK, CRK; unfold LIVE_MAX in *; repeat split; [lia| lia| lia| exact POSK]
         end. }
  after_call RT AF.
  lazymatch goal with H : sel_body (rt_live RT ?S) _ ?p ?vv |- _ => rename H into SBODY; rename S into Σc; rename p into sel; rename vv into v end.
  lazymatch goal with H : rt_live RT Σc = _ |- _ => rename H into LVC end.
  lazymatch goal with H : s_sy v = _ |- _ => rename H into ESY end. lazymatch goal with H : s_sx v = _ |- _ => rename H into ESX end.
  lazymatch goal with H : s_name v = _ |- _ => rename H into ENAME end.
  lazymatch goal with H : rt_frames RT Σc = _ |- _ => rename H into FRC end. lazymatch goal with H : rt_sp0 RT Σc = _ |- _ => rename H into SPC end.
  lazymatch goal with H : rt_credit RT Σc = _ |- _ => rename H into CRC end.
  lazymatch goal with A : ART RT Σc ?mm |- cps _ (ASTA RT Σc _ _) _ =>
    assert (NEWAP : forall p n, In (p, n) (tl (sel_live sel v)) -> forall a, PS a -> a < p \/ p + n <= a)
      by (intros p n Hp a Ha; apply (new_chunks_apart RT AF Σc mm _ (rt_live RT Σk) (rt_frames RT Σk) usp A LVC ltac:(congruence)
                                        ltac:(rewrite SPC; ul) p n a Hp Ha)) end.
  assert (SUBC : forall e, In e (rt_live RT Σk) -> In e (rt_live RT Σc)) by (intros e He; rewrite LVC; apply in_or_app; right; exact He).
  pose proof SBODY as (_ & _ & _ & _ & HLEN & _).
  assert (LENC : Z.of_nat (length (rt_live RT Σc)) = Z.of_nat (length (rt_live RT Σk)) + (3 + 2))
    by (rewrite LVC, tl_sel_live, !length_app, length_rev, length_map; cbn [length]; rewrite ESY in HLEN; lia).
  assert (POSC : forall p n, In (p, n) (rt_live RT Σc) -> 0 < n)
    by (intros p n Hp; rewrite LVC in Hp; apply in_app_or in Hp; destruct Hp as [Hp|Hp]; [exact (sel_body_pos _ _ _ _ SBODY p n Hp)| exact (POSK p n Hp)]).
  hide LVC.
  agf_call AGS AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [intros e He; exact He| intros e He; exact He| lia]| exact I]).
  agf_call AGF0 AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (PF0S _ Hx)); [intros e He; exact He| intros e He; exact He| lia]| exact I]).
  clear AG.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 32, usp)] [e_selSetElement].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; first [pose proof (PSS _ Hx) | pose proof (PSS _ (PF0S _ Hx))]; split; [lia| exact I]).
  assert (RIN : In (nth (Z.to_nat 1) (s_rows v) 0, 4 * s_sx v) (tl (sel_live sel v)))
    by (apply row_in_sel_live; apply nth_In; rewrite ESY in HLEN; lia).
  (* [comment removed for export] *)
  lazymatch goal with A : ART RT Σc ?mm |- cps _ (ASTA RT Σc _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    pose proof (af_live_range RT AF Σc mm _ _ A ltac:(unfold hid in LVC; rewrite LVC; apply in_or_app; left; exact RIN)) as (_ & RPHI & _) end.
  rewrite SPC in RPHI. unfold STACK_WIN in RPHI.
  eapply cps_seq.
  { eapply SET with (lo := lo) (sel := sel) (v := v) (row := 1) (col := 1) (ty := 1); rt_side idtac.
    all: rewrite ?ESY, ?ESX; try lia.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- sel_body _ _ _ _ => assumption
         end. }
  clear SBODY.
  after_call RT AF.
  lazymatch goal with H : sel_body (rt_live RT Σc) _ sel v |- _ => rename H into SBODY end.
  agf_call AGS AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ Hx); [exact SUBC| intros e He; rewrite FRC; exact He| lia]
                                         | cbn [outside]; pose proof (NEWAP _ _ RIN _ Hx); split; [lia| exact I]]).
  agf_call AGF0 AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (PF0S _ Hx)); [exact SUBC| intros e He; rewrite FRC; exact He| lia]
                                          | cbn [outside]; pose proof (NEWAP _ _ RIN _ (PF0S _ Hx)); split; [lia| exact I]]).
  clear AG RIN RPHI.
  refresh RT AF. unfold SHB in *.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  walk_to AF MST [(usp - 32, usp)] [e_selaAddSel].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; first [pose proof (PSS _ Hx) | pose proof (PSS _ (PF0S _ Hx))]; split; [lia| exact I]).
  lazymatch type of AGS with agree_on _ _ ?mj =>
    assert (SAOj : sela_obj (rt_live RT Σc) mj sela arr sels)
      by (apply (sela_obj_agree (rt_live RT Σk) (rt_live RT Σc) mc mj sela arr sels SAO SUBC); eapply agree_sub; [exact AGS|];
          intros zz (pz & nz & Hpz & Hzz); right; right; left; exists pz, nz; split; [exact (SAIN pz nz Hpz)| exact Hzz]) end.
  (* [comment removed for export] *)
  pose proof SBODY as (_ & (SINc & _) & _). pose proof SAOj as (_ & (SAINc & _) & (ARINc & _) & _).
  lazymatch goal with A : ART RT Σc ?mm |- cps _ (ASTA RT Σc _ (eq (entry_st _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ?mm))) _ =>
    pose proof (af_live_range RT AF Σc mm sel 32 A SINc) as (_ & SELHI & _);
    pose proof (af_live_range RT AF Σc mm sela 16 A SAINc) as (_ & SELAHI & _);
    pose proof (af_live_range RT AF Σc mm arr 400 A ARINc) as (_ & ARRHI & _) end.
  rewrite SPC in SELHI, SELAHI, ARRHI. unfold STACK_WIN in SELHI, SELAHI, ARRHI.
  eapply cps_seq.
  { eapply ADD with (lo := lo) (sela := sela) (arr := arr) (sel := sel) (sels := sels) (v := v) (i := 0) (live0 := rt_live RT Σ); rt_side idtac.
    all: try lia.
    all: lazymatch goal with
         | |- lenv _ _ _ _ _ _ => lenv_tac
         | |- lres _ _ _ _ _ => unfold lres; rewrite FRC, FRK, CRC, CRK; unfold LIVE_MAX in *; repeat split; [lia| lia| lia| exact POSC]
         | |- sel_body _ _ _ _ => assumption
         | |- sela_obj _ _ _ _ _ => exact SAOj
         | |- rt_live _ _ = _ => unfold hid in LVC, LVK; rewrite LVC, LVK; reflexivity
         | |- _ = Z_to_bv 64 _ => reflexivity
         | |- _ => idtac
         end. }
  clear SBODY SAOj SAO.
  after_call RT AF.
  lazymatch goal with H : sela_obj (rt_live RT ?S) _ sela arr _ |- _ => rename H into SAO'; rename S into Σn end.
  lazymatch goal with H : rt_live RT Σn = (?p, 8) :: _ |- _ => rename H into LVN; set (nmp := p) in * end.
  agf_call AGF0 AG ltac:(fun Hx => split; [apply (aclient_mono _ _ usp _ _ _ _ (PF0S _ Hx)); [exact SUBC| intros e He; rewrite FRC; exact He| lia]|];
                                    cbn [outside]; pose proof (NEWAP _ _ (sel_in_sel_live sel v) _ (PF0S _ Hx)); destruct (NCSA _ Hx); repeat split; lia).
  clear AG.
(* [comment removed for export] *)
  (* [comment removed for export] *)
  eapply NEXT.
  unfold hm_inv. fold PF0.
  split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|]. split; [assumption|].
  split; [exact AGF0|]. split; [assumption|]. split; [assumption|]. split; [exact SAO'|].
  split. { apply (hm_sels_upto_snoc 0 sels sel _ _ 3 3 UPTO); [exact ESY| exact ESX| reflexivity| reflexivity]. }
  unfold hid in LVC, LVK.
  split. { rewrite LVN, LVC, LVK, sela_live_snoc, <- app_assoc. reflexivity. }
  split. { rewrite LVN. cbn [length]. rewrite Nat2Z.inj_succ, LENC, LENK, CNT1. lia. }
  split. { intros p n Hp. rewrite LVN in Hp. destruct Hp as [E|Hp]; [injection E as _ <-; lia| exact (POSC p n Hp)]. }
  split; [congruence|]. split; congruence.
Qed.
End HMSEG.
