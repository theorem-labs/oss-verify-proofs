(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import Tac.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep Arr.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.B9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit D_iface D_defs Lept_kit Lept_iface Lept_env LeptC_kit Lept_chain Lept_objkit LeptL_kit Lept_fuzzkit LeptM_destroy_defs Ed_fp Ed_iface Numa_kit Ed_tracekit LeptB_guard LeptB_guard2.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.

Section REALLOC.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Hypothesis GP : rt_gaps RT.
Hypothesis EG : ed_gaps RT.
Hypothesis RC : rt_contracts RT.

(* [comment removed for export] *)
Lemma accok_keep_shadow : forall live frames (m m' : mem) a n, accok live frames m a n ->
  (forall f k, In (f, k) frames -> agree_on (fun x => shad f <= x < shad (f + fs_size k)) m m') -> 0 <= n -> accok live frames m' a n.
Proof.
  intros live frames m m' a n [H|(f & k & Hin & H1 & H2 & H8 & H0 & HT & Hb)] AG Hn; [left; exact H| right].
  exists f, k. repeat (split; [assumption|]). apply (bytes_at_agree asegs m m' _ _ Hb). eapply agree_sub; [exact (AG f k Hin)|].
  cbv beta. intros x Hx. rewrite ushadow_length in Hx by lia. unfold shad in *. split; Z.div_mod_to_equations; lia.
Qed.

(* [comment removed for export] *)
Definition calloc_contract_any : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (nmemb size lo : Z),
  fdfs_only PMc -> mat_stable PMc ->
  0 < nmemb -> 0 < size -> nmemb * size <= CALLOC_SEC_MAX -> a0 = Z_to_bv 64 nmemb -> a1 = Z_to_bv 64 size -> tp = Z_to_bv 64 TP_A ->
  Z.of_nat (length (rt_live RT Σ)) < LIVE_MAX -> mcost (nmemb * size) <= rt_credit RT Σ ->
  ART RT Σ m -> mem_inv asegs m -> call_ok RT Σ m sp lo -> unwind_okC m ra s0 sp ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_calloc m)))
    (fun c => exists (Σ' : rts RT) (p : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 p) m' ms
         /\ rt_after RT Σ' (bv_unsigned sp) lo m m' /\ rt_pres (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) m m'
         /\ wr_at asegs m' p (nmemb * size) /\ acc asegs m' p (nmemb * size)) c
       /\ rt_live RT Σ' = (p, nmemb * size) :: rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ' = rt_credit RT Σ - mcost (nmemb * size) /\ 0 < p /\ p mod 16 = 0 /\ p + nmemb * size < USTACK_TOP).

Lemma calloc_any : calloc_contract_any.
Proof using GP EG.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nmemb size lo
    FDO MST N0 S0 NS A0 A1 TP LL CR HA MI CO UW.
  destruct (Z_le_gt_dec (nmemb * size) CALLOC_MAX) as [PRIM|SEC].
  - pose proof (gp_calloc RT GP) as CC. unfold calloc_contract in CC.
    eapply cps_conseq; [eapply (CC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nmemb size lo);
                         assumption | intros c Hc; exact Hc |].
    cbv beta. intros c (Σ' & p & HAS & L & FR & SP & CRE & P0 & P16 & PU). exists Σ', p.
    split; [| split; [exact L| split; [exact FR| split; [exact SP| split; [| split; [exact P0| split; [exact P16| exact PU]]]]]]].
    + eapply (ASTA_conseq RT); [exact HAS|]. intros ms (m' & R & A & P & CE & AC). exists m'.
      split; [exact R|]. split; [exact A|]. split; [exact P|]. split; [| exact AC].
      destruct CE as [_ W]. cbn [cells_size csize Nat.add] in W. rewrite Nat.add_0_r, Z2Nat.id in W by lia. exact W.
    + rewrite CRE. unfold mcost. unfold CALLOC_MAX in PRIM. rewrite (proj2 (Z.leb_le _ _) PRIM). lia.
  - pose proof (eg_calloc_sec RT EG) as CC. unfold calloc_contract_sec in CC.
    apply (CC Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m nmemb size lo);
      first [assumption | split; [unfold CALLOC_MAX in *; lia| exact NS]].
Qed.

Theorem reallocNew_ok : reallocNew_cps RT.
Proof using AF GP EG RC.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo pind old oldsz newsz vals junk
    FDO MST -> -> -> -> OP PCC OLDC APT OLDCELLS VLEN SZ NSZ ENV RES.
  pose proof (gp_free RT GP) as FREE. unfold free_contractC in FREE.
  unfold lpost_f, lenv, lres, keeps, keepsL, optr, optrL in *. destruct ENV as (LH & SSP & ART0 & MI & ST & LOW & LOR & SPT & SPA & SPB).
  destruct RES as (FRB & LVB & CRB & LVP).
  destruct OP as (OWN & PI0 & PI8 & PIH & PIS). destruct OLDC as (INO & OLD0 & OLD16 & OSZ0).
  pose proof (af_client_consts RT AF Σ m ART0) as (G1 & G2 & _).
  pose proof (af_sp0_range RT AF Σ m ART0) as SP0R. pose proof (af_sp0_win RT AF Σ m ART0) as SP0W.
  pose proof (accok_acc RT AF Σ m pind 8 ART0 ltac:(lia) OWN) as ACCP.
  pose proof (af_acc_live RT AF Σ m old oldsz ART0 INO) as (WRO & ACCO).
  pose proof (af_live_range RT AF Σ m old oldsz ART0 INO) as (_ & OLDR & OLDS).
  pose proof (gp_live_hi RT GP Σ m old oldsz ART0 INO) as OLDSH.
  assert (PILO : pind + 8 <= lo).
  { destruct OWN as [(p & k & Hin & H1 & H2)|(f & k & Hin & H1 & H2 & _)].
    - pose proof (af_live_range RT AF Σ m p k ART0 Hin) as (_ & R & _). lia.
    - pose proof (af_frames_range RT AF Σ m f k ART0 Hin) as (_ & R & _). lia. }
  (* [comment removed for export] *)
  pose proof OLDCELLS as [[OWF OB] _]. rewrite cells_bytes_app, cells_bytes_mapC4 in OB. cbn [cells_bytes cbytes] in OB. rewrite app_nil_r in OB.
  apply cells_wf_app in OWF. destruct OWF as [_ [LJ _]]. cbn [cell_wf] in LJ.
  set (sbs := u32s vals ++ junk) in OB.
  assert (SBL : Z.of_nat (length sbs) = oldsz) by (unfold sbs; rewrite length_app, u32s_length, LJ; lia).
  unfold entry_st, e_reallocNew, g_GOT_shadow_offset_cell, g_shadow_memory_dynamic_address in *.
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (unfold usp; symmetry; apply Z_to_bv_bv_unsigned). rewrite ESP.
  assert (USP : 0 <= usp < 2^64) by (unfold usp; apply bv_unsigned_in_range).
  unfold LSTK, STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A, CALLOC_SEC_MAX in *. unfold SHB in *.
  lazymatch goal with |- cps _ _ ?Q => set (QF := Q) end.
  set (LVF := live_remove old (rt_live RT Σ)) in *.
  set (PF := fun a => aclient LVF (rt_frames RT Σ) usp a /\ outside [(pind, pind + 8)] a).
  assert (OWNA : accok LVF (rt_frames RT Σ) m pind 8).
  { destruct OWN as [(p & k & Hin & H1 & H2)|OF]; [left| right; exact OF]. exists p, k. split; [| lia].
    unfold LVF. apply live_remove_keep; [exact Hin|]. cbn [fst]. intros E. subst p.
    destruct (Z.eq_dec k oldsz) as [->|NEk]; [lia|].
    destruct (in_split _ _ INO) as (l1 & l2 & EL).
    assert (IN2 : In (old, k) (l1 ++ l2)).
    { rewrite EL in Hin. apply in_app_or in Hin. apply in_or_app. destruct Hin as [X|[X|X]]; [left; exact X| injection X; lia| right; exact X]. }
    pose proof (af_live_disj RT AF Σ m old oldsz old k l1 l2 ART0 EL IN2). lia. }
  pose proof (agree_refl PF m) as AGF.
  assert (PFS : forall a, PF a -> usp <= a \/ a < lo).
  { intros a [Ha _]. destruct (aclient_split RT AF Σ m usp a ART0) as [Hs|Hs]; [| left; exact Hs| right; unfold STACK_WIN in Hs; lia].
    apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [| auto| lia]. intros e He. exact (live_remove_sub _ _ _ He). }
  assert (OAP : forall a, PF a -> a < old \/ old + oldsz <= a).
  { intros a [Ha _]. apply (removed_chunk_apart RT AF Σ m old oldsz LVF usp a ART0 INO); [| unfold STACK_WIN; lia| exact Ha].
    intros e He. unfold LVF in He. destruct (live_remove_in _ _ _ He) as [He1 NE1]. split; [exact He1| exact NE1]. }
  walk_to AF MST [(usp - 64, usp)] [e_calloc; 0xe95d4; 0xe9630].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  (* [comment removed for export] *)
  eapply cps_seq.
  { pose proof calloc_any as CC; unfold calloc_contract_any in CC; eapply CC with (lo := lo) (nmemb := 1) (size := newsz); rt_side idtac.
    all: first [ unfold CALLOC_SEC_MAX; lia
               | replace (1 * newsz) with newsz by lia; repeat match goal with H : context [rt_credit] |- _ => revert H end; clear; intros; lia
               | apply unwind_okC_of_ok; rewrite ?unsigned_lit by lia; [exact tr_reallocNew_1| left; lia] ]. }
  after_call RT AF.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx); [solve [live_sub_tac]| solve [frames_sub_tac]| lia]).
  replace (1 * newsz) with newsz in * by lia.
  lazymatch goal with H : rt_live RT ?S = (?p, newsz) :: _ |- _ => rename H into LVN; rename S into Σ1; set (nw := p) in * end.
  assert (INN : In (nw, newsz) (rt_live RT Σ1)) by (rewrite LVN; left; reflexivity).
  assert (INO1 : In (old, oldsz) (rt_live RT Σ1)) by (rewrite LVN; right; exact INO).
  lazymatch goal with A : ART RT Σ1 ?mm |- cps _ (ASTA RT Σ1 _ _) _ =>
    pose proof (af_live_range RT AF Σ1 mm nw newsz A INN) as (_ & NWHI & NWSEG);
    pose proof (gp_live_hi RT GP Σ1 mm nw newsz A INN) as NWSH;
    pose proof (af_live_disj RT AF Σ1 mm nw newsz old oldsz [] (rt_live RT Σ) A LVN ltac:(cbn [app]; exact INO)) as NWO;
    assert (NCA : forall a, PF a -> a < nw \/ nw + newsz <= a)
      by (intros a Ha; destruct Ha as [Ha _]; apply (new_chunk_apart RT AF Σ1 mm nw newsz (rt_live RT Σ) (rt_frames RT Σ) usp a A LVN);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul
          | apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ usp a Ha); [intros e He; exact (live_remove_sub _ _ _ He)| auto| lia] ]);
    (* [comment removed for export] *)
    lazymatch goal with W : wr_at asegs mm nw newsz |- _ => destruct (wr_at_rw_CB mm nw newsz W ltac:(lia)) as (bs0 & NWC0) end
  end.
  repeat match goal with H : rt_sp0 RT _ = _ |- _ => rewrite H in * end.
  unfold STACK_WIN, USTACK_TOP, RT_STACK, SEGTOP_A in *.
  refresh RT AF. unfold SHB in *.
  walk_to AF MST [(usp - 64, usp)] [e_asan_memcpy; 0xe964c; 0xe9688].
  (* [comment removed for export] *)
  lazymatch goal with |- evt ?segs ?Q (MS ?R ?F _ ?fc ?rv ?mm ?ro) =>
    eapply (evt_cut segs (fun ms' => ms' = MS (@bvmap_set 5 word (Z_to_bv 5 9) (Z_to_bv 64 oldsz) R) F (Z_to_bv 64 0xe95a8) fc rv mm ro)) end.
  { destruct (Z.eq_dec oldsz newsz) as [EQ|NE].
    - lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with false by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_ge; lia) end. cbv iota.
      awalk [0xe95a8]. apply evt_done. rewrite <- EQ. norm_regset. reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
        replace c with true by (symmetry; unfold bv_ltu; rewrite !unsigned_lit by lia; apply Z.ltb_lt; lia) end. cbv iota.
      apply evt_done. norm_regset. reflexivity. }
  intros ms ->. norm_regset.
  awalk [e_asan_memcpy; 0xe964c; 0xe9688].
  (* [comment removed for export] *)
  lazymatch goal with H : rw_cells asegs ?mm nw [CB ?n ?bs] |- _ =>
    pose proof (rw_cells_recell mm nw _ [CB (Z.to_nat oldsz) (firstn (Z.to_nat oldsz) bs); CB (Z.to_nat (newsz - oldsz)) (skipn (Z.to_nat oldsz) bs)] H
                  ltac:(destruct H as [[Hwf _] _]; cbn [cells_wf cell_wf] in Hwf |- *; destruct Hwf as [Hl _];
                        rewrite firstn_length_le by lia; rewrite length_skipn; repeat split; lia)
                  ltac:(cbn [cells_bytes cbytes]; rewrite !app_nil_r; apply firstn_skipn)
                  ltac:(cbn [cells_size csize]; lia)) as NWC;
    clear H; pose proof (rw_cells_head _ _ _ _ NWC) as NWH; pose proof (rw_cells_tail _ _ _ _ NWC) as NWT; clear NWC; cbn [csize] in NWT;
    replace (nw + Z.of_nat (Z.to_nat oldsz)) with (nw + oldsz) in NWT by lia end.
  set (tailb := skipn (Z.to_nat oldsz) bs0) in NWT.
  hide NWT. hide PCC. hide OWNA. hide OWN.
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  lazymatch goal with A : ART RT Σ1 ?mm |- _ =>
    pose proof (af_acc_live RT AF Σ1 mm nw newsz A INN) as (WRN1 & ACCN1);
    pose proof (af_acc_live RT AF Σ1 mm old oldsz A INO1) as (WRO1 & ACCO1) end.
  eapply cps_seq.
  { pose proof (rc_asan_memcpy RT RC) as MC0; unfold memcpy_icontract in MC0;
    eapply MC0 with (lo := lo) (d := nw) (s := old) (bs := sbs); rewrite ?SBL.
    all: lazymatch goal with
         | |- fdfs_only _ => exact FDO
         | |- mat_stable _ => exact MST
         | |- Z_to_bv 64 _ = Z_to_bv 64 _ => reflexivity
         | |- _ = Z_to_bv 64 _ => reflexivity
         | |- bytes_at _ _ _ _ => assumption
         | |- ART _ _ _ => assumption
         | |- mem_inv _ _ => assumption
         | |- checked_src _ _ _ _ _ _ _ =>
             unfold checked_src; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [exact ACCO1| left; exists old, oldsz; split; [exact INO1| lia]]| left; lia]
         | |- checked_dst _ _ _ _ _ _ =>
             unfold checked_dst; rewrite ?unsigned_lit by lia;
             split; [intros _; split; [apply (acc_sub asegs _ nw newsz); [exact ACCN1| lia| lia]| left; exists nw, newsz; split; [exact INN| lia]]|];
             split; [intros i Hi; right; right; left; exists nw, newsz; split; [exact INN| lia]| apply (wr_at_sub _ nw newsz); [exact WRN1| lia| lia| lia]]
         | |- call_ok _ _ _ _ _ => unfold call_ok; rewrite ?unsigned_lit by lia; split; [assumption| ul]
         | |- _ \/ _ => clear - NWO SZ0 SZ1; lia
         | |- (_ <= _ <= _) => lia
         | |- (_ < _) => lia
         | |- ?g => idtac "LEFTOVER:" g
         end. }
  after_call RT AF.
  unfold hid in NWT, PCC, OWNA, OWN.
  lazymatch goal with AGx : agree_on (fun a => aclient _ _ _ a /\ ~ _) ?ma ?mb, A : ART RT Σ1 ?mb |- _ =>
    assert (OWNB : accok LVF (rt_frames RT Σ) mb pind 8)
      by (apply (accok_keep_shadow _ _ ma mb pind 8 OWNA); [| lia]; intros f k Hfk; eapply agree_sub; [exact AGx|]; cbv beta; intros xa Hxa;
          pose proof (af_frames_range RT AF Σ1 mb f k A ltac:(repeat match goal with H : rt_frames RT Σ1 = _ |- _ => rewrite H end; exact Hfk)) as (FR0 & FR1 & FR2 & FR3);
          split; [right; right; right; right; exists f, k; split; [repeat match goal with H : rt_frames RT Σ1 = _ |- _ => rewrite H end; exact Hfk| exact Hxa]|];
          unfold shad in Hxa; rewrite SBL; pose proof (af_sp0_range RT AF Σ1 mb A) as SR; clear - Hxa NWSH NWHI FR0 FR1 FR2 SR SZ0 SZ1; unfold STACK_WIN, SEGTOP_A, USTACK_TOP, SHB in *; Z.div_mod_to_equations; lia);
    clear OWNA; rename OWNB into OWNA; clear OWN;
    assert (NAPT : forall a, aclient (rt_live RT Σ) (rt_frames RT Σ) usp a -> a < nw \/ nw + newsz <= a)
      by (intros a Ha; apply (new_chunk_apart RT AF Σ1 mb nw newsz (rt_live RT Σ) (rt_frames RT Σ) usp a A LVN);
          [ assumption | repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end; ul | exact Ha ]);
    assert (PCC2 : rw_cells asegs mb pind [C8 (Z_to_bv 64 old)])
      by (apply (rw_cells_agree_nw asegs ma mb _ _ PCC); eapply agree_sub; [exact AGx|]; cbv beta; intros a Ha; cbn [cells_size csize] in Ha;
          pose proof (accok_aclient _ _ _ usp pind 8 a OWNA ltac:(lia)) as AC1;
          pose proof (aclient_mono LVF (rt_frames RT Σ) usp (rt_live RT Σ) (rt_frames RT Σ) usp a AC1 ltac:(intros e He; exact (live_remove_sub _ _ _ He)) ltac:(auto) ltac:(lia)) as AC0;
          pose proof (NAPT _ AC0); rewrite SBL;
          split; [| lia]; apply (aclient_mono (rt_live RT Σ) (rt_frames RT Σ) usp _ _ _ a AC0); [intros e He; rewrite LVN; right; exact He| | lia];
          repeat match goal with H : rt_frames RT Σ1 = _ |- _ => rewrite H end; auto);
    lazymatch type of NWT with rw_cells _ _ _ ?tcs =>
    assert (NWT2 : rw_cells asegs mb (nw + oldsz) tcs)
      by (apply (rw_cells_agree_nw asegs ma mb _ _ NWT); eapply agree_sub; [exact AGx|]; cbv beta; intros a Ha; cbn [cells_size csize] in Ha; rewrite SBL;
          split; [| lia]; right; right; left; exists nw, newsz; split; [exact INN| lia]) end
  end.
  clear PCC NWT.
  fold_ag ltac:(fun Hx => pose proof (NCA _ Hx) as NC1; destruct Hx as [Hx _]; split;
                [apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx);
                   [ intros e He; rewrite LVN; right; exact (live_remove_sub _ _ _ He)
                   | intros e He; repeat match goal with H : rt_frames RT Σ1 = _ |- _ => rewrite H end; exact He | lia]
                | rewrite SBL; lia]).
  lazymatch goal with H : bytes_at asegs _ nw sbs |- _ => rename H into NWB2 end.
  hide PCC2. hide NWT2. hide NWB2.
  refresh RT AF.
  cps_walk AF MST.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => pose proof (munch_refl [(usp - 64, usp)] mm) as MU1; pose proof (wmono_refl asegs mm) as WM1 end.
  awalk [0xb87f4; 0xe96c4].
  at_call RT AF ltac:(cbn [ivls_client]; split; [intros zz Hzz; left; ul| exact I])
                ltac:(fun Hx => cbn [outside]; pose proof (PFS _ Hx); split; [lia| exact I]).
  eapply cps_seq.
  { eapply FREE with (lo := lo) (p := old) (n := oldsz); try reflexivity; try eassumption.
    all: first [ solve [in_live_tac]
               | rewrite LVN; right; exact INO
               | unfold call_ok; rewrite unsigned_lit by ul; split; [eassumption| ul]
               | apply unwind_okC_of_ok; rewrite !unsigned_lit by ul; [exact tr_reallocNew_2| left; ul]
               ]. }
  after_call RT AF.
  unfold hid in PCC2, NWT2, NWB2.
  lazymatch goal with AGx : agree_on (aclient ?lv2 ?fr2 ?sp2) ?mb ?mc, A : ART RT ?S2 ?mc, L2 : rt_live RT ?S2 = live_remove old (rt_live RT Σ1) |- _ =>
    (* [comment removed for export] *)
    lazymatch goal with
    | O : accok LVF (rt_frames RT Σ) mc pind 8 |- _ => idtac
    | O : accok LVF (rt_frames RT Σ) mb pind 8 |- _ =>
        apply (accok_keep_sub LVF (rt_frames RT Σ) mb mc lv2 fr2 sp2 pind 8) in O;
        [| exact AGx| lia| intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He]
    end;
    assert (SUBL : forall e, In e LVF -> In e lv2)
      by (intros e He; unfold LVF in He; destruct (live_remove_in _ _ _ He) as [He1 Hne];
          repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; apply live_remove_keep; [right; exact He1| exact Hne]);
    assert (INN2 : In (nw, newsz) lv2)
      by (repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; apply live_remove_keep; [left; reflexivity| cbn [fst]; clear - NWO SZ0 SZ1; lia]);
    assert (PCC3 : rw_cells asegs mc pind [C8 (Z_to_bv 64 old)])
      by (apply (rw_cells_agree_nw asegs mb mc _ _ PCC2); eapply agree_sub; [exact AGx|]; cbv beta; intros a Ha; cbn [cells_size csize] in Ha;
          lazymatch goal with O : accok LVF (rt_frames RT Σ) _ pind 8 |- _ => pose proof (accok_aclient _ _ _ usp pind 8 a O ltac:(lia)) as AC1 end;
          apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ a AC1); [exact SUBL| | lia];
          intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He);
    lazymatch type of NWT2 with rw_cells _ _ _ ?tcs =>
    assert (NWT3 : rw_cells asegs mc (nw + oldsz) tcs)
      by (apply (rw_cells_agree_nw asegs mb mc _ _ NWT2); eapply agree_sub; [exact AGx|]; cbv beta; intros a Ha; cbn [cells_size csize] in Ha;
          right; right; left; exists nw, newsz; split; [exact INN2| lia]) end;
    assert (NWB3 : bytes_at asegs mc nw sbs)
      by (apply (bytes_at_agree asegs mb mc _ _ NWB2); eapply agree_sub; [exact AGx|]; cbv beta; intros a Ha; rewrite SBL in Ha;
          right; right; left; exists nw, newsz; split; [exact INN2| lia]);
    assert (ACC3 : acc asegs mc pind 8)
      by (lazymatch goal with O : accok LVF (rt_frames RT Σ) mc pind 8 |- _ =>
            apply (accok_acc_sub RT AF S2 mc LVF (rt_frames RT Σ) pind 8 A ltac:(lia) SUBL); [| exact O];
            intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He end)
  end.
  clear PCC2 NWT2 NWB2.
  fold_ag ltac:(fun Hx => destruct Hx as [Hx _]; apply (aclient_mono LVF (rt_frames RT Σ) usp _ _ _ _ Hx);
                [ intros e He; unfold LVF in He; destruct (live_remove_in _ _ _ He) as [He1 Hne];
                  repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; apply live_remove_keep; [right; exact He1| exact Hne]
                | intros e He; repeat match goal with H : rt_frames RT _ = _ |- _ => rewrite H end; exact He | lia]).
  (* [comment removed for export] *)
  assert (PNW : pind + 8 <= nw \/ nw + newsz <= pind).
  { lazymatch goal with O : accok LVF (rt_frames RT Σ) _ pind 8 |- _ => pose proof (accok_aclient _ _ _ usp pind 8 pind O ltac:(lia)) as A1 end.
    pose proof (NAPT pind (aclient_mono LVF (rt_frames RT Σ) usp (rt_live RT Σ) (rt_frames RT Σ) usp pind A1
                  ltac:(intros e He; exact (live_remove_sub _ _ _ He)) ltac:(auto) ltac:(lia))) as X.
    lazymatch goal with M16 : nw mod 16 = 0 |- _ => clear - X PI8 M16 SZ0 SZ1; Z.div_mod_to_equations; lia end. }
  refresh RT AF.
  walk_to AF MST [(usp - 64, usp); (pind, pind + 8)] (@nil Z).
  cps_stop.
  lazymatch goal with MUx : munch [(usp - 64, usp); (pind, pind + 8)] _ _ |- _ =>
    agf_munch AGF MUx ltac:(fun Hx => cbn [outside]; destruct Hx as [Hx1 Hx2]; cbn [outside] in Hx2; split; [destruct (PFS _ (conj Hx1 Hx2)); lia| split; [tauto| exact I]]) end.
  apply cps_finish. intros c Hc. subst QF. cbv beta.
  lazymatch type of Hc with ASTA RT ?S _ _ _ => exists S end. exists nw.
  rewrite ?SBL in *.
  split.
  2:{ repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_frames _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end.
      repeat match goal with H : rt_credit _ _ = _ |- _ => rewrite H end.
      split; [| split; [reflexivity| split; [reflexivity| unfold mcost; destruct (newsz <=? 64512); lia]]].
      unfold LVF. rewrite lrm_cons. cbn [fst]. replace (nw =? old) with false by (symmetry; apply Z.eqb_neq; clear - NWO SZ0 SZ1; lia). reflexivity. }
  eapply (ASTA_conseq RT); [exact Hc|]. intros ms <-. eexists. exists (junk ++ tailb).
  split; [unfold ret_st; rewrite ESP; do 16 eexists; reflexivity|].
  split.
  { split; [split; [| split; [assumption| assumption]]| split; assumption].
    lazymatch goal with A : ART RT ?S ?mm, MUx : munch ?W ?mm ?mf, WMx : wmono asegs ?mm ?mf |- ART RT ?S ?mf =>
      apply (art_client_writes RT AF S mm mf (usp + -64) W A MUx WMx) end.
    - repeat match goal with H : rt_sp0 _ _ = _ |- _ => rewrite H end. ul.
    - cbn [ivls_client]. split; [intros zz Hzz; left; ul|]. split; [| exact I]. intros zz Hzz.
      lazymatch goal with O : accok LVF (rt_frames RT Σ) _ pind 8 |- aclient ?lv' ?frs' ?sp' _ =>
        apply (aclient_mono LVF (rt_frames RT Σ) sp' lv' frs' sp' zz); [exact (accok_aclient _ _ _ sp' pind 8 zz O Hzz)| | solve [frames_sub_tac]| lia];
        intros e He; unfold LVF in He; destruct (live_remove_in _ _ _ He) as [He1 Hne];
        repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; apply live_remove_keep; [right; exact He1| exact Hne] end. }
  split.
  { intros a Ha Ho. apply AGF. split; [| exact Ho].
    lazymatch type of Ha with aclient ?lv _ _ _ => replace LVF with lv; [exact Ha|] end.
    unfold LVF. repeat match goal with H : rt_live _ _ = _ |- _ => rewrite H end. reflexivity. }
  split; [assumption|].
  split.
  { lazymatch goal with HC : ASTA RT ?S _ _ _, NB : bytes_at asegs ?mf nw sbs, NT : rw_cells asegs ?mf (nw + oldsz) _, A : ART RT ?S ?mm, WMx : wmono asegs ?mm ?mf |- rw_cells asegs ?mf nw _ =>
      pose proof (af_acc_live RT AF S mm nw newsz A ltac:(repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end; apply live_remove_keep; [left; reflexivity| cbn [fst]; clear - NWO SZ0 SZ1; lia])) as (WRF & ACF);
      apply (wr_at_transport asegs mm mf nw newsz) in WRF; [| exact WMx];
      destruct NT as [[NTW NTB] _]; cbn [cells_bytes cbytes] in NTB; rewrite app_nil_r in NTB; cbn [cells_wf cell_wf] in NTW; destruct NTW as [LT _];
      split; [split|];
      [ apply cells_wf_app; split; [apply cells_wf_mapC4|]; cbn [cells_wf cell_wf]; split; [| exact I]; rewrite length_app, LJ, LT; lia
      | rewrite cells_bytes_app, cells_bytes_mapC4; cbn [cells_bytes cbytes]; rewrite app_nil_r, app_assoc; fold sbs;
        apply bytes_at_app; split; [exact NB|]; rewrite SBL; exact NTB
      | rewrite cells_size_app, cells_size_mapC4; cbn [cells_size csize];
        replace (Z.of_nat (4 * length vals + (Z.to_nat (newsz - 4 * Z.of_nat (length vals)) + 0))) with newsz by lia; exact WRF ]
    end. }
  split; [| repeat split; lia]. repeat match goal with H : rt_live RT _ = _ |- _ => rewrite H end. apply live_remove_keep; [left; reflexivity| cbn [fst]; clear - NWO SZ0 SZ1; lia].
Qed.
End REALLOC.
