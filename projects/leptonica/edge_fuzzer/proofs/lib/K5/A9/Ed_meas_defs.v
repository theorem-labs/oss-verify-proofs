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
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import ImageA.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import RzCPS NodesA SysStep.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.Lib Require Import StoreFast.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.PG Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import Layout.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.AG Require Import Shadow.
From OSSVerify.Proofs.leptonica.edge_fuzzer.lib.K5.A9 Require Import RT_iface RT_traces RT_gaps_iface LeptTac D_kit Lept_kit Lept_iface Lept_lits Lept_env LeptC_kit Lept_chain Lept_leaf Lept_objkit Lept_fuzzkit Lept_litmem D_iface D_defs D_libiface Ed_iface Numa_kit.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Definition MEAS_RAS : list Z := [RA_FUZZ_MEASURE; RA_TOP].

(* [comment removed for export] *)
Lemma tr_meas_profile : numaCreate_trace_ok (RA_MEASURE_PROFILE :: MEAS_RAS).
Proof. unfold numaCreate_trace_ok, MEAS_RAS. apply ct_mem_In; vm_compute; reflexivity. Qed.
Lemma tr_meas_extrema : numaCreate_trace_ok (RA_MEASURE_EXTREMA :: MEAS_RAS).
Proof. unfold numaCreate_trace_ok, MEAS_RAS. apply ct_mem_In; vm_compute; reflexivity. Qed.

(* [comment removed for export] *)
Definition MEAS_MSG_LIT : Z := 0x3a020.
Definition MEAS_FUNC_LIT : Z := 0x39fe0.
Lemma meas_msg_lit : exists l, In (MEAS_MSG_LIT, l) LEPT_LITS.
Proof. apply lept_lit_ex. vm_compute. reflexivity. Qed.
Lemma meas_func_lit : exists l, In (MEAS_FUNC_LIT, l) LEPT_LITS.
Proof. apply lept_lit_ex. vm_compute. reflexivity. Qed.


(* [comment removed for export] *)
Ltac unpark_cells_munch H MU side :=
  unpark H;
  lazymatch type of H with rw_cells asegs ?m0 ?a ?cs =>
    lazymatch type of MU with munch ?W m0 ?m1 =>
      apply (rw_cells_agree_nw asegs m0 m1 a cs) in H;
      [ | apply (agree_of_munch W m0 m1 _ MU);
          let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx;
          cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in Hx; cbn [outside]; side Hx ]
    end end.
Ltac acl_ak AK :=
  let T := type of AK in let T := eval unfold hid, parked in T in
  lazymatch T with accok ?lv ?frs ?m ?a ?n =>
    lazymatch goal with |- aclient ?lv' ?frs' ?sp' ?x =>
      apply (aclient_mono lv frs sp' lv' frs' sp' x);
      [ exact (accok_aclient lv frs m sp' a n x AK ltac:(lia)) | first [solve [live_sub_tac] | solve [live_add_tac]] | frames_sub_tac | lia ] end end.



(* [comment removed for export] *)
Lemma own_frame_shadow_client : forall frs (m : mem) a n x, own_frame frs m a n -> 0 <= n ->
  shad a <= x < shad a + (n + 7) / 8 -> in_fframe_shadow frs x.
Proof.
  intros frs m a n x (f & k & Hin & Hf & Hn & H8 & H0 & _) Hn0 Hx. exists f, k. split; [exact Hin|].
  unfold shad in *. Z.div_mod_to_equations. lia.
Qed.
Lemma own_frame_accok_later : forall live frs (m m' : mem) (P : Z -> Prop) a n, own_frame frs m a n -> agree_on P m m' -> 0 <= n ->
  (forall x, in_fframe_shadow frs x -> shad a <= x < shad a + (n + 7) / 8 -> P x) -> accok live frs m' a n.
Proof.
  intros live frs m m' P a n OW AG Hn HP. apply (accok_keep_P live frs m m' P a n (or_intror OW) AG Hn).
  intros x Hx. apply HP; [exact (own_frame_shadow_client frs m a n x OW Hn Hx) | exact Hx].
Qed.

(* [comment removed for export] *)
Section MeasFrames.
Variable RT : rt_sig.
Hypothesis AF : art_facts RT.
Lemma own_frame_live_apart : forall Σ (m m0 : mem) frs a n b k,
  ART RT Σ m -> own_frame frs m0 a n -> (forall e, In e frs -> In e (rt_frames RT Σ)) -> In (b, k) (rt_live RT Σ) ->
  a + n <= b \/ b + k <= a.
Proof using AF.
  intros Σ m m0 frs a n b k HA (f & kk & Hin & Hf & Hn & _) SUB HB.
  pose proof (af_frames_range RT AF Σ m f kk HA (SUB _ Hin)) as (_ & _ & _ & R). destruct (R b k HB); lia.
Qed.

(* [comment removed for export] *)
Lemma lrm_notin_meas : forall p (l : list (Z * Z)), (forall e, In e l -> fst e <> p) -> live_remove p l = l.
Proof.
  intros p l H. induction l as [|e l IH]; [reflexivity|]. rewrite lrm_cons.
  destruct (Z.eqb_spec (fst e) p) as [E|E]; [exfalso; exact (H e (or_introl eq_refl) E)|].
  rewrite IH; [reflexivity|]. intros e' He'. apply H. right. exact He'.
Qed.
Lemma numa_gone_live : forall Σ (m : mem) na h arr live0,
  ART RT Σ m -> rt_live RT Σ = numa_live na h arr live0 -> 0 < h -> (forall p n, In (p, n) live0 -> 0 < n) ->
  numa_gone na arr (rt_live RT Σ) = live0.
Proof using AF.
  intros Σ m na h arr live0 HA HL Hh LVP. unfold numa_gone. rewrite HL. unfold numa_live.
  assert (D1 : forall p n, In (p, n) ((na, 32) :: live0) -> arr + 4 * h <= p \/ p + n <= arr).
  { intros p n Hin. exact (af_live_disj RT AF Σ m arr (4 * h) p n [] ((na, 32) :: live0) HA ltac:(rewrite HL; reflexivity) Hin). }
  assert (D2 : forall p n, In (p, n) live0 -> na + 32 <= p \/ p + n <= na).
  { intros p n Hin. exact (af_live_disj RT AF Σ m na 32 p n [(arr, 4 * h)] live0 HA ltac:(rewrite HL; reflexivity) ltac:(right; exact Hin)). }
  rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl.
  rewrite (lrm_notin_meas arr).
  2:{ intros [p n] Hin E. cbn [fst] in E. subst p.
      destruct Hin as [E|Hin]; [injection E as E1 E2; destruct (D1 na 32 (or_introl eq_refl)); lia|].
      pose proof (LVP _ _ Hin). destruct (D1 arr n (or_intror Hin)); lia. }
  rewrite lrm_cons. cbn [fst]. rewrite Z.eqb_refl.
  apply lrm_notin_meas. intros [p n] Hin E. cbn [fst] in E. subst p. pose proof (LVP _ _ Hin). destruct (D2 na n Hin); lia.
Qed.
End MeasFrames.



(* [comment removed for export] *)
Lemma numa_arr_cells_size : forall cap vals junk, Z.of_nat (length vals) <= cap ->
  Z.of_nat (cells_size (numa_arr_cells cap vals junk)) = 4 * cap.
Proof.
  intros cap vals junk H. unfold numa_arr_cells. rewrite cells_size_app, cells_size_mapC4. cbn [cells_size csize]. lia.
Qed.
(* [comment removed for export] *)
Ltac unpark_na_munch NA MU side :=
  unpark NA;
  lazymatch type of NA with rw_cells asegs ?m0 ?a (numa_arr_cells ?cap ?vals ?junk) =>
    lazymatch type of MU with munch ?W m0 ?m1 =>
      apply (rw_cells_agree_nw asegs m0 m1 a (numa_arr_cells cap vals junk)) in NA;
      [ | apply (agree_of_munch W m0 m1 _ MU);
          let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in Hx;
          rewrite (numa_arr_cells_size cap vals junk) in Hx by (rewrite ?length_map; lia); cbn [outside];
          repeat match goal with H : parked ?T |- _ => lazymatch T with context [a] => unpark H end end; side Hx ]
    end end.
(* [comment removed for export] *)
Ltac unpark_na_agree NA AG side :=
  unpark NA;
  lazymatch type of NA with rw_cells asegs ?m0 ?a (numa_arr_cells ?cap ?vals ?junk) =>
    lazymatch type of AG with agree_on ?P m0 ?m1 =>
      apply (rw_cells_agree_nw asegs m0 m1 a (numa_arr_cells cap vals junk)) in NA;
      [ | apply (agree_sub P _ m0 m1 AG);
          let x := fresh "x" in let Hx := fresh "Hx" in intros x Hx; cbv beta in Hx;
          rewrite (numa_arr_cells_size cap vals junk) in Hx by (rewrite ?length_map; lia); side Hx ]
    end end.

(* [comment removed for export] *)
Ltac meas_accok_keep H AG m' :=
  lazymatch type of H with accok ?lv ?frs ?m ?a ?n =>
    lazymatch type of AG with agree_on ?P2 m m' =>
      let H2 := fresh "AK" in
      first [ assert (H2 : accok lv frs m' a n)
                by (let OL := fresh "OL" in let OF := fresh "OF" in
                    destruct H as [OL|OF]; [left; exact OL|];
                    apply (own_frame_accok_later lv frs m m' P2 a n OF AG); [lia|];
                    let x := fresh "x" in let HS := fresh "HS" in let Hx := fresh "Hx" in
                    intros x HS Hx; split;
                    [ right; right; right; right;
                      let f := fresh "f" in let k := fresh "k" in let Hin := fresh "Hin" in let Hr := fresh "Hr" in
                      destruct HS as (f & k & Hin & Hr); exists f, k; split; [revert Hin; generalize (f, k); solve [frames_sub_tac] | exact Hr]
                    | cbn [outside]; unfold shad, SHB in *;
                      let OF2 := fresh "OF" in pose proof OF as OF2;
                      let H0 := fresh "HO" in let HT := fresh "HT" in
                      destruct OF2 as (? & ? & _ & _ & _ & _ & H0 & HT & _); change (2 ^ 47) with 140737488355328 in HT;
                      repeat match goal with |- _ /\ _ => split end; try exact I;
                      (* [comment removed for export] *)
                      lazymatch goal with
                      | |- ~ (?lo <= _ < _) =>
                          let b := head_var lo in
                          first [ match goal with FRx : parked (b + _ <= 2147446784 \/ 17594333495296 <= b) |- _ =>
                                    clear - Hx H0 HT FRx; unfold parked in FRx; Z.div_mod_to_equations; lia end
                                | match goal with FRx : b + _ <= 2147446784 \/ 17594333495296 <= b |- _ =>
                                    clear - Hx H0 HT FRx; Z.div_mod_to_equations; lia end
                                | Z.div_mod_to_equations; lia ]
                      end ]);
              clear H; rename H2 into H
            | idtac "note: meas_rt_transport_extra drops accok fact:" H; clear H ]
    end end.
Ltac meas_rt_transport_extra m m' AG :=
  lept_rt_transport_extra m m' AG;
  lazymatch type of AG with
  | agree_on (aclient _ _ _) _ _ => idtac
  | _ => repeat match goal with H : accok _ _ m _ _ |- _ => meas_accok_keep H AG m' end
  end.


(* [comment removed for export] *)
Ltac meas_after_call RT AF fixlive :=
  cps_open RT;
  after_call_unfold;
  fold_zdefs;
  unfold rt_after, rt_after_f in *;
  split_hyps;
  fixlive;
  unfold SEGTOP_A, STACK_WIN, USTACK_TOP, RT_STACK in *;
  repeat match goal with
  | H : context [bv_unsigned (Z_to_bv 64 ?e)] |- _ => rewrite (unsigned_lit e) in H by lia
  end;
  lazymatch goal with
  | P : rt_pres ?lv ?frs ?spc ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (aclient lv frs spc) ma mb) by (intros ? Ha; exact (P _ Ha));
      clear P;
      rt_transport ma mb AG ltac:(fun A => acl_dispatch A)
  | P : rt_pres_ex ?lv ?frs ?spc ?d ?n ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (fun a => aclient lv frs spc a /\ ~ (d <= a < d + n)) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
      clear P;
      rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | notin_side])
  | P : rt_pres_fp ?lv ?frs ?spc ?W ?ma ?mb |- _ =>
      let AG := fresh "AG" in
      assert (AG : agree_on (fun a => aclient lv frs spc a /\ outside W a) ma mb) by (intros ? [Ha Hb]; exact (P _ Ha Hb));
      clear P;
      rt_transport ma mb AG ltac:(fun A => split; [acl_dispatch A | outside_side])
  | _ => idtac
  end;
  fix_ret_pc.

(* [comment removed for export] *)
Definition meas_case (RT : rt_sig) (al : Z) : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (lo : Z) (pix p1 p2 p3 : Z) (v : pixv) (cv : cmapv) (o1 o2 o3 : word) (ras : list Z),
  fdfs_only PMc -> mat_stable PMc -> tp = Z_to_bv 64 TP_A ->
  a0 = Z_to_bv 64 pix -> a1 = Z_to_bv 64 1 -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 1 ->
  a4 = Z_to_bv 64 p1 -> a5 = Z_to_bv 64 p2 -> a6 = Z_to_bv 64 p3 -> a7 = Z_to_bv 64 0 ->
  pix_obj (rt_live RT Σ) m pix v cv -> p_data v <> 0 ->
  optrF RT Σ m p1 4 -> optrF RT Σ m p2 4 -> optrF RT Σ m p3 4 ->
  rw_cells asegs m p1 [C4 o1] -> rw_cells asegs m p2 [C4 o2] -> rw_cells asegs m p3 [C4 o3] ->
  p1 + 4 <= p2 -> p2 + 4 <= p3 ->
  uctx m sp s0 ras -> bv_unsigned ra = RA_FUZZ_MEASURE -> ras = [RA_TOP] ->
  lenv RT Σ m sp lo (LSTK 7) -> lres RT Σ 4 6 (MEASURE_COST (p_w v) (p_h v)) ->
  bv_unsigned sp mod 32 = al ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc
                                         e_pixMeasureEdgeSmoothness m)))
    (fun c => exists (Σ' : rts RT) (rv y1 y2 y3 : word),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 rv m' ms
          /\ lpost_f RT Σ Σ' m m' sp lo /\ keeps RT Σ Σ' sp [(p1, p1 + 4); (p2, p2 + 4); (p3, p3 + 4)] m m'
          /\ rw_cells asegs m' p1 [C4 y1] /\ rw_cells asegs m' p2 [C4 y2] /\ rw_cells asegs m' p3 [C4 y3]) c
       /\ rt_live RT Σ' = rt_live RT Σ
       /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - MEASURE_COST (p_w v) (p_h v) <= rt_credit RT Σ').

Lemma meas_cases : forall RT, meas_case RT 0 -> meas_case RT 16 -> pixMeasureEdgeSmoothness_cps RT.
Proof.
  intros RT C0 C16 Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo
    pix p1 p2 p3 v cv o1 o2 o3 ras H1 H2 H3 H4 H5 H6 H7 H8 H9 H10 H11 H12 H13 H14 H15 H16 H17 H18 H19 H20 H21 H22 H23 H24 H25 H26.
  assert (AL : bv_unsigned sp mod 32 = 0 \/ bv_unsigned sp mod 32 = 16).
  { destruct H25 as (_ & _ & _ & _ & _ & _ & _ & _ & SPA & _). clear - SPA. Z.div_mod_to_equations. lia. }
  destruct AL as [AL|AL]; [eapply C0 | eapply C16]; eassumption.
Qed.
