(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg MmapSim.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_AKit V_Stgw7 V_Vsb V_World V_Ma6xg V_Lad4x V_Img0 V_Vct V_Co10c V_Paq9r V_PKit Img0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk Require AllocSpec LayoutP0.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require V_AKit.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.AllocSpec OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Zk.LayoutP0 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.V_AKit.Allovwl.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)
Open Scope bv_scope.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AllocSpec LayoutP0}.
  Hypothesis HMC : vep_mark_common_stmt.

  Definition after_mark (x : pst) (p' : Z) (v1 : vep) (vv1 : vsb_rec) : pst :=
    PST p' (x_st x) v1 (x_tag x) (x_q x) vv1 (x_va x) (x_vi x).

  Lemma mark_call_x : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ps p' mark ret : Z)
      (s4v t0 t1 t2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md ->
    x_p x <= p' -> p' <= pe_e E -> bool01 mark -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (x_st x = S_Attr \/ x_st x = S_Match -> p' = x_p x) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m2 : mem) (md1 : Model)
            (v1 : vep) (vv1 : vsb_rec) (x1 : pst),
        x1 = after_mark x p' v1 vv1 ->
        pinv E x1 A1 m2 -> ainv A1 m2 md1 -> md_frame md md1 ->
        hstep E x x1 A A1 m m2 ->
        vkeep (x_v x) v1 MARK_FIELDS -> v1 Fver_p = p' -> v1 Flast_mark = mark -> v1 Fo_pending = 0 ->
        0 <= v1 Fcrc < 2^64 -> 0 <= v1 Fcrcp < 2^64 ->
        realizes rsegs (mkCfg (loop_msx E ret ps s4v (Z_to_bv 64 ret) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6' m2) md1) T) ->
    realizes rsegs (mkCfg (loop_msx E vep_mark_common_entry ps s4v (Z_to_bv 64 ret) t0 t1 t2
                             (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p') (Z_to_bv 64 mark) a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV LEP PLE' BM RR RET SAME K.
    pose proof PI as PI0.
    world_open PE PI AINV.
    assert (OUT' : vb_len (x_vv x) + oacost x + oicost x <= 3 * x_v x Fo_last + 4 * (x_p x - pe_DATA E)).
    { revert OUT OA0 OI0; clear; destruct (x_st x); cbv beta iota; intros; lia. }
    (* [comment removed for export] *)
    (first [ pose proof ((pinv_sizes _ _ _ _ PI0)) as dR_s; dand4 dR_s as OUT7 WBB LEN0 SZ0 | pose proof (pinv_sizes _ _ _ _ PI0) as (OUT7 & WBB & LEN0 & SZ0) ]).
    pose proof (vsb_extendsize_tight (vb_size (x_vv x) + 9)) as EXT.
    pose proof (pw_nlive_range (x_va x) (x_vi x)) as WNL.
    eapply (HMC (pe_VEP E) (x_v x) (x_tag x) (x_q x) (x_vv x) (pe_H E)
                p' mark (x_v x Fver_p - pe_DATA E) (pslice E (x_v x Fver_p) p') (pe_lo E));
      [ exact AINV | exact MI | reflexivity | reflexivity | reflexivity | exact BM
      | split; [exact LVEP|]; split; [unfold vep_cells; rewrite STATE; exact VEPC|]; split; [exact TAG| exact PADS]
      | exact BASE | exact HENV | exact HG | exact IMG
      | exact B_lm | exact CNT | lia | unfold NMAX, pe_e, pe_N in *; lia
      | rewrite VSBF; exact VSBO | rewrite VSBF; exact D_VS | exact D_VB
      | revert ROOM OUT' OA0 OI0 CNT VERP PLE NN DLEN LEP PLE'; unfold EXT_MAX, pe_e, pe_N, vep_cnt; clear; intros; lia
      | revert LB BUDL WBB EXT ROOM OUT7 OA0 OI0 NN LEN0 SZ0; unfold PARSE_LIVE, pe_N; clear; intros; lia
      | revert NL BUDN WNL; unfold PARSE_NLIVE; clear; intros; lia
      | apply pslice_bytes; [exact DBY| lia| lia| exact PLE']
      | apply pslice_length; [lia| lia| exact PLE']
      | lia
      | unfold pe_e, pe_N in *; lia
      | right; exists (pe_DATA E), (pe_N E); split; [exact LDATA|]; unfold pe_e, pe_N in *;
        split; [lia|]; split; [lia|]; split; [lia|]; split; [exact NE3|]; split; [rewrite VSBF; exact NE4| exact (not_eq_sym D_BD)]
      | reflexivity
      | rewrite unsigned_lit by lia; rewrite PSP; rewrite Zminus_mod, G1; reflexivity
      | rewrite unsigned_lit by lia; exact RET
      | rewrite unsigned_lit by lia; exact STK
      | exact CEIL
      | rewrite unsigned_lit by lia; stk_lia
      | rewrite unsigned_lit by lia; lia
      | ].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' A1 m2 md1 v1 vv1
           AINV' MI' MDF ST' VO1 VK VERP1 LM1 OP1 CNT1 CRC1 CRCP1 VSO1 LEN1 SZ1 REL LIVE1 LB1 NL1 HENV1 DBY1 CF1.
    rewrite unsigned_lit in ST', CF1 by lia. rewrite VSBF in VSO1, CF1.
    assert (CV1 : vcover (pe_H E) A [pe_DATA E; x_v x Fattr_vsb; oabuf x; x_v x Finclude_src; oibuf x]
                         (fun a => blk (pe_VEP E) 312 a \/ blk (vb_buf (x_vv x)) (vb_size (x_vv x)) a \/ (pe_S E <= a < pe_S E + 40))).
    { intros a [Ha|[Ha|Ha]].
      - eapply cover_blk; [exact LVEP| wz_not_in| exact Ha].
      - eapply cover_blk; [exact LVB| wz_not_in| exact Ha].
      - eapply cover_rng; [exact LVS| wz_not_in| exact Ha]. }
    assert (WIN : alloc_ceiling <= pe_sp E - MARK_STACK) by (stk_lia).
    assert (FR2 : rw_cells rsegs m2 (pe_sp E) (pframe E j0 j8)).
    { eapply (pframe_call E A A1 m m2 md); [exact PE| exact AINV| exact CF1| exact WIN| stk_lia| lia| exact CV1| unfold pframe; exact FR]. }
    assert (LDATA1 : a_live A1 (pe_DATA E) = Some (Z.of_nat (length (pe_inp E)))).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact LDATA| exact (not_eq_sym D_BD)]. }
    assert (DBY2 : bytes_at rsegs m2 (pe_DATA E) (pe_inp E)).
    { refine (proj1 (proj2 (data_obj_call (pe_H E) A A1 m m2 md _ _ _ _ _ AINV CF1 HG WIN (pe_DATA E) (pe_inp E) CV1 _ LDATA1 DATA))). in_list. }
    assert (WAL1 : a_live A1 (pe_wa E) = Some 40).
    { eapply (live_keep _ _ _ _ _ _ LIVE1 REL); [exact WAL| exact D_WB]. }
    assert (NB_V : pe_VEP E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LVEP| exact D_VB]).
    assert (NB_W : pe_wa E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact WAL| exact D_WB]).
    assert (NB_D : pe_DATA E <> vb_buf vv1) by (eapply (fresh_ne _ _ _ _ _ _ REL); [exact LDATA| exact (not_eq_sym D_BD)]).
    assert (VA2 : va_world E x A1 m2) by (unfold va_world; world_call VA CV1 CF1 AINV LIVE1 REL D_AB D_ABB).
    assert (VI2 : vi_world E x A1 m2) by (unfold vi_world; world_call VI CV1 CF1 AINV LIVE1 REL D_IB D_IBB).
    assert (PI1 : pinv E (after_mark x p' v1 vv1) A1 m2).
    { unfold after_mark. apply Build_pinv; psimp; vk_norm VK; psimp; try pinv_triv.
      - unfold vep_base. vk_norm VK. exact BASE.
      - rewrite VERP1. replace (p' - pe_DATA E) with (x_v x Fver_p - pe_DATA E + (p' - x_v x Fver_p)) by lia. exact CNT1.
      - rewrite VERP1. lia.
      - rewrite LM1. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; first [assumption | exact BM].
      - split; [exact DELIM1| exact DELIM2].
      - intros X Y Z. rewrite (SAME (or_introl X)) in Z |- *. unfold look in LOOKA |- *. cbn [x_p]. exact (LOOKA X Y Z).
      - intros X Y Z. rewrite (SAME (or_intror X)) in Z |- *. unfold look in LOOKM |- *. cbn [x_p]. exact (LOOKM X Y Z).
      - lia.
      - revert OUT LEN1 LEP. clear. cbv [oacost oicost x_va x_vi]. destruct (x_st x); cbv [x_st]; intros; lia.
      - intros y Hy. split; [apply (proj1 (APART y Hy))|].
        cbn in Hy. destruct Hy as [<-|[<-|[<-|[]]]]; apply not_eq_sym; [exact NB_V| exact NB_W| exact NB_D].
      - (* [comment removed for export] *)
        clear - VA VA2 REL. unfold va_world in VA2. destruct (x_va x) as [ya|]; [|exact VA2].
        (first [ dand4 VA2 as Q1 Q2 Q3 Q4 | destruct VA2 as (Q1 & Q2 & Q3 & Q4) ]). (first [ dand4 VA as _ (_ & _ & LA1 & LA2 & _) _ AAP | destruct VA as (_ & (_ & _ & LA1 & LA2 & _) & _ & AAP) ]).
        refine (conj Q1 (conj Q2 (conj Q3 _))).
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply Q4; cbn; auto 10.
        destruct (AAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
        split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LA1| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LA2| exact N2]].
      - clear - VI VI2 REL. unfold vi_world in VI2. destruct (x_vi x) as [yi|]; [|exact VI2].
        (first [ dand6 VI2 as Q1 Q2 Q3 Q3b Q4 Q5 | destruct VI2 as (Q1 & Q2 & Q3 & Q3b & Q4 & Q5) ]). (first [ dand6 VI as _ (_ & _ & LI1 & LI2 & _) _ _ IAP _ | destruct VI as (_ & (_ & _ & LI1 & LI2 & _) & _ & _ & IAP & _) ]).
        refine (conj Q1 (conj Q2 (conj Q3 (conj Q3b (conj _ Q5))))).
        intros y Hy. cbn in Hy. destruct Hy as [<-|[<-|[<-|[<-|[<-|[]]]]]].
        1-4: apply Q4; cbn; auto 10.
        destruct (IAP (vb_buf (x_vv x)) ltac:(cbn; auto 10)) as [N1 N2].
        split; [eapply (fresh_ne _ _ _ _ _ _ REL); [exact LI1| exact N1] | eapply (fresh_ne _ _ _ _ _ _ REL); [exact LI2| exact N2]].
      - split; [exact LDATA1| split; [exact DBY2| exact DLEN]].
      - eapply (img_call (pe_H E) A A1 m m2 md); [exact AINV| exact CF1| exact HG| exact WIN| exact CV1| exact IMG].
      - exists j0, j8. exact FR2.
      - (* [comment removed for export] *) rewrite LB1, LB. unfold pw_bytes. clear. lia.
      - (* [comment removed for export] *) rewrite NL1. exact NL. }
    (* [comment removed for export] *)
    assert (HS : hstep E x (after_mark x p' v1 vv1) A A1 m m2).
    { eapply (hstep_call1 E x _ A A1 m m2 MARK_STACK _ (vb_buf (x_vv x)) (vb_size vv1) (vb_buf vv1));
        [ exact CF1
        | stk_lia
        | eapply parse_window_mapped; [exact PE| exact ST'| exact FR2]
        | intros a [Ha|[Ha|Ha]]; unfold pzone; [left; exact Ha| right; right; left; exact Ha| right; left; exact Ha]
        | exact LIVE1 | exact REL
        | unfold pst_blocks; left; reflexivity
        | unfold pst_blocks, after_mark; cbn [x_vv x_va x_vi x_v]; intros p Hp; vk_norm_in VK Hp;
          destruct Hp as [Hp|Hp]; [right; exact Hp| left; right; exact Hp]
        | unfold parse_new, after_mark, pzone; cbn [x_vv x_va x_vi x_v option_map]; intros a Ha; vk_norm_in VK Ha;
          destruct Ha as [Ha|[Ha|Ha]]; [left; exact Ha| right; right; right; right; left| right; right; right; right; right; left];
          [destruct (x_va x); [exact Ha| destruct Ha] | destruct (x_vi x); [exact Ha| destruct Ha]] ]. }
    unfold loop_msx in K. rewrite (ret_pc_even ret RR RET).
    exact (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ A1 m2 md1 v1 vv1 _ eq_refl PI1 AINV' MDF HS VK VERP1 LM1 OP1 CRC1 CRCP1).
  Qed.

  (* [comment removed for export] *)
  Lemma mark_call : forall (E : penv) (x : pst) (A : AS) (m : mem) (md : Model) (T : TSet) (ps p' mark ret : Z)
      (t0 t1 t2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 : word),
    penv_ok E -> pinv E x A m -> ainv A m md ->
    x_p x <= p' -> p' <= pe_e E -> bool01 mark -> 0 <= ret < 2^64 -> ret mod 2 = 0 ->
    (x_st x = S_Attr \/ x_st x = S_Match -> p' = x_p x) ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (A1 : AS) (m2 : mem) (md1 : Model)
            (v1 : vep) (vv1 : vsb_rec) (x1 : pst),
        x1 = after_mark x p' v1 vv1 ->
        pinv E x1 A1 m2 -> ainv A1 m2 md1 -> md_frame md md1 ->
        hstep E x x1 A A1 m m2 ->
        vkeep (x_v x) v1 MARK_FIELDS -> v1 Fver_p = p' -> v1 Flast_mark = mark -> v1 Fo_pending = 0 ->
        0 <= v1 Fcrc < 2^64 -> 0 <= v1 Fcrcp < 2^64 ->
        realizes rsegs (mkCfg (loop_ms E ret ps (Z_to_bv 64 ret) t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s7 t3' t4' t5' t6' m2) md1) T) ->
    realizes rsegs (mkCfg (loop_ms E vep_mark_common_entry ps (Z_to_bv 64 ret) t0 t1 t2
                             (Z_to_bv 64 (pe_VEP E)) (Z_to_bv 64 p') (Z_to_bv 64 mark) a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 m) md) T.
  Proof.
    intros until t6. intros PE PI AINV LEP PLE' BM RR RET SAME K.
    apply (mark_call_x E x A m md T ps p' mark ret (Z_to_bv 64 (st0 S_BOM)) t0 t1 t2 a3 a4 a5 a6 a7 s7 t3 t4 t5 t6 PE PI AINV LEP PLE' BM RR RET SAME).
    exact K.
  Qed.
End S.
