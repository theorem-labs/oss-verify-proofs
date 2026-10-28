(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Mem Frame Cells Step Arr ImageA Exec RzCPS.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.AS Require Import AsanAcct.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Shadow R_sizeclass.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import Layout RT_iface D_defs D_kit. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_cache_defs R_prim_defs. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import R_thread R_m2s. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import R_leaves R_poison R_setshadow R_glue_defs R_sec_defs R_depot_defs R_fs_defs R_tlsgetaddr R_intalloc RT_state RT_rep RT_frame RT_trans RT_facts0 RT_sep RT_freelift RT_geo0 RT_fkit RT_freeA RT_facts RT_stackmalloc. From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A Require Import I_lkit.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.BA Require Import RT_iface2 RT_anndefs RT_livefresh R_annotate RT_annart RT_annlive TopA_iodefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

Import ListNotations.
Open Scope Z_scope.

Section GWIN. Context {GWc : OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.A.Shadow.GW}.
Lemma live_rng_ok : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> ann_rng_ok p n.
Proof.
  intros Σ m p n HA HIN. pose proof (geo_of_ART Σ m HA) as HG. pose proof (fk_aceil Σ HG) as (X1 & X2). pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  unfold ann_rng_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd.
  destruct (geo_live Σ m HA p n HIN) as [(c & i & Hc & Hn & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y5)].
  - pose proof (g_grant Σ HG (l_PRB (lay Σ)) 0x2000011000 ltac:(unfold startup_grants; left; reflexivity)) as (G1 & G2 & G3 & G4 & G5).
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc; lia).
    right. unfold rb, kUserCap, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. clear - G1 G3 G4 H Y1 Y2 Y3 Y4 P3 P4 X2 Hc. lia.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (map_geo Σ m HA k s Hk) as (Hsn1 & (G1 & G2 & G3 & G4 & G5) & _ & _ & Hroom).
    rewrite Hsn in *. unfold s_ubeg, K_LOW_SHADOW_lo, K_HIGH_SHADOW_hi in *. clear - G1 G3 G4 Ep Y1 X2. lia.
Qed.

Lemma live_shadow_stk : forall Σ m p n, ART_A Σ m -> In (p, n) (live Σ) -> n mod 8 = 0 -> stk asegs m (shad p) (shad p + n / 8).
Proof.
  intros Σ m p n HA HIN N8. pose proof (geo_of_ART Σ m HA) as HG. pose proof (fk_prb Σ HG) as (P0 & P1 & P2 & P3 & P4).
  pose proof (rta_live_block Σ m HA p n HIN) as (P8 & _). pose proof (shad_aligned_add p n P8 ltac:(pose proof (rta_live_size Σ m HA p n HIN); lia)) as E.
  destruct (geo_live Σ m HA p n HIN) as [(c & i & Hc & Hn & Ep & Y1 & Y2 & Y3 & Y4 & Y5)|(s & Hs & Hq & Hsn & Ep & Y1 & Y5)].
  - pose proof (ART_prim Σ m HA c Hc) as (_ & _ & _ & _ & _ & _ & ST).
    assert (c * 2 ^ 32 + 2 ^ 32 <= 2 ^ 37) by (clear - Hc; lia).
    pose proof (fk_shad_mono (rb (l_SB (lay Σ)) c) p ltac:(lia)) as M1.
    pose proof (fk_shad_mono (p + n) (rb (l_SB (lay Σ)) c + 2 ^ 32) ltac:(unfold rb, kUserCap in *; clear - Y2 Y3 Y4 H; lia)) as M2.
    destruct (stk_split asegs m _ (shad p) _ ST ltac:(lia)) as [_ ST1]. destruct (stk_split asegs m _ (shad p + n / 8) _ ST1 ltac:(lia)) as [ST2 _]. exact ST2.
  - destruct (In_nth_error _ _ Hs) as (k & Hk). pose proof (ART_chunk Σ m HA) as [_ SC]. pose proof (SC k s Hk) as (_ & _ & _ & _ & ST & _).
    pose proof (map_geo Σ m HA k s Hk) as (Hsn1 & _ & _ & _ & Hroom). rewrite Hsn in *.
    pose proof (fk_shad_mono (s_mb s) p ltac:(unfold s_ubeg in *; lia)) as M1.
    pose proof (fk_shad_mono (p + n) (s_mb s + smsz n) ltac:(unfold s_ubeg in *; lia)) as M2.
    destruct (stk_split asegs m _ (shad p) _ ST ltac:(lia)) as [_ ST1]. destruct (stk_split asegs m _ (shad p + n / 8) _ ST1 ltac:(lia)) as [ST2 _]. exact ST2.
Qed.

Lemma rta_ann_cells : forall Σ m, ART_A Σ m -> ann_cells m /\ ps_cells m.
Proof.
  intros Σ m HA. pose proof (ART_consts Σ m HA) as (_ & _ & _ & _ & PS & _ & _ & IC). split; [|exact PS].
  pose proof IC as IC2. do 22 (apply proj2 in IC2). apply proj1 in IC2.
  unfold icells_rep in IC. repeat (lazymatch type of IC with _ /\ (_ /\ (_ /\ _)) => apply proj2 in IC end). apply proj1 in IC.
  pose proof (ART_fs Σ m HA) as (_ & _ & _ & _ & _ & _ & (dtvbeg & _ & TGA) & _). destruct TGA as (_ & _ & _ & _ & (_ & _ & GV & CV & _)).
  unfold ann_cells, g_got_flags, g_flags, g_detect_container_overflow. split; [exact IC2|]. split; [|split; [exact GV | exact CV]].
  apply (proj1 (Forall_forall _ _) IC (0x171498, [C1 (Z_to_bv 8 1)])). unfold io_ro. cbn [In]. tauto.
Qed.

Lemma rta_ASTA_mat_stable' : forall Σ PMc, mat_stable PMc -> mat_stable (fun mo => ARTM RTA Σ mo /\ PMc mo).
Proof. intros Σ PMc H. apply mat_stable_and; [exact (rta_mat_stable Σ) | exact H]. Qed.

Theorem rta_annotate : annotate_contract RTA.
Proof.
  intros Σ PMc ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n v v' l1 l2 lo
    FDO MST LV L1P -> -> -> -> Hv Hv' V8 V8' N16 Hn ART0 MI0 CALL.
  intros T cf Hc Hk. cbn [ART rt_frames rt_live rt_sp0 rt_credit RTA] in *. unfold rtA_frames, rtA_live, rtA_sp0, rtA_credit in *.
  destruct CALL as (ST & LOW & LOR & SPT & SPA).
  set (usp := bv_unsigned sp) in *.
  assert (ESP : sp = Z_to_bv 64 usp) by (symmetry; apply Z_to_bv_bv_unsigned).
  assert (N8 : n mod 8 = 0) by (pose proof (Z.div_mod n 16 ltac:(lia)); lia).
  pose proof (geo_of_ART Σ m ART0) as HG. pose proof (fk_aceil Σ HG) as (X1 & X2). pose proof (g_aceil Σ HG) as (_ & _ & X3).
  unfold l_ACEIL, RT_STACK, STACK_WIN, USTACK_TOP in *.

  pose proof (rta_live_nodup_real Σ m ART0) as ND.
  destruct (vis_live_block (ann Σ) (live Σ) p n v l1 l2 ND (rta_live_size Σ m ART0) LV
              ltac:(intros e He; exact (proj1 (Forall_forall _ _) L1P e He)) ltac:(lia) ltac:(lia) N16) as (L1 & L2 & EL & EV1 & EV2 & CUR).
  assert (HIN : In (p, n) (live Σ)) by (rewrite EL; apply in_app_iff; right; left; reflexivity).
  pose proof (rta_live_block Σ m ART0 p n HIN) as (P8 & _ & _ & OLD & PCE). rewrite (ushadowA_cur p n v (ann Σ) CUR ltac:(lia) N16) in OLD.
  pose proof (ru8_id n N8) as RU. unfold l_ACEIL, STACK_WIN in PCE.
  destruct (rta_ann_cells Σ m ART0) as (AC & PS).
  pose proof (live_rng_ok Σ m p n ART0 HIN) as HR.
  assert (P0 : 0 <= p) by (clear - HR; unfold ann_rng_ok, kLowMemEnd, kHighShadowEnd, kHighMemEnd in HR; lia).

  set (lo' := Z.min v v') in *. set (len := Z.max v v' - Z.min v v') in *.
  assert (HL : 0 <= lo' /\ lo' + len <= n /\ 0 <= len /\ lo' mod 8 = 0 /\ len mod 8 = 0).
  { subst lo' len. destruct (Z_lt_le_dec v v'); [rewrite (Z.min_l v v'), (Z.max_r v v') by lia | rewrite (Z.min_r v v'), (Z.max_l v v') by lia]; repeat split; lia. }
  destruct HL as (HL0 & HL1 & HL2 & HL8 & HL8').
  cbn [rt_sp0 RTA] in LOW. unfold rtA_sp0 in LOW.
  pose proof (shad_aligned_add p lo' P8 HL0) as SH1.
  pose proof (shad_hi (p + n) ltac:(lia)) as SHN. pose proof (shad_aligned_add p n P8 ltac:(lia)) as SH3.

  assert (SHX : exists shj, v <> v' -> rw_cells asegs m (shad (p + lo')) [CB (Z.to_nat (len / 8)) shj]).
  { destruct (Z.eq_dec v v') as [E|NE]; [exists []; intros X; exfalso; exact (X E)|].
    pose proof (live_shadow_stk Σ m p n ART0 HIN N8) as SS.
    destruct (stk_split asegs m _ (shad (p + lo')) _ SS ltac:(rewrite SH1; lia)) as [_ SS1].
    destruct (stk_split asegs m _ (shad (p + lo') + len / 8) _ SS1 ltac:(rewrite SH1; lia)) as [SS2 _].
    destruct (stk_carve asegs m _ _ (Z.to_nat (len / 8)) SS2 ltac:(lia)) as [_ (shj & FR)].
    exists shj. intros _. replace (shad (p + lo') + len / 8 - Z.of_nat (Z.to_nat (len / 8))) with (shad (p + lo')) in FR by lia. exact FR. }
  destruct SHX as (shj & SH).

  assert (W1 : evt asegs (annotate_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (p + lo') len (if v <? v' then 0 else 252) lo m)
                 (entry_st ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 p) (Z_to_bv 64 (p + n)) (Z_to_bv 64 (p + v)) (Z_to_bv 64 (p + v')) a4 a5 a6 a7
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc e_annotate m)).
  { unfold entry_st, e_annotate.
    exact (annotate_spec ra sp gp tp t0 t1 t2 s0 s1 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m p n v v' lo shj
             Hv Hv' V8 V8' P8 N8 ltac:(lia) HR SH AC PS ST ltac:(lia) ltac:(unfold kHighShadowEnd; lia) MI0). }
  lazymatch type of W1 with evt asegs _ ?X =>
    assert (W1' : forall ms, eq X ms -> evt asegs _ ms) by (intros ms <-; exact W1) end.
  clear W1.
  apply (cps_realizes asegs _ _ _ cf (ast_evt asegs SEGTOP_A asegs_wx asegs_below (rtA_allow Σ) _ _ _ (rta_ASTA_mat_stable' Σ PMc MST) W1') Hc).
  intros c1 Hc1. apply Hk. unfold annotate_post in Hc1.
  apply AST_exI in Hc1 as (t0' & Hc1). apply AST_exI in Hc1 as (t1' & Hc1). apply AST_exI in Hc1 as (t2' & Hc1). apply AST_exI in Hc1 as (a0' & Hc1).
  set (A' := (p, n, v') :: arem p (ann Σ)).
  assert (ALK : forall q k, q <> p -> alook q k A' = alook q k (ann Σ)).
  { intros q k Hq. subst A'. rewrite (alook_cons_other q k p n v' _ Hq). exact (alook_arem_other q p k (ann Σ) Hq). }

  assert (SUB : sub_fp [(shad (p + lo'), shad (p + lo') + len / 8); (usp - 2192, usp)] (W_ann (p + lo') len (l_sp0 (lay Σ) - 8388608) usp)).
  { intros x Hx. unfold W_ann in Hx. cbn [outside fst snd] in Hx |- *. destruct Hx as (Hx1 & Hx2 & _). split; [exact Hx1|]. split; [lia | exact I]. }
  assert (SUB2 : sub_fp [(shad (p + lo'), shad (p + lo') + len / 8); (usp - 2192, usp)] ((shad p + lo' / 8, shad p + lo' / 8 + len / 8) :: [(usp - 2192, usp)])).
  { intros x Hx. cbn [outside fst snd] in Hx |- *. rewrite SH1. exact Hx. }
  exists (set_ann Σ A'), a0'. split.
  - unfold ASTA in *. eapply AST_conseq; [exact Hc1 | | intros mo [H1 H2]; split; [exact H1 | exact H2]].
    intros ms (a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' & -> & MU & WM & MI & PC & ST').
    pose proof (munch_weaken _ _ m m' SUB MU) as MU'.
    exists m'. split; [unfold ret_stF; do 15 eexists; reflexivity|].
    assert (NEW : bytes_at asegs m' (shad p) (ushadowA (alook p n A') n)).
    { subst A'. rewrite (ushadowA_upd p n v' (ann Σ) ltac:(lia) V8' N16).
      destruct (Z.eq_dec v v') as [<-|NE].
      *
        assert (SUB0 : sub_fp [(shad (p + lo'), shad (p + lo') + len / 8); (usp - 2192, usp)] [(usp - 2192, usp)]).
        { intros x Hx. cbn [outside fst snd] in Hx |- *. split; [subst lo' len; rewrite Z.min_id, Z.max_id; lia | exact Hx]. }
        apply (bytes_at_transport asegs _ m m' _ _ OLD (munch_weaken _ _ m m' SUB0 MU)).
        rewrite (annsh_len n v ltac:(lia) V8 N8). cbn [disjoint_from fst snd]. split; [left; lia | exact I].
      * pose proof (munch_weaken _ _ m m' SUB2 MU) as MU2.
        destruct (PC ltac:(lia)) as [[_ DB] _]. cbn [cells_bytes cbytes] in DB. rewrite app_nil_r, SH1 in DB.
        apply (reshadow m m' [(usp - 2192, usp)] (shad p) n v v' ltac:(pose proof (shad_lo p P0); unfold SHB in *; lia) Hv Hv' NE V8 V8' N8 OLD MU2).
        -- cbn [disjoint_from fst snd]. split; [left; lia | exact I].
        -- exact DB. }
    destruct (ann_ART_live Σ m m' p n lo' len usp A' ART0 HIN ltac:(lia) N16 HL0 HL1 HL2 HL8 HL8' ltac:(unfold l_ACEIL, USTACK_TOP, STACK_WIN; lia) MU' WM ALK NEW)
      as [ART' CL].
    split.
    + split; [exact ART' | split; [exact MI | split; [exact WM | exact ST']]].
    +
      intros x Hx. apply MU'. apply CL. exact (aclient_vis _ _ _ _ _ Hx).
  - cbn [lay live frames credit ann set_ann]. split; [| split; [reflexivity | split; reflexivity]].
    subst A'. rewrite (vis_live_update (ann Σ) (live Σ) p n v' L1 L2 ND EL ltac:(lia) V8' N16), EV1, EV2. reflexivity.
Qed.

End GWIN.
