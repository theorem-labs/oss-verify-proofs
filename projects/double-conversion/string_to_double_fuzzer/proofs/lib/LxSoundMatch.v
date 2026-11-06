(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec CatSim.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import LxLin LxState LxMem LxStep LxCheck LxSem LxWf LxSoundVal LxSoundMem LxOrder.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import LXL LXS LXM LXI LXC LXSEM LXWF LXSV LXSM.
Open Scope Z_scope.

Module LXSMT.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma concat_map_nil : forall (A B : Type) (f : A -> list B) (l : list A),
  concat (map f l) = [] -> forall x, In x l -> f x = [].
Proof.
  induction l as [|a l IH]; intros H x Hx; [destruct Hx|].
  cbn in H. apply app_eq_nil in H as [Ha Hl]. destruct Hx as [<-|Hx]; [exact Ha | exact (IH Hl x Hx)].
Qed.

Lemma if_nil : forall (A : Type) (b : bool) (m : A), (if b then [] else [m]) = [] -> b = true.
Proof. intros A [|] m H; [reflexivity | discriminate]. Qed.

Lemma forallb_In : forall (A : Type) (f : A -> bool) (l : list A) (x : A), forallb f l = true -> In x l -> f x = true.
Proof. intros A f l x H Hx. exact (proj1 (forallb_forall f l) H x Hx). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition rho_th (rho : valuation) (th : theta) : valuation :=
  fun x => match th_fun th x with Some l => evl rho l | None => rho x end.

Lemma rho_th_subst_ok : forall rho th, subst_ok (rho_th rho th) rho (th_fun th).
Proof. intros rho th x. unfold rho_th. destruct (th_fun th x); reflexivity. Qed.

(* [comment removed for export] *)
Lemma tsub_eval : forall rho th e, evl rho (tsub th e) = evl (rho_th rho th) e.
Proof. intros. unfold tsub. apply (lsubst_sound (rho_th rho th) rho). apply rho_th_subst_ok. Qed.

Lemma rho_th_glob : forall rho th x, (x < NGLOB)%nat -> rho_th rho th x = rho x.
Proof. intros rho th x Hx. unfold rho_th, th_fun. rewrite (proj2 (Nat.ltb_lt _ _) Hx). reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ent_sound : forall rho C certs g, ctx_ok rho C -> ent C certs g = true -> 0 <= evl rho g.
Proof. intros rho C certs g HC H. unfold ent in H. eapply entails_sound; [exact HC | exact H]. Qed.

Lemma ent_eq_sound : forall rho C certs a b, ctx_ok rho C -> ent_eq C certs a b = true -> evl rho a = evl rho b.
Proof.
  intros rho C certs a b HC H. unfold ent_eq in H. apply orb_prop in H as [H|H].
  - apply leqb_sound in H. subst. reflexivity.
  - apply andb_prop in H as [H1 H2].
    pose proof (ent_sound rho C certs _ HC H1) as E1. pose proof (ent_sound rho C certs _ HC H2) as E2.
    rewrite lsub_sound in E1, E2. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma match_aval_sound : forall rho C certs th t s w,
  ctx_ok rho C -> match_aval C certs th t s = true -> val_ok rho s w -> val_ok (rho_th rho th) t w.
Proof.
  intros rho C certs th t s w HC H Hs. destruct t as [|l|? ? ? ?|? ?]; cbn in H; try discriminate; [exact I|].
  destruct s as [|l'|? ? ? ?|? ?]; try discriminate. cbn in Hs |- *.
  rewrite <- tsub_eval, (ent_eq_sound rho C certs _ _ HC H). exact Hs.
Qed.

(* [comment removed for export] *)
Lemma match_aval_shape : forall C certs th t s,
  match_aval C certs th t s = true -> t = Top \/ exists l l', t = LV l /\ s = LV l' /\ ent_eq C certs (tsub th l) l' = true.
Proof.
  intros C certs th t s H. destruct t as [|l|? ? ? ?|? ?]; cbn in H; try discriminate; [left; reflexivity|].
  destruct s as [|l'|? ? ? ?|? ?]; try discriminate. right. exists l, l'. repeat split; auto.
Qed.

Lemma regs_report_get : forall C certs th tr sr k,
  regs_report C certs th tr sr k = [] -> forall i, match_aval C certs th (list_get tr i Top) (list_get sr i Top) = true.
Proof.
  intros C certs th tr. induction tr as [|t tr' IH]; intros sr k H i; [destruct i; reflexivity|].
  destruct sr as [|s sr']; [discriminate|]. cbn [regs_report] in H. apply app_eq_nil in H as [Ht H].
  apply if_nil in Ht. destruct i as [|i]; [exact Ht | exact (IH sr' (S k) H i)].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma cells_find_In : forall sc off w v,
  cells_find sc off w = Some v -> exists c, In c sc /\ c_off c = off /\ c_w c = w /\ c_val c = v.
Proof.
  induction sc as [|c r IH]; intros off w v H; [discriminate|]. cbn [cells_find] in H.
  destruct (Z.eqb (c_off c) off &&& Z.eqb (c_w c) w)%bool eqn:E.
  - injection H as <-. apply andb_prop in E as [E1 E2]. apply Z.eqb_eq in E1. apply Z.eqb_eq in E2.
    exists c. split; [left; reflexivity | repeat split; assumption].
  - destruct (IH off w v H) as (c' & Hin & X). exists c'. split; [right; exact Hin | exact X].
Qed.

Lemma cells_report_In : forall C certs th tc sc c,
  cells_report C certs th tc sc = [] -> In c tc ->
  c_val c = Top \/ exists v', cells_find sc (c_off c) (c_w c) = Some v' /\ match_aval C certs th (c_val c) v' = true.
Proof.
  intros C certs th tc sc c H Hin. unfold cells_report in H.
  pose proof (concat_map_nil _ _ _ _ H c Hin) as Hc. cbv beta in Hc.
  destruct c as [off w v]. cbn [c_val c_off c_w] in *.
  destruct v as [|l|neg k a b|a b]; [left; reflexivity | right | exfalso | exfalso].
  - destruct (cells_find sc off w) as [v'|]; [|discriminate]. exists v'. split; [reflexivity|].
    destruct (match_aval C certs th (LV l) v'); [reflexivity | discriminate].
  - cbn in Hc. destruct (cells_find sc off w); discriminate.
  - cbn in Hc. destruct (cells_find sc off w); discriminate.
Qed.

(* [comment removed for export] *)
Lemma rdn_defined : forall segs M (a : Z) k,
  0 <= a -> a + Z.of_nat k <= 2 ^ 64 ->
  (forall i, 0 <= i < Z.of_nat k -> exists b, M (Z_to_bv 64 (a + i)) = Some b) ->
  exists bs, rdn segs M (Z_to_bv 64 a) k = Some bs /\ length bs = k.
Proof.
  intros segs M a k. revert a. induction k as [|k IH]; intros a Ha Hnw Hdef.
  - exists []. split; reflexivity.
  - cbn [rdn]. destruct (Hdef 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb. rewrite Hb.
    destruct (IH (a + 1) ltac:(lia) ltac:(lia) ltac:(intros i Hi; replace (a + 1 + i) with (a + (1 + i)) by lia; apply Hdef; lia))
      as (bs & Hbs & Hlen).
    replace (Z_to_bv 64 a + 1)%bv with (Z_to_bv 64 (a + 1)).
    2:{ apply bv_eq. rewrite bv_add_unsigned, !Z_to_bv_unsigned, !bv_wrap64_mod. change (bv_wrap 64 1) with 1.
        rewrite Z.add_mod_idemp_l by lia. reflexivity. }
    rewrite Hbs. exists (b :: bs). split; [reflexivity | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bget_cases : forall b x, bget b x = itop \/ In (x, bget b x) b.
Proof.
  induction b as [|[y i] r IH]; intros x; cbn; [left; reflexivity|].
  destruct (Nat.eqb_spec x y); [subst; right; left; reflexivity|].
  destruct (IH x) as [H|H]; [left; exact H | right; right; exact H].
Qed.

Lemma facts_report_sound : forall rho C certs th T,
  ctx_ok rho C -> facts_report C certs th T = [] -> ctx_ok (rho_th rho th) T.
Proof.
  intros rho C certs th T HC H. unfold facts_report in H. apply app_eq_nil in H as [HF HB]. split.
  - apply Forall_forall. intros f Hf. pose proof (concat_map_nil _ _ _ _ HF f Hf) as X. cbv beta in X.
    apply if_nil in X. rewrite <- tsub_eval. exact (ent_sound rho C certs _ HC X).
  - intros x. destruct (bget_cases (cb T) x) as [E|Hin]; [rewrite E; apply itop_sound|].
    pose proof (concat_map_nil _ _ _ _ HB _ Hin) as X. cbv beta in X. apply app_eq_nil in X as [Xlo Xhi].
    assert (EV : evl rho (tsub th (lvar x)) = rho_th rho th x) by (rewrite tsub_eval, lvar_sound; reflexivity).
    split.
    + destruct (ilo (bget (cb T) x)) as [lo|]; [|exact I]. apply if_nil in Xlo.
      pose proof (ent_sound rho C certs _ HC Xlo) as E. rewrite laddc_sound, EV in E. lia.
    + destruct (ihi (bget (cb T) x)) as [hi|]; [|exact I]. apply if_nil in Xhi.
      pose proof (ent_sound rho C certs _ HC Xhi) as E. rewrite laddc_sound, lneg_sound, EV in E. lia.
Qed.

(* [comment removed for export] *)
Lemma itv_sub_sound : forall z a b, itv_sub a b = true -> in_itv z a -> in_itv z b.
Proof.
  intros z [al ah] [bl bh] H [Ha Hb]. unfold itv_sub in H. cbn in *. apply andb_prop in H as [H1 H2].
  split.
  - destruct bl as [lb|]; [|exact I]. destruct al as [la|]; [|discriminate]. apply Z.leb_le in H1. cbn in Ha |- *. lia.
  - destruct bh as [hb|]; [|exact I]. destruct ah as [ha|]; [|discriminate]. apply Z.leb_le in H2. cbn in Hb |- *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma bm_eqb_sound : forall a b, bm_eqb a b = true -> a = b.
Proof.
  induction a as [|[x y] a' IH]; intros [|[u v] b'] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H as [H1 H3]. apply andb_prop in H1 as [H1 H2].
  apply Z.eqb_eq in H1. apply Z.eqb_eq in H2. subst. f_equal. apply IH. exact H3.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma forallb_ent_nonneg : forall rho C certs ms,
  ctx_ok rho C -> forallb (fun c => ent C certs c) ms = true -> Forall (fun z => 0 <= z) (map (evl rho) ms).
Proof.
  intros rho C certs ms HC H. apply Forall_forall. intros z Hz. apply in_map_iff in Hz as (m & <- & Hm).
  exact (ent_sound rho C certs m HC (forallb_In _ _ _ _ H Hm)).
Qed.

Lemma lex_chk_sound : forall rho C certs cur start,
  ctx_ok rho C -> forallb (fun c => ent C certs c) cur = true -> lex_chk C certs cur start = true ->
  LXO.lex_lt (map (evl rho) cur) (map (evl rho) start).
Proof.
  intros rho C certs cur. induction cur as [|c cr IH]; intros start HC Hpos H; [destruct start; discriminate|].
  destruct start as [|s sr]; [discriminate|]. cbn [lex_chk] in H. cbn [map LXO.lex_lt].
  cbn [forallb] in Hpos. apply andb_prop in Hpos as [Hc Hcr]. pose proof (ent_sound rho C certs c HC Hc) as Pc.
  destruct (ent C certs (laddc (lsub s c) (-1))) eqn:E.
  - left. pose proof (ent_sound rho C certs _ HC E) as X. rewrite laddc_sound, lsub_sound in X.
    apply Nat.eqb_eq in H. split; [exact Pc|]. split; [lia|]. split; [rewrite !length_map; exact H|].
    exact (forallb_ent_nonneg rho C certs cr HC Hcr).
  - right. apply andb_prop in H as [H1 H2]. split; [exact Pc|]. split; [exact (ent_eq_sound rho C certs c s HC H1)|].
    exact (IH sr HC Hcr H2).
Qed.

Lemma mu_ok_sound : forall rho C certs cur start,
  ctx_ok rho C -> mu_ok C certs cur start = true -> LXO.mu_lt (map (evl rho) cur) (map (evl rho) start).
Proof.
  intros rho C certs cur start HC H. unfold mu_ok in H. apply andb_prop in H as [Hpos H]. unfold mu_lex in H.
  destruct start as [|s sr].
  - left. split; [reflexivity|]. split; [destruct cur; [discriminate | cbn; discriminate]|].
    exact (forallb_ent_nonneg rho C certs cur HC Hpos).
  - right. exact (lex_chk_sound rho C certs cur (s :: sr) HC Hpos H).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section WithU.
  Variable U : uenv.
  Variable G : sym -> Z.
  Variable M0 : word -> option byte.
  Let segs := ue_segs U.

  Lemma in_window_sound : forall off w, in_window U off w = true -> - ue_fr U <= off /\ off + w <= 0.
  Proof.
    intros off w H. unfold in_window in H. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. lia.
  Qed.

  Theorem match_sound : forall (total : bool) (S : astate) (cp : cutpoint) (mu_start : list lin) (h : arrival_hint)
                               (rho : valuation) (ms : machine_state),
    wf_state S = true -> R U G M0 rho S ms ->
    template_okb U cp = true ->
    match_report total S cp mu_start h = [] ->
    exists rhoT : valuation,
         R U G M0 rhoT (set_pc (cp_st cp) (cp_pc cp)) ms
      /\ (total = true -> LXO.mu_lt (map (evl rhoT) (cp_mu cp)) (map (evl rho) mu_start)).
  Proof.
    intros total S cp mu_start h rho ms WF HR TOK REP.
    set (T := cp_st cp) in *.
    (* [comment removed for export] *)
    unfold template_okb in TOK. fold T in TOK.
    apply andb_prop in TOK as [TOK TWF]. apply andb_prop in TOK as [TOK TMU]. apply andb_prop in TOK as [TOK TRESV]. apply andb_prop in TOK as [TOK TPC].
    apply andb_prop in TOK as [TCELLS TARRS].
    destruct (wf_parts (set_pc T (cp_pc cp)) TWF) as (Wregs & Wctx & Wstk & Warrs & Wpc & Wpay & Wdisj & W18 & Wcw & Wad).
    cbn [s_regs s_ctx s_next s_stk s_arrs s_pcache s_pay set_pc] in Wregs, Wctx, Wstk, Warrs, Wpc, Wpay, Wdisj, W18, Wcw, Wad.
    (* [comment removed for export] *)
    unfold match_report in REP. fold T in REP.
    destruct (Z.eqb_spec (s_pc S) (cp_pc cp)) as [EPC|NPC]; [|discriminate]. cbn [negb] in REP.
    set (th := infer_theta (ah_bind h) T S) in REP.
    destruct (template_closed T (cp_mu cp) th); [|discriminate]. cbn [negb] in REP.
    apply app_eq_nil in REP as [RREGS REP]. apply app_eq_nil in REP as [RCELLS REP]. apply app_eq_nil in REP as [RARRS REP].
    apply app_eq_nil in REP as [RABS REP]. apply app_eq_nil in REP as [RFACTS REP]. apply app_eq_nil in REP as [RRESV REP].
    apply app_eq_nil in REP as [RPC REP]. apply app_eq_nil in REP as [RPAY RMU].
    apply if_nil in RARRS. apply if_nil in RABS. apply if_nil in RRESV.
    destruct HR as [Rglob Rpc Rsvc Rregs [RC RCB] Rstk Rarrs Rwin Rpay Rabs Rresv Rfrm Rframe Rsp0 Ralign Rra Rdata].
    set (rhoT := rho_th rho th).
    assert (HG : forall x, (x < NGLOB)%nat -> rhoT x = rho x) by (intros x Hx; apply rho_th_glob; exact Hx).
    assert (GSP : rhoT SYM_SP0 = rho SYM_SP0) by (apply HG; unfold SYM_SP0, NGLOB; lia).
    assert (GDATA : rhoT SYM_DATA = rho SYM_DATA) by (apply HG; unfold SYM_DATA, NGLOB; lia).
    assert (GN : rhoT SYM_N = rho SYM_N) by (apply HG; unfold SYM_N, NGLOB; lia).
    assert (GRA : rhoT SYM_RA = rho SYM_RA) by (apply HG; unfold SYM_RA, NGLOB; lia).
    assert (TS : forall e, evl rho (tsub th e) = evl rhoT e) by (intros e; apply tsub_eval).
    exists rhoT. split.
    - constructor; cbn [s_pc s_regs s_ctx s_next s_stk s_arrs s_abs s_pcache s_resv s_pay set_pc].
      + (* [comment removed for export] *) intros x Hx. rewrite HG by exact Hx. apply Rglob. exact Hx.
      + (* [comment removed for export] *) rewrite Rpc, EPC. reflexivity.
      + exact Rsvc.
      + (* [comment removed for export] *) intros r Hr. eapply match_aval_sound; [exact RC | | apply Rregs; exact Hr].
        exact (regs_report_get _ _ _ _ _ _ RREGS r).
      + (* [comment removed for export] *) split; [exact (facts_report_sound rho _ _ th _ RC RFACTS) | exact Wctx].
      + (* [comment removed for export] *)
        rewrite GSP. apply Forall_forall. intros c Hc.
        pose proof (in_window_sound _ _ (forallb_In _ _ _ _ TCELLS Hc)) as [Wlo Whi].
        pose proof (forallb_In _ _ _ _ Wcw Hc) as Ww. cbv beta in Ww. apply andb_prop in Ww as [Ww0 Ww8].
        apply Z.ltb_lt in Ww0. apply Z.leb_le in Ww8.
        destruct (cells_report_In _ _ _ _ _ c RCELLS Hc) as [HTop | (v' & Hfind & Hmv)].
        * (* [comment removed for export] *)
          split; [exact Wlo|]. split; [exact Whi|]. split; [exact Ww0|].
          destruct Rwin as [Wdef _]. pose proof Rsp0 as [SP1 SP2].
          destruct (rdn_defined segs (ms_mem ms) (rho SYM_SP0 + c_off c) (Z.to_nat (c_w c))) as (bs & Hbs & Hlen).
          -- lia.
          -- rewrite Z2Nat.id by lia. lia.
          -- intros i Hi. rewrite Z2Nat.id in Hi by lia. apply Wdef. lia.
          -- exists bs. split; [exact Hbs|]. rewrite HTop. split; [rewrite Hlen, Z2Nat.id by lia; reflexivity | exact I].
        * (* [comment removed for export] *)
          destruct (cells_find_In _ _ _ _ Hfind) as (c' & Hin' & Hoff & Hw & Hval).
          pose proof (proj1 (Forall_forall _ _) Rstk c' Hin') as (A & B & Cw & bs & Hrd & Hlenb & Hvb).
          rewrite Hoff, Hw in *. split; [exact Wlo|]. split; [exact Whi|]. split; [exact Ww0|].
          exists bs. split; [exact Hrd|]. split; [exact Hlenb|].
          destruct (match_aval_shape _ _ _ _ _ Hmv) as [HT | (l & l' & Hl & Hl' & Heq)]; [rewrite HT; exact I|].
          rewrite Hl. rewrite Hval, Hl' in Hvb. cbn in Hvb |- *. rewrite <- TS, (ent_eq_sound rho _ _ _ _ RC Heq). exact Hvb.
      + (* [comment removed for export] *)
        rewrite GSP. apply Forall_forall. intros a Ha.
        unfold match_arrs in RARRS. apply andb_prop in RARRS as [RA1 _].
        pose proof (forallb_In _ _ _ _ RA1 Ha) as X. cbv beta in X. apply existsb_exists in X as (b & Hb & X).
        apply andb_prop in X as [X Hfact]. apply andb_prop in X as [Xlo Xhi]. apply Z.eqb_eq in Xlo. apply Z.eqb_eq in Xhi.
        pose proof (proj1 (Forall_forall _ _) Rarrs b Hb) as (A & B & Cf).
        split; [rewrite Xlo; exact A|]. split; [rewrite Xhi; exact B|].
        destruct (ar_fact a) as [f|] eqn:Ef; [|exact I].
        unfold match_afact in Hfact. destruct (ar_fact b) as [g|]; [|discriminate].
        apply andb_prop in Hfact as [Hfact Hfirst]. apply andb_prop in Hfact as [Hfact Hlen]. apply andb_prop in Hfact as [Hblo Hbhi].
        apply Z.eqb_eq in Hblo. apply Z.eqb_eq in Hbhi. destruct Cf as (C1 & C2 & Cf & Cfst).
        split; [rewrite Hblo; exact C1|]. split; [rewrite Hbhi; exact C2|].
        pose proof (ent_sound rho _ _ _ RC Hlen) as L. rewrite lsub_sound, TS in L.
        split; [intros j Hj; rewrite Xlo, Xhi, Hblo, Hbhi; apply Cf; lia|].
        intros H1. rewrite Xlo. destruct (itv_sub (af_first g) (af_first f)) eqn:Xsub.
        * destruct (Cfst ltac:(lia)) as (bb & Hbb & Hib). exists bb. split; [exact Hbb | exact (itv_sub_sound _ _ _ Xsub Hib)].
        * exfalso. pose proof (ent_sound rho _ _ _ RC Hfirst) as L0. rewrite lneg_sound, TS in L0. lia.
      + (* [comment removed for export] *) rewrite GSP. exact Rwin.
      + (* [comment removed for export] *)
        unfold payload_ok. rewrite GSP, GDATA, GN. destruct Rpay as (P1 & P2 & P3 & P4).
        split; [exact P1|]. split; [exact P2|]. split.
        * intros off sx x Hin. destruct (s_pcache T); [destruct Hin | discriminate].
        * intros off i Hin. unfold pay_report in RPAY.
          pose proof (concat_map_nil _ _ _ _ RPAY _ Hin) as X. cbv beta in X. apply if_nil in X. cbn [fst snd] in X.
          unfold pay_justified in X. apply orb_prop in X as [X|X].
          -- apply existsb_exists in X as ([o' i'] & Hin' & X). cbn [fst snd] in X. apply andb_prop in X as [Xeq Xsub].
             destruct (P4 o' i' Hin') as (Q1 & b & Qrd & Qitv).
             assert (E : evl rhoT off = evl rho o') by (rewrite <- TS; exact (ent_eq_sound rho _ _ _ _ RC Xeq)).
             rewrite E. split; [exact Q1|]. exists b. split; [exact Qrd | exact (itv_sub_sound _ _ _ Xsub Qitv)].
          -- apply existsb_exists in X as ([[o' sx] x] & Hin' & X).
             apply andb_prop in X as [X Xhi]. apply andb_prop in X as [X Xlo]. apply andb_prop in X as [Xsx Xeq].
             apply Z.eqb_eq in Xsx. subst sx.
             destruct (P3 o' 0 x Hin') as (Q1 & b & Qrd & Qx). cbn in Qx.
             assert (E : evl rhoT off = evl rho o') by (rewrite <- TS; exact (ent_eq_sound rho _ _ _ _ RC Xeq)).
             rewrite E. split; [exact Q1|]. exists b. split; [exact Qrd|]. split.
             ++ destruct (ilo i) as [lo|]; [|exact I]. pose proof (ent_sound rho _ _ _ RC Xlo) as L.
                rewrite laddc_sound, lvar_sound in L. lia.
             ++ destruct (ihi i) as [hi|]; [|exact I]. pose proof (ent_sound rho _ _ _ RC Xhi) as L.
                rewrite laddc_sound, lneg_sound, lvar_sound in L. lia.
      + (* [comment removed for export] *) rewrite (bm_eqb_sound _ _ RABS). exact Rabs.
      + (* [comment removed for export] *) destruct (s_resv T); [discriminate|]. destruct (s_resv S); [discriminate|].
        cbn in Rresv |- *. destruct (ms_resv ms); [destruct Rresv | exact I].
      + exact Rfrm.
      + rewrite GSP. exact Rframe.
      + rewrite GSP. exact Rsp0.
      + rewrite GSP, GDATA. exact Ralign.
      + rewrite GRA. exact Rra.
      + rewrite GDATA, GN. exact Rdata.
    - (* [comment removed for export] *)
      intros Htot. rewrite Htot in RMU. apply if_nil in RMU.
      replace (map (evl rhoT) (cp_mu cp)) with (map (evl rho) (map (tsub th) (cp_mu cp))).
      2:{ rewrite map_map. apply map_ext_in. intros m _. apply TS. }
      exact (mu_ok_sound rho _ _ _ _ RC RMU).
  Qed.
End WithU.

End LXSMT.
