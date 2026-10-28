(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp.bitvector Require Import definitions.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.jsoncons.fuzz_json_encoder.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib Require Import PropExec CatExec CatSim StoreOk Hoare ShapeAlg SpinAlg HeapIface L5Defs L5Core. From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5 Require Import PmLibDefs_u5 PmLibSpecs_u5 PmEncSpecs_u5 PmLibSpecsX_u5
  PmLibSpecsW_u5 PmRef_u5 PmRefFacts_u5 PmRefFacts2_u5 PmRefRead_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTop Require Import TopSpecs_u5.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_json_encoder.lib.U5.PmTopW Require Import TopSpecsW_u5.
Import ListNotations. Import PML.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module RKW.
Import PMR. Import PMRR.
(* [comment removed for export] *)
Local Strategy expand [TPSW.chunk_of TPSW.rest_of TPSW.chunk_w].

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma skipn_firstn_len : forall {A} C (r : list A), skipn (length (firstn C r)) r = skipn C r.
Proof.
  intros A C r. destruct (Nat.le_gt_cases C (length r)) as [L|L].
  - rewrite length_firstn, Nat.min_l by lia. reflexivity.
  - rewrite firstn_all2 by lia. rewrite skipn_all. symmetry. apply skipn_all2. lia.
Qed.
Lemma length_firstn_min : forall {A} C (r : list A), length (firstn C r) = Nat.min C (length r).
Proof. intros A C r. apply length_firstn. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma wwz_nil : forall c rest bof eof, wwz (RS c [] rest bof eof) = 0. Proof. reflexivity. Qed.
Lemma wwz_cons : forall c b r rest bof eof, wwz (RS c (b :: r) rest bof eof) = 1. Proof. reflexivity. Qed.
Lemma nchunks_rs : forall c c' w w' rest bof bof' eof, nchunks (RS c w rest bof eof) = nchunks (RS c' w' rest bof' eof). Proof. reflexivity. Qed.
Lemma nchunks_eof : forall c w rest bof, nchunks (RS c w rest bof true) = 0. Proof. reflexivity. Qed.
Lemma wwz_range : forall rs, 0 <= wwz rs <= 1. Proof. intros rs. unfold wwz. destruct (r_w rs); lia. Qed.
Lemma wwz_pos : forall rs, r_w rs <> [] -> wwz rs = 1. Proof. intros rs H. unfold wwz. destruct (r_w rs); [exfalso; exact (H eq_refl) | reflexivity]. Qed.
Lemma RB_more : forall c w rest bof eof, c_more c = true ->
  RB (RS c w rest bof eof) = (if (wwz (RS c w rest bof eof) =? 0) && (nchunks (RS c w rest bof eof) =? 0) then 2 + rankz c
                              else wwz (RS c w rest bof eof) + nchunks (RS c w rest bof eof) + 3).
Proof. intros c w rest bof eof H. unfold RB. cbn [r_c]. rewrite H. reflexivity. Qed.
Lemma rankz_range : forall c, 0 <= rankz c <= 1. Proof. intros c; unfold rankz; destruct (_ || _); lia. Qed.
Lemma RB_arith : forall A B wz rq rc,
  0 <= A -> 0 <= B -> 0 <= rq <= 1 -> 0 <= rc <= 1 -> (wz = 0 \/ wz = 1) ->
  (wz = 1 -> A = B) ->
  (wz = 0 -> (A <= B - 1 /\ 1 <= B) \/ (A = B /\ B = 0 /\ rc = 1 /\ rq = 0)) ->
  (if (0 =? 0) && (A =? 0) then 2 + rq else 0 + A + 3) <= (if (wz =? 0) && (B =? 0) then 2 + rc else wz + B + 3) - 1.
Proof.
  intros A B wz rq rc HA HB HQ HC HW H1 H0. cbn [Z.eqb andb].
  destruct (Z.eqb_spec A 0); destruct (Z.eqb_spec wz 0); cbn [andb]; try destruct (Z.eqb_spec B 0); lia.
Qed.
Lemma RB_cont : forall rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) ->
  (r_w rs = [] -> r_eof rs = false -> nchunks rs1 <= nchunks rs - 1 /\ 1 <= nchunks rs) ->
  ((r_w rs <> [] \/ r_eof rs = true) -> rs1 = rs) ->
  0 <= nchunks rs1 ->
  q_w q = [] -> c_more (q_c q) = true ->
  (r_w rs = [] -> r_eof rs = true -> rankz (r_c rs) = 1 /\ rankz (q_c q) = 0) ->
  RB (rs_after q rs1) <= RB rs - 1.
Proof.
  intros [c w rest bof eof] [c1 w1 rest1 bof1 eof1] q. cbn [r_c r_w r_rest r_eof]. intros Hm Hr RD NRD N1 Hw Hm' RK.
  pose proof (rankz_range c) as R0. pose proof (rankz_range (q_c q)) as R1. pose proof (nchunks_nonneg (RS c w rest bof eof)) as N0.
  unfold rs_after. cbn [r_rest r_bof r_eof]. rewrite Hw. rewrite (RB_more (q_c q)) by exact Hm'. rewrite (RB_more c) by exact Hm.
  rewrite wwz_nil. rewrite (nchunks_rs (q_c q) c1 [] w1 rest1 bof1 bof1 eof1).
  apply RB_arith; [exact N1 | exact N0 | exact R1 | exact R0 | destruct w; [left|right]; reflexivity | |].
  - intros H1. destruct w as [|b r]; [discriminate H1|]. assert (E : RS c1 w1 rest1 bof1 eof1 = RS c (b :: r) rest bof eof) by (apply NRD; left; intros X; discriminate X).
    injection E as -> -> -> -> ->. reflexivity.
  - intros H0. destruct w as [|b r]; [|discriminate H0]. destruct eof.
    + right. assert (E : RS c1 w1 rest1 bof1 eof1 = RS c [] rest bof true) by (apply NRD; right; reflexivity).
      injection E as -> -> -> -> ->. destruct (RK eq_refl eq_refl) as [X1 X2]. rewrite X1, X2. rewrite nchunks_eof. repeat split; reflexivity.
    + left. exact (RD eq_refl eq_refl).
Qed.
Lemma refill_same : forall rs, (r_w rs <> [] \/ r_eof rs = true) -> refill rs = (rs, 0).
Proof.
  intros rs [H|H]; [|apply refill_eof; exact H]. destruct (r_w rs) as [|b r] eqn:Hw; [exfalso; exact (H eq_refl)|]. exact (refill_full rs b r Hw).
Qed.
Lemma refill_nchunks : forall rs rs1 cd, r_w rs = [] -> r_eof rs = false -> refill rs = (rs1, cd) -> nchunks rs1 <= nchunks rs - 1 /\ 1 <= nchunks rs.
Proof.
  intros [c w rest bof eof] rs1 cd Hw He Hr. cbn [r_w r_eof] in Hw, He. subst w eof. rewrite refill_read in Hr. cbv zeta in Hr.
  remember (firstn (Z.to_nat CHUNK) rest) as s eqn:Hs.
  assert (LS : Z.of_nat (length s) = Z.min CHUNK (Z.of_nat (length rest))) by (rewrite Hs; apply length_firstn_Z; unfold CHUNK; lia).
  destruct (chunkw s bof) as [[j cd'] b']. injection Hr as <- _.
  unfold nchunks. cbn [r_eof r_rest]. rewrite length_skipn.
  pose proof (Z.div_pos (Z.of_nat (length rest)) CHUNK ltac:(lia) ltac:(unfold CHUNK; lia)) as P0.
  destruct (Nat.ltb_spec (length s) (Z.to_nat CHUNK)) as [X|X]; [split; lia|].
  assert (FULL : Z.of_nat (length s) = CHUNK) by (clear - LS X; unfold CHUNK in *; lia).
  rewrite Nat2Z.inj_sub by (clear - FULL LS; unfold CHUNK in *; lia). change (Z.of_nat (Z.to_nat CHUNK)) with CHUNK.
  replace (Z.of_nat (length rest)) with ((Z.of_nat (length rest) - CHUNK) + 1 * CHUNK) at 2 3 by lia. rewrite Z.div_add by (unfold CHUNK; lia).
  pose proof (Z.div_pos (Z.of_nat (length rest) - CHUNK) CHUNK ltac:(clear - FULL LS; unfold CHUNK in *; lia) ltac:(unfold CHUNK; lia)). lia.
Qed.
Lemma RB_round : forall rs rs1 q, c_more (r_c rs) = true -> refill rs = (rs1, 0) ->
  q_w q = [] -> c_more (q_c q) = true ->
  (r_w rs = [] -> r_eof rs = true -> rankz (r_c rs) = 1 /\ rankz (q_c q) = 0) ->
  RB (rs_after q rs1) <= RB rs - 1.
Proof.
  intros rs rs1 q Hm Hr Hw Hm' RK. apply (RB_cont rs rs1 q Hm Hr); [| | apply nchunks_nonneg | exact Hw | exact Hm' | exact RK].
  - intros W E. exact (refill_nchunks rs rs1 0 W E Hr).
  - intros X. rewrite (refill_same rs X) in Hr. injection Hr as ->. reflexivity.
Qed.
Lemma bind_suffix : forall q k w, PMRF2.wsuf q w -> (forall c' w', PMRF2.wsuf (k c' w') w') -> PMRF2.wsuf (bind q k) w.
Proof.
  intros q k w [u Hu] Hk. unfold bind. destruct (negb (q_code q =? 0)); [exists u; exact Hu|]. cbn [q_w].
  destruct (Hk (q_c q) (q_w q)) as [v Hv]. exists (v + u)%nat. rewrite Hv, Hu. apply skipn_skipn.
Qed.
Lemma act_run_suffix : forall a c b r, PMRF2.wsuf (act_run a c b r) (b :: r).
Proof.
  intros a c b r. destruct a; try destruct consumed; try destruct consume; cbn [act_run];
  first [ apply PMRF2.wsuf_same; reflexivity
        | apply PMRF2.wsuf_tl; apply PMRF2.wsuf_same; reflexivity
        | unfold skip_space_r; destruct (PMRF2.skip_space_suffix (b :: r) c) as [u Hu]; exists u; exact Hu
        | apply PMRF2.wsuf_tl; apply PMRF2.wsuf_same; apply PMRF2.begin_container_w
        | apply PMRF2.wsuf_tl; apply PMRF2.wsuf_same; apply PMRF2.end_container_w
        | unfold start_string; apply PMRF2.wsuf_tl; apply PMRF2.parse_string_suffix
        | unfold start_number; apply PMRF2.wsuf_tl; apply PMRF2.parse_number_suffix
        | unfold parse_null, parse_true, parse_false; destruct (which =? 0); [apply PMRF2.parse_lit_suffix|]; destruct (which =? 1); apply PMRF2.parse_lit_suffix
        | unfold bind; destruct (negb _); [apply PMRF2.wsuf_same; apply PMRF2.begin_member_w | cbn [q_w]; apply PMRF2.wsuf_tl; apply PMRF2.wsuf_same; reflexivity]
        | unfold lit_done; apply PMRF2.wsuf_tl; apply PMRF2.wsuf_same; reflexivity
        | apply PMRF2.parse_string_suffix
        | apply PMRF2.parse_number_suffix ].
Qed.
Lemma loop_suffix : forall F c w, PMRF2.wsuf (loop F c w) w.
Proof.
  induction F as [|F IH]; intros c [|b r]; cbn [loop]; try (apply PMRF2.wsuf_same; reflexivity); destruct (negb (c_more c)); try (apply PMRF2.wsuf_same; reflexivity).
  apply bind_suffix; [apply act_run_suffix | intros c' w'; apply IH].
Qed.
Lemma prologue_w : forall c, q_w (prologue c) = [].
Proof.
  intros c. unfold prologue. destruct (c_st c =? ST_NUMBER); [destruct (_ || _); [apply PMRF2.end_number_w | reflexivity]|].
  destruct (c_st c =? ST_ACCEPT); [reflexivity|]. destruct (c_st c =? ST_START); [reflexivity|]. destruct (c_st c =? ST_DONE); [reflexivity|]. destruct (c_st c =? ST_CR); reflexivity.
Qed.
Lemma parse_some_suffix : forall c w, PMRF2.wsuf (parse_some c w) w.
Proof.
  intros c w. unfold parse_some. destruct (c_st c =? ST_ACCEPT); [apply PMRF2.wsuf_same; reflexivity|].
  destruct w as [|b r]; [|apply loop_suffix]. destruct (c_more c); [apply PMRF2.wsuf_nil; apply prologue_w | apply PMRF2.wsuf_same; reflexivity].
Qed.
Lemma parse_some_after : forall c w, PMW.w_after the_rm (rstep PMW.FParseSome c w) w = q_w (parse_some c w).
Proof.
  intros c w. unfold PMW.w_after. cbn [rstep]. rewrite PMRF2.r_of_used. destruct (parse_some_suffix c w) as [u Hu]. rewrite Hu, PMRF2.used_to_nat. apply PMRF2.skipn_used.
Qed.
Lemma sws_suffix : forall c w, exists u, snd (skip_whitespace c w) = skipn u w.
Proof.
  intros c [|b r]; [exists 0%nat; reflexivity|]. unfold skip_whitespace.
  set (cw := if c_st c =? ST_CR then _ else _).
  assert (X : exists u, snd cw = skipn u (b :: r)).
  { subst cw. destruct (c_st c =? ST_CR); [|exists 0%nat; reflexivity]. cbn [snd]. destruct (b =? 10); [exists 1%nat | exists 0%nat]; reflexivity. }
  destruct X as [u Hu]. destruct (snd cw) as [|b1 r1] eqn:Hcw; [exists u; rewrite Hcw; exact Hu|].
  destruct (is_ws b1); [|exists u; rewrite Hcw; exact Hu]. destruct (PMRF2.skip_space_suffix (b1 :: r1) (fst cw)) as [v Hv]. exists (v + u)%nat. rewrite Hv, Hu. apply skipn_skipn.
Qed.
Lemma sws_after : forall c w, PMW.w_after the_rm (rstep PMW.FSkipWs c w) w = snd (skip_whitespace c w).
Proof.
  intros c w. unfold PMW.w_after. cbn [rstep]. cbv zeta. rewrite PMRF2.r_of_used. cbn [q_w ret]. destruct (sws_suffix c w) as [u Hu]. rewrite Hu, PMRF2.used_to_nat. apply PMRF2.skipn_used.
Qed.
Lemma pcd_facts : forall c w, let q := pcheck_done c w in (q_code q = 0 -> q_w q = [] /\ q_c q = c) /\ (q_code q = 0 \/ q_code q = E_EXTRA_CHAR).
Proof. intros c w. unfold pcheck_done. destruct (forallb is_ws w); cbn; [split; [intros _; split; reflexivity | left; reflexivity] | split; [intros X; discriminate X | right; reflexivity]]. Qed.
Lemma read_check_done_live : forall F rs, r_eof rs = false -> read_check_done F rs = rcheck F rs.
Proof. intros F rs H. unfold read_check_done. rewrite H. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma after_psome : forall c w, PMW.w_after the_rm (PMW.rm_step the_rm PMW.FParseSome c w) w = q_w (parse_some c w).
Proof. intros c w. exact (parse_some_after c w). Qed.
Lemma after_sws : forall c w, PMW.w_after the_rm (PMW.rm_step the_rm PMW.FSkipWs c w) w = snd (skip_whitespace c w).
Proof. intros c w. exact (sws_after c w). Qed.
Lemma ctrl_sws : forall c w, PMW.r_ctrl (PMW.rm_step the_rm PMW.FSkipWs c w) = fst (skip_whitespace c w). Proof. reflexivity. Qed.
Lemma code_sws : forall c w, PMW.r_code (PMW.rm_step the_rm PMW.FSkipWs c w) = 0. Proof. reflexivity. Qed.
Lemma ctrl_psome : forall c w, PMW.r_ctrl (PMW.rm_step the_rm PMW.FParseSome c w) = q_c (parse_some c w). Proof. reflexivity. Qed.
Lemma code_psome : forall c w, PMW.r_code (PMW.rm_step the_rm PMW.FParseSome c w) = q_code (parse_some c w). Proof. reflexivity. Qed.
Lemma evs_psome : forall c w, PMW.r_evs (PMW.rm_step the_rm PMW.FParseSome c w) = q_evs (parse_some c w). Proof. reflexivity. Qed.
Lemma allow_psome : forall c w, PMW.r_allow (PMW.rm_step the_rm PMW.FParseSome c w) = q_al (parse_some c w). Proof. reflexivity. Qed.

(* [comment removed for export] *)
Section S.
Variable IS : Z.
Variable rep : srep.
#[local] Set Default Proof Using "IS rep".   (* [comment removed for export] *)
Let txt := srep_chars rep.
Let D := srep_data (IS + 80) rep.

Definition rsof (c : ctrl) (w : list Z) (gp : Z) (bof : bool) (rdst : Z) : rstate := RS c w (TPSW.rest_of IS rep gp) bof (rdst =? 2).

Lemma rest_of_D : TPSW.rest_of IS rep D = txt.
Proof. unfold TPSW.rest_of. fold D. rewrite Z.sub_diag. reflexivity. Qed.
Lemma rsof_init : rsof ctrl0 [] D true 0 = rs0 txt.
Proof. unfold rsof, rs0. rewrite rest_of_D. reflexivity. Qed.
Lemma length_rest_of : forall gp, D <= gp <= D + Z.of_nat (length txt) -> Z.of_nat (length (TPSW.rest_of IS rep gp)) = D + Z.of_nat (length txt) - gp.
Proof. intros gp H. unfold TPSW.rest_of. fold D. fold txt. rewrite length_skipn. lia. Qed.
Lemma length_chunk_of : forall gp, D <= gp <= D + Z.of_nat (length txt) -> Z.of_nat (length (TPSW.chunk_of IS rep gp)) = Z.min CHUNK (D + Z.of_nat (length txt) - gp).
Proof. intros gp H. unfold TPSW.chunk_of. rewrite length_firstn_min. pose proof (length_rest_of gp H). unfold CHUNK in *. lia. Qed.
(* [comment removed for export] *)
Lemma rest_of_next : forall gp, D <= gp <= D + Z.of_nat (length txt) ->
  TPSW.rest_of IS rep (gp + Z.of_nat (length (TPSW.chunk_of IS rep gp))) = skipn (Z.to_nat CHUNK) (TPSW.rest_of IS rep gp).
Proof.
  intros gp H. unfold TPSW.chunk_of. rewrite <- skipn_firstn_len. unfold TPSW.rest_of. fold D. fold txt. rewrite skipn_skipn. f_equal.
  rewrite length_firstn_min, length_skipn. lia.
Qed.

(* [comment removed for export] *)
Lemma chunk_w_inv : forall (M' : mem) gp bof ch p k gp' rdst' code bof',
  TPSW.chunk_w M' IS rep gp bof ch p k gp' rdst' code bof' ->
  exists s j cd b', TPSW.chunk_of IS rep gp = s /\ chunkw s bof = (j, cd, b') /\
  gp' = gp + Z.of_nat (length s) /\ rdst' = (if (length s <? Z.to_nat CHUNK)%nat then 2 else 0) /\ code = cd /\ bof' = b' /\
  (cd = 0 -> k = Z.of_nat (length s) - Z.of_nat j /\ (0 < k -> p = ch + Z.of_nat j /\ L5.bytes_at RSEGS M' p (skipn j s))) /\
  (cd <> 0 -> k = 0).
Proof.
  intros M' gp bof ch p k gp' rdst' code bof'. unfold TPSW.chunk_w. cbv zeta.
  generalize (TPSW.chunk_of IS rep gp) as s. intros s CW. exists s.
  destruct (chunkw s bof) as [[j cd] b']. exists j, cd, b'. split; [reflexivity|]. split; [reflexivity|]. exact CW.
Qed.
(* [comment removed for export] *)
Lemma refill_rsof_read : forall c gp bof s j cd b', D <= gp <= D + Z.of_nat (length txt) ->
  TPSW.chunk_of IS rep gp = s -> chunkw s bof = (j, cd, b') ->
  refill (rsof c [] gp bof 0) = (rsof c (if cd =? 0 then skipn j s else []) (gp + Z.of_nat (length s)) b' (if (length s <? Z.to_nat CHUNK)%nat then 2 else 0), cd).
Proof.
  intros c gp bof s j cd b' Hgp Hs EC. unfold rsof. change (0 =? 2) with false. rewrite refill_read.
  change (firstn (Z.to_nat CHUNK) (TPSW.rest_of IS rep gp)) with (TPSW.chunk_of IS rep gp). cbv zeta. rewrite Hs, EC. f_equal. f_equal.
  - rewrite <- (rest_of_next gp Hgp), Hs. reflexivity.
  - destruct (length s <? Z.to_nat CHUNK)%nat; reflexivity.
Qed.
Lemma refill_of_chunk_w : forall (M' : mem) c gp bof ch p k gp' rdst' code bof',
  D <= gp <= D + Z.of_nat (length txt) ->
  TPSW.chunk_w M' IS rep gp bof ch p k gp' rdst' code bof' ->
  exists s j cd b', TPSW.chunk_of IS rep gp = s /\ chunkw s bof = (j, cd, b') /\
  refill (rsof c [] gp bof 0) = (rsof c (if code =? 0 then skipn j s else []) gp' bof' rdst', code) /\
  gp' = gp + Z.of_nat (length s) /\ (rdst' = 2 <-> (length s < Z.to_nat CHUNK)%nat) /\ (rdst' = 0 \/ rdst' = 2) /\
  (code = 0 -> k = Z.of_nat (length s) - Z.of_nat j /\ (j <= length s)%nat /\ (0 < k -> p = ch + Z.of_nat j /\ L5.bytes_at RSEGS M' p (skipn j s))) /\
  (code <> 0 -> k = 0).
Proof.
  intros M' c gp bof ch p k gp' rdst' code bof' Hgp CW.
  destruct (chunk_w_inv M' gp bof ch p k gp' rdst' code bof' CW) as (s & j & cd & b' & Hs & EC & Hgp' & Hrd & -> & -> & C0 & C1).
  pose proof (chunkw_skip_le _ _ _ _ _ EC) as [JL _].
  exists s, j, cd, b'. split; [exact Hs|]. split; [exact EC|].
  split; [rewrite (refill_rsof_read c gp bof s j cd b' Hgp Hs EC), Hgp', Hrd; reflexivity|].
  split; [exact Hgp'|]. split; [rewrite Hrd; destruct (Nat.ltb_spec (length s) (Z.to_nat CHUNK)); split; intros X; try lia; try reflexivity; discriminate X|].
  split; [rewrite Hrd; destruct (length s <? Z.to_nat CHUNK)%nat; lia|].
  split; [|exact C1]. intros Hc. destruct (C0 Hc) as [K0 KP]. split; [exact K0 | split; [exact JL | exact KP]].
Qed.
(* [comment removed for export] *)
Lemma refill_at_eof : forall c w gp bof, refill (rsof c w gp bof 2) = (rsof c w gp bof 2, 0).
Proof. intros c w gp bof. unfold rsof. destruct w; [apply refill_eof; reflexivity | reflexivity]. Qed.
Lemma refill_nonempty : forall c b r gp bof rdst, refill (rsof c (b :: r) gp bof rdst) = (rsof c (b :: r) gp bof rdst, 0).
Proof. intros. reflexivity. Qed.

(* [comment removed for export] *)
Lemma nchunks_le : forall c w gp bof rdst, D <= gp <= D + Z.of_nat (length txt) -> nchunks (rsof c w gp bof rdst) <= Z.of_nat (length txt) / CHUNK + 1.
Proof.
  intros c w gp bof rdst Hgp. unfold nchunks, rsof. cbn [r_eof r_rest]. destruct (rdst =? 2); [pose proof (Z.div_pos (Z.of_nat (length txt)) CHUNK); unfold CHUNK in *; lia|].
  rewrite (length_rest_of gp Hgp). apply Z.add_le_mono_r. apply Z.div_le_mono; unfold CHUNK; lia.
Qed.
Lemma nchunks_read : forall (M' : mem) c gp bof ch p k gp' rdst' code bof' w',
  D <= gp <= D + Z.of_nat (length txt) -> TPSW.chunk_w M' IS rep gp bof ch p k gp' rdst' code bof' ->
  nchunks (rsof c w' gp' bof' rdst') <= nchunks (rsof c [] gp bof 0) - 1.
Proof.
  intros M' c gp bof ch p k gp' rdst' code bof' w' Hgp CW.
  destruct (refill_of_chunk_w M' c gp bof ch p k gp' rdst' code bof' Hgp CW) as (s & j & cd & b' & Hs & _ & _ & G' & RD & _ & _ & _).
  pose proof (length_chunk_of gp Hgp) as LS. rewrite Hs in LS. pose proof (length_rest_of gp Hgp) as LR.
  unfold nchunks, rsof. cbn [r_eof r_rest]. change (0 =? 2) with false. cbv iota.
  destruct (Z.eqb_spec rdst' 2) as [E|NE].
  - pose proof (Z.div_pos (Z.of_nat (length (TPSW.rest_of IS rep gp))) CHUNK ltac:(lia) ltac:(unfold CHUNK; lia)). lia.
  - assert (FULL : Z.of_nat (length s) = CHUNK).
    { destruct (Nat.lt_ge_cases (length s) (Z.to_nat CHUNK)) as [X|X]; [exfalso; exact (NE (proj2 RD X))|]. clear - LS X. unfold CHUNK in *. lia. }
    rewrite (length_rest_of gp' ltac:(unfold CHUNK in *; lia)), LR. rewrite G', FULL.
    replace (D + Z.of_nat (length txt) - gp) with ((D + Z.of_nat (length txt) - (gp + CHUNK)) + 1 * CHUNK) by lia. rewrite Z.div_add by (unfold CHUNK; lia). lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition accA (evs : list evk) (al : Z) (F' : nat) (rs : rstate) : Prop :=
  rloop (rfuel txt) (rs0 txt) = rpre evs al (rloop F' rs) /\ RB rs <= Z.of_nat F'.
Lemma accA_init : accA [] 0 (rfuel txt) (rs0 txt).
Proof. split; [symmetry; apply rpre_nil | rewrite <- RB_init; unfold rs0; lia]. Qed.
(* [comment removed for export] *)
Lemma accA_cont : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  rcont rs1 q -> RB (rs_after q rs1) <= RB rs - 1 ->
  exists F'', F' = S F'' /\ accA (evs ++ q_evs q) (al + q_al q) F'' (rs_after q rs1).
Proof.
  intros evs al F' rs rs1 q [ACC FB] Hm Hr Hq Hc RC DEC. pose proof (RB_pos rs) as P0.
  destruct F' as [|F'']; [cbn in FB; lia|]. exists F''. split; [reflexivity|]. split; [|lia].
  rewrite ACC. rewrite (rloop_cont F'' rs rs1 q Hm Hr Hq Hc RC). rewrite rpre_rpre. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma accA_end : forall evs al F' rs t, accA evs al F' rs -> (forall F'', F' = S F'' -> rloop F' rs = t) ->
  rloop (rfuel txt) (rs0 txt) = rpre evs al t.
Proof.
  intros evs al F' rs t [ACC FB] HT. pose proof (RB_pos rs) as P0. destruct F' as [|F'']; [cbn in FB; lia|]. rewrite ACC, (HT F'' eq_refl). reflexivity.
Qed.

Lemma rfuel_ge : forall c w gp bof rdst, D <= gp <= D + Z.of_nat (length txt) -> nchunks (rsof c w gp bof rdst) + 3 <= Z.of_nat (rfuel txt).
Proof.
  intros c w gp bof rdst Hgp. pose proof (nchunks_le c w gp bof rdst Hgp) as X. unfold rfuel. rewrite Nat2Z.inj_add, Nat2Z.inj_div.
  change (Z.of_nat (Z.to_nat CHUNK)) with CHUNK. change (Z.of_nat 4) with 4. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma accA_S : forall evs al F' rs, accA evs al F' rs -> exists F'', F' = S F''.
Proof. intros evs al F' rs [_ FB]. pose proof (RB_pos rs). destruct F' as [|F'']; [cbn in FB; lia | exists F''; reflexivity]. Qed.
Lemma accA_SS : forall evs al F' rs, accA evs al F' rs -> c_more (r_c rs) = true -> exists F'', F' = S (S F'').
Proof.
  intros evs al F' rs [_ FB] Hm. pose proof (nchunks_nonneg rs) as N0. pose proof (rankz_range (r_c rs)) as R0.
  assert (2 <= RB rs) by (unfold RB, wwz; rewrite Hm; cbn [negb]; destruct (r_w rs); cbn [Z.eqb andb]; [destruct (nchunks rs =? 0)|]; lia).
  destruct F' as [|[|F'']]; [cbn in FB; lia | cbn in FB; lia | exists F''; reflexivity].
Qed.
(* [comment removed for export] *)
Lemma READ_A : forall tA, rloop (rfuel txt) (rs0 txt) = tA -> t_code tA <> 0 -> READ txt = (t_evs tA, t_al tA, t_code tA).
Proof. intros tA HA Hc. exact (proj1 (READ_of txt tA HA) Hc). Qed.
Lemma READ_B : forall tA tB, rloop (rfuel txt) (rs0 txt) = tA -> t_code tA = 0 -> rtail (rfuel txt) (sw (t_rs tA)) = tB -> snd tB <> 0 -> READ txt = (t_evs tA, t_al tA, snd tB).
Proof. intros tA tB HA Hc HB Hb. exact (proj1 (proj2 (READ_of txt tA HA) Hc tB HB) Hb). Qed.
Lemma READ_C : forall tA tB, rloop (rfuel txt) (rs0 txt) = tA -> t_code tA = 0 -> rtail (rfuel txt) (sw (t_rs tA)) = tB -> snd tB = 0 ->
  READ txt = (t_evs tA, t_al tA, read_check_done (rfuel txt) (fst tB)).
Proof. intros tA tB HA Hc HB Hb. exact (proj2 (proj2 (READ_of txt tA HA) Hc tB HB) Hb). Qed.
Lemma roundA_referr : forall evs al F' rs rs1 cd, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, cd) -> cd <> 0 ->
  READ txt = (evs, al, cd).
Proof.
  intros evs al F' rs rs1 cd ACC Hm Hr Hcd. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  pose proof (accA_end evs al (S F'') rs (rs1, [], 0, cd) ACC (fun G _ => rloop_referr F'' rs rs1 cd Hm Hr Hcd)) as HA.
  rewrite (READ_A _ HA ltac:(cbn; exact Hcd)). unfold rpre. cbn [t_rs t_evs t_al t_code fst snd]. rewrite app_nil_r, Z.add_0_r. reflexivity.
Qed.
Lemma roundA_pserr : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q <> 0 ->
  READ txt = (evs ++ q_evs q, al + q_al q, q_code q).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  pose proof (accA_end evs al (S F'') rs (rs_after q rs1, q_evs q, q_al q, q_code q) ACC (fun G _ => rloop_pserr F'' rs rs1 q Hm Hr Hq Hc)) as HA.
  rewrite (READ_A _ HA ltac:(cbn; exact Hc)). reflexivity.
Qed.
Lemma roundA_ueof : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  weof rs1 = true -> c_st (q_c q) <> ST_START -> c_st (q_c q) <> ST_ACCEPT -> c_done (q_c q) = false ->
  READ txt = (evs ++ q_evs q, al + q_al q, E_EOF).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc He Hs Ha Hd. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  pose proof (accA_end evs al (S F'') rs (rs_after q rs1, q_evs q, q_al q, E_EOF) ACC (fun G _ => rloop_ueof F'' rs rs1 q Hm Hr Hq Hc He Hs Ha Hd)) as HA.
  rewrite (READ_A _ HA ltac:(cbn; discriminate)). reflexivity.
Qed.
(* [comment removed for export] *)
Lemma roundA_stop : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  (weof rs1 = true /\ c_st (q_c q) = ST_START) \/ (c_more (q_c q) = false /\ (weof rs1 = true -> c_st (q_c q) = ST_ACCEPT \/ c_done (q_c q) = true)) ->
  rloop (rfuel txt) (rs0 txt) = (rs_after q rs1, evs ++ q_evs q, al + q_al q, 0).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc HX. destruct (accA_SS _ _ _ _ ACC Hm) as [F'' ->].
  apply (accA_end evs al (S (S F'')) rs (rs_after q rs1, q_evs q, q_al q, 0) ACC). intros G HG. injection HG as <-.
  destruct (Z.eqb_spec (c_st (q_c q)) ST_START) as [Hs|Hs].
  - destruct HX as [[He _]|[Hm' HA]].
    + exact (rloop_start (S F'') rs rs1 q Hm Hr Hq Hc He Hs).
    + destruct (weof rs1) eqn:He; [exact (rloop_start (S F'') rs rs1 q Hm Hr Hq Hc He Hs)|].
      rewrite (rloop_cont (S F'') rs rs1 q Hm Hr Hq Hc (or_introl He)). rewrite (rloop_stopped F'' (rs_after q rs1) Hm'). unfold rpre. cbn [t_rs t_evs t_al t_code fst snd]. rewrite app_nil_r, Z.add_0_r. reflexivity.
  - destruct HX as [[_ X]|[Hm' HA]]; [contradiction|].
    assert (RC : rcont rs1 q) by (unfold rcont; destruct (weof rs1); [right; split; [exact Hs | exact (HA eq_refl)] | left; reflexivity]).
    rewrite (rloop_cont (S F'') rs rs1 q Hm Hr Hq Hc RC). rewrite (rloop_stopped F'' (rs_after q rs1) Hm'). unfold rpre. cbn [t_rs t_evs t_al t_code fst snd]. rewrite app_nil_r, Z.add_0_r. reflexivity.
Qed.
(* [comment removed for export] *)
Lemma roundA_cont : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  rcont rs1 q -> q_w q = [] -> c_more (q_c q) = true -> (r_w rs = [] -> r_eof rs = true -> rankz (r_c rs) = 1 /\ rankz (q_c q) = 0) ->
  exists F'', accA (evs ++ q_evs q) (al + q_al q) F'' (rs_after q rs1).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc RC Hw Hm' RK.
  destruct (accA_cont evs al F' rs rs1 q ACC Hm Hr Hq Hc RC (RB_round rs rs1 q Hm Hr Hw Hm' RK)) as (F'' & _ & A). exists F''. exact A.
Qed.

(* [comment removed for export] *)
Lemma roundA_referr_t : forall evs al F' rs rs1 cd, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, cd) -> cd <> 0 ->
  rloop (rfuel txt) (rs0 txt) = (rs1, evs, al, cd).
Proof.
  intros evs al F' rs rs1 cd ACC Hm Hr Hcd. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  rewrite (accA_end evs al (S F'') rs (rs1, [], 0, cd) ACC (fun G _ => rloop_referr F'' rs rs1 cd Hm Hr Hcd)).
  unfold rpre. cbn [t_rs t_evs t_al t_code fst snd]. rewrite app_nil_r, Z.add_0_r. reflexivity.
Qed.
Lemma roundA_pserr_t : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q <> 0 ->
  rloop (rfuel txt) (rs0 txt) = (rs_after q rs1, evs ++ q_evs q, al + q_al q, q_code q).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  rewrite (accA_end evs al (S F'') rs (rs_after q rs1, q_evs q, q_al q, q_code q) ACC (fun G _ => rloop_pserr F'' rs rs1 q Hm Hr Hq Hc)). reflexivity.
Qed.
Lemma roundA_ueof_t : forall evs al F' rs rs1 q, accA evs al F' rs -> c_more (r_c rs) = true -> refill rs = (rs1, 0) -> parse_some (r_c rs1) (r_w rs1) = q -> q_code q = 0 ->
  weof rs1 = true -> c_st (q_c q) <> ST_START -> c_st (q_c q) <> ST_ACCEPT -> c_done (q_c q) = false ->
  rloop (rfuel txt) (rs0 txt) = (rs_after q rs1, evs ++ q_evs q, al + q_al q, E_EOF).
Proof.
  intros evs al F' rs rs1 q ACC Hm Hr Hq Hc He Hs Ha Hd. destruct (accA_S _ _ _ _ ACC) as [F'' ->].
  rewrite (accA_end evs al (S F'') rs (rs_after q rs1, q_evs q, q_al q, E_EOF) ACC (fun G _ => rloop_ueof F'' rs rs1 q Hm Hr Hq Hc He Hs Ha Hd)). reflexivity.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma qcheck_rsof : forall c w gp bof rdst, qcheck (rsof c w gp bof rdst) = match w with [] => ret c [] | _ => pcheck_done c w end.
Proof. intros c [|b r] gp bof rdst; reflexivity. Qed.
Lemma sw_rsof : forall c w gp bof rdst c' w', skip_whitespace c w = (c', w') -> sw (rsof c w gp bof rdst) = rsof c' w' gp bof rdst.
Proof. intros c w gp bof rdst c' w' H. unfold sw, rsof. cbn [r_c r_w r_rest r_bof r_eof]. rewrite H. reflexivity. Qed.
Lemma rs_after_rsof : forall q c w gp bof rdst, rs_after q (rsof c w gp bof rdst) = rsof (q_c q) (q_w q) gp bof rdst.
Proof. reflexivity. Qed.
Lemma r_c_rsof : forall c w gp bof rdst, r_c (rsof c w gp bof rdst) = c. Proof. reflexivity. Qed.
Lemma r_w_rsof : forall c w gp bof rdst, r_w (rsof c w gp bof rdst) = w. Proof. reflexivity. Qed.
Lemma r_eof_rsof : forall c w gp bof rdst, r_eof (rsof c w gp bof rdst) = (rdst =? 2). Proof. reflexivity. Qed.
Lemma weof_rsof : forall c w gp bof rdst, weof (rsof c w gp bof rdst) = match w with [] => true | _ => false end. Proof. reflexivity. Qed.
Lemma wwz_rsof : forall c w gp bof rdst, wwz (rsof c w gp bof rdst) = match w with [] => 0 | _ => 1 end. Proof. reflexivity. Qed.
Lemma wwz_rsof_nil : forall c gp bof rdst, wwz (rsof c [] gp bof rdst) = 0. Proof. reflexivity. Qed.
Lemma wwz_rsof_cons : forall c b r gp bof rdst, wwz (rsof c (b :: r) gp bof rdst) = 1. Proof. reflexivity. Qed.
Lemma nchunks_rsof_c : forall c c' w w' gp bof bof' rdst, nchunks (rsof c w gp bof rdst) = nchunks (rsof c' w' gp bof' rdst). Proof. reflexivity. Qed.
Lemma read_check_done_eof : forall F c w gp bof, read_check_done F (rsof c w gp bof 2) = q_code (pcheck_done c w). Proof. reflexivity. Qed.
End S.
End RKW.
