(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.AS Require Import PropExec AxSymExec3 AxSymExec3Sound.
From OSSVerify.Proofs.simdjson.fuzz_parser.lib.Seg Require Import SegLin SegTmpl SegGhost SegDig.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S.
Open Scope Z_scope.

Module SDGok.
Import SDG.
Local Notation u := bv_unsigned.

Lemma u_rng : forall w : word, 0 <= u w < 2 ^ 64.
Proof. intros w. pose proof (bv_unsigned_in_range _ w) as H. unfold bv_modulus in H. exact H. Qed.
Lemma u_lit : forall z, u (Z_to_bv 64 z) = z mod 2 ^ 64.
Proof. intros z. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. reflexivity. Qed.

Lemma leqx_sound : forall E a b, leqx a b = true -> edenot E a = edenot E b.
Proof.
  intros E a b H. unfold leqx in H. destruct (lin_of (mkAlu ALU_SUB a b)) as [c ts] eqn:Hl. destruct ts; [|discriminate].
  apply Z.eqb_eq in H. pose proof (lin_of_sound E (mkAlu ALU_SUB a b)) as L. rewrite Hl in L. unfold lden in L. cbn [fst snd tden] in L.
  unfold uE in L. rewrite mkAlu_denot, alu_sub in L. unfold v_sub in L. rewrite u_lit in L.
  destruct L as [q Hq]. pose proof (u_rng (edenot E a)). pose proof (u_rng (edenot E b)).
  pose proof (Z.mod_pos_bound (u (edenot E a) - u (edenot E b)) (2 ^ 64) ltac:(lia)).
  assert (Hm : (u (edenot E a) - u (edenot E b)) mod 2 ^ 64 = 0).
  { rewrite Z.add_0_r in Hq. rewrite Hq in H. rewrite Z.mod_add in H by lia. rewrite Z.mod_mod in H by lia. exact H. }
  apply bv_eq. apply Z.mod_divide in Hm; [|lia]. destruct Hm as [k Hk]. assert (k = 0) by nia. subst k. lia.
Qed.

Lemma u_eadd : forall E a b, u (edenot E (eadd a b)) = (u (edenot E a) + u (edenot E b)) mod 2 ^ 64.
Proof. intros E a b. unfold eadd. rewrite mkAlu_denot, alu_add. unfold v_add. apply u_lit. Qed.
Lemma u_e1 : forall E a, u (edenot E (e1 a)) = (u (edenot E a) + 1) mod 2 ^ 64.
Proof. intros E a. unfold e1. rewrite mkAlu_denot, alu_add. unfold v_add. rewrite u_lit, edenot_lit, u_lit. reflexivity. Qed.

Lemma u_x1 : forall E v, u (edenot E (x1 v)) = u (ev E v) mod 256.
Proof.
  intros E v. unfold x1. cbn [edenot]. unfold ext_val, ext_Z. cbn [Z.of_nat]. rewrite Z.mul_0_r, Z.pow_0_r, Z.div_1_r.
  change (2 ^ (8 * 1)) with 256. rewrite u_lit. apply Z.mod_small. pose proof (Z.mod_pos_bound (u (ev E v)) 256). lia.
Qed.

Section Sound.
Variable segs : list Segment.

Lemma kimp_range : forall E M kn e lo hi, know_ok segs E M kn -> kimp segs kn (KRange e lo hi) = true -> lo <= u (edenot E e) <= hi.
Proof. intros E M kn e lo hi HK H. pose proof (ST.kimplied_ok segs E M kn _ HK H) as R. cbn [kentry_ok] in R. exact R. Qed.

(* [comment removed for export] *)
Lemma rd1_sound : forall m E path s AP v, scs_denot segs m E path -> In s path -> rd1 s = Some (AP, v) ->
  u (edenot E (x1 v)) = mbr segs m (u (edenot E AP)) /\ u (edenot E (x1 v)) < 256.
Proof.
  intros m E path s AP v HP Hin H. unfold rd1 in H.
  destruct s as [| | | | |a n sx e| ]; try discriminate.
  destruct n as [|[|n]]; try discriminate. destruct sx; try discriminate. destruct e as [|w| | | | | |]; try discriminate.
  injection H as <- <-.
  pose proof (proj1 (Forall_forall _ _) HP _ Hin) as (bs & Hr & Hv). cbn [sc_denot extz] in Hv. cbn [edenot] in Hv.
  cbn [rdn] in Hr.
  destruct (match m (adenot E a) with Some b => Some b | None => seg_rom segs (adenot E a) end) as [b|] eqn:Hb; [|discriminate].
  injection Hr as <-. cbn [bytes_le_to_Z] in Hv. rewrite Z.shiftl_0_l, Z.lor_0_r in Hv.
  assert (Ub : u (ev E w) = u b) by (rewrite <- Hv, u_lit; apply Z.mod_small; pose proof (bv_unsigned_in_range _ b); unfold bv_modulus in *; cbn in *; lia).
  assert (Ab : Z_to_bv 64 (u (edenot E (EAlu ALU_ADD (a_base a) (ELit (a_off a))))) = adenot E a).
  { cbn [edenot]. rewrite alu_add. unfold v_add, adenot, v_addi. rewrite Z_to_bv_bv_unsigned. apply bv_eq. rewrite !u_lit.
    rewrite Zplus_mod_idemp_r. reflexivity. }
  rewrite u_x1, Ub. unfold mbr. rewrite Ab, Hb.
  pose proof (bv_unsigned_in_range _ b) as Rb. unfold bv_modulus in Rb. change (2 ^ Z.of_N 8) with 256 in Rb.
  rewrite Z.mod_small by lia. split; [reflexivity | lia].
Qed.

Lemma rd_at_sound : forall E m path P f, scs_denot segs m E path -> rd_at path P f = true ->
  exists v, f v = true /\ u (edenot E (x1 v)) = mbr segs m (u (edenot E P)) /\ u (edenot E (x1 v)) < 256.
Proof.
  intros E m path P f HP H. unfold rd_at in H. apply SLin.lex_exists in H as (s & Hin & Hs).
  destruct (rd1 s) as [[AP v]|] eqn:Hr; [|discriminate]. destruct (leqx AP P) eqn:Hq; [|discriminate].
  destruct (rd1_sound m E path s AP v HP Hin Hr) as [A B]. exists v. split; [exact Hs|].
  rewrite <- (leqx_sound E AP P Hq). split; assumption.
Qed.

Lemma dtest_u : forall E v, u (edenot E (dtest v)) = (u (edenot E (x1 v)) + 208) mod 256.
Proof.
  intros E v. unfold dtest. cbn [edenot]. rewrite alu_and, alu_add. unfold v_and, v_add.
  rewrite !u_lit. change (255 mod 2 ^ 64) with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
  rewrite (Z.mod_small (_ mod 256) (2 ^ 64)) by (match goal with |- context [?y mod 256] => pose proof (Z.mod_pos_bound y 256) end; lia).
  rewrite Z.mod_mod_divide by (exists (2 ^ 56); reflexivity).
  change ((-48) mod 2 ^ 64) with 18446744073709551568.
  replace (u (edenot E (x1 v)) + 18446744073709551568) with ((u (edenot E (x1 v)) + 208) + 72057594037927935 * 256) by lia.
  apply Z.mod_add. lia.
Qed.

Lemma dig_known_sound : forall E M kn v, know_ok segs E M kn -> u (edenot E (x1 v)) < 256 -> dig_known segs kn v = true ->
  isdig (u (edenot E (x1 v))).
Proof.
  intros E M kn v HK Hb H. unfold dig_known in H. unfold isdig.
  destruct (kimp segs kn (KRange (x1 v) 48 57)) eqn:H1; [exact (kimp_range E M kn _ _ _ HK H1)|].
  pose proof (kimp_range E M kn _ _ _ HK H) as R. rewrite dtest_u in R. pose proof (u_rng (edenot E (x1 v))).
  destruct (Z_lt_ge_dec (u (edenot E (x1 v))) 48) as [L|L].
  - rewrite Z.mod_small in R by lia. lia.
  - rewrite (Z.mod_eq (u (edenot E (x1 v)) + 208) 256) in R by lia.
    assert ((u (edenot E (x1 v)) + 208) / 256 = 1) by (symmetry; apply Z.div_unique with (u (edenot E (x1 v)) - 48); [left; lia | lia]). lia.
Qed.

Lemma nodig_known_sound : forall E M kn v, know_ok segs E M kn -> u (edenot E (x1 v)) < 256 -> nodig_known segs kn v = true ->
  ~ isdig (u (edenot E (x1 v))).
Proof.
  intros E M kn v HK Hb H Hd. unfold nodig_known in H. unfold isdig in Hd.
  pose proof (kimp_range E M kn _ _ _ HK H) as R. rewrite dtest_u in R.
  rewrite (Z.mod_eq (u (edenot E (x1 v)) + 208) 256) in R by lia.
  assert ((u (edenot E (x1 v)) + 208) / 256 = 1) by (symmetry; apply Z.div_unique with (u (edenot E (x1 v)) - 48); [left; lia | lia]). lia.
Qed.

Lemma zero_known_sound : forall E M kn v, know_ok segs E M kn -> zero_known segs kn v = true -> u (edenot E (x1 v)) = 48.
Proof.
  intros E M kn v HK H. unfold zero_known in H.
  destruct (kimp segs kn (KRange (x1 v) 48 48)) eqn:H1; [pose proof (kimp_range E M kn _ _ _ HK H1); lia|].
  pose proof (kimp_range E M kn _ _ _ HK H) as R. rewrite u_x1. cbn [edenot] in R. rewrite Z.mod_small by lia. lia.
Qed.

Lemma mbr_log : forall E m kn lg A N, know_ok segs E m kn -> log_flat E lg -> SG.log_apart kn lg [(A, 0, N)] = true ->
  forall i, 0 <= i < u (edenot E N) -> u (edenot E A) + i < 2 ^ 64 ->
  mbr segs (mem_denot E m lg) (u (edenot E A) + i) = mbr segs m (u (edenot E A) + i).
Proof.
  intros E m kn lg A N HK HL HA i Hi Hw. apply mbr_frame. apply (SG.mem_denot_apart segs E kn m lg [(A, 0, N)] _ HK HL HA).
  exists (A, 0, N). split; [left; reflexivity|]. cbn [SG.win_den]. rewrite u_lit, Z.mod_small by (pose proof (u_rng (edenot E A)); lia).
  lia.
Qed.

Lemma mdec_log : forall E m kn lg A N n, know_ok segs E m kn -> log_flat E lg -> SG.log_apart kn lg [(A, 0, N)] = true ->
  0 <= n <= u (edenot E N) -> u (edenot E A) + n < 2 ^ 64 ->
  mdec segs (mem_denot E m lg) (u (edenot E A)) n = mdec segs m (u (edenot E A)) n.
Proof.
  intros E m kn lg A N n HK HL HA Hn Hw. unfold mdec. apply mdec_n_frame. intros i Hi. rewrite Z2Nat.id in Hi by lia.
  apply (SG.mem_denot_apart segs E kn m lg [(A, 0, N)] _ HK HL HA).
  exists (A, 0, N). split; [left; reflexivity|]. cbn [SG.win_den]. rewrite u_lit, Z.mod_small by (pose proof (u_rng (edenot E A)); lia).
  lia.
Qed.

Lemma step_val_sound : forall E X X' D, step_val X X' D = true -> u (edenot E D) <= 9 ->
  u (edenot E X') = (10 * u (edenot E X) + u (edenot E D)) mod 2 ^ 64.
Proof.
  intros E X X' D H HD. unfold step_val in H.
  assert (A : forall D0, u (edenot E D0) = u (edenot E D) ->
            u (edenot E (eadd (mkMd M_MUL (ELit 10) X) D0)) = (10 * u (edenot E X) + u (edenot E D)) mod 2 ^ 64).
  { intros D0 HD0. rewrite u_eadd, mkMd_denot, m_mul. unfold v_mul. rewrite u_lit, edenot_lit, u_lit. change (10 mod 2 ^ 64) with 10.
    rewrite HD0. rewrite Zplus_mod_idemp_l. reflexivity. }
  destruct (leqx X' (eadd (mkMd M_MUL (ELit 10) X) D)) eqn:H1.
  - rewrite (leqx_sound E _ _ H1). apply A. reflexivity.
  - rewrite (leqx_sound E _ _ H). apply A. rewrite mkAlu_denot, alu_and. unfold v_and. rewrite u_lit, edenot_lit, u_lit.
    change (255 mod 2 ^ 64) with (Z.ones 8). rewrite Z.land_ones by lia. change (2 ^ 8) with 256.
    pose proof (u_rng (edenot E D)). rewrite (Z.mod_small (u (edenot E D)) 256) by lia. apply Z.mod_small. lia.
Qed.

Lemma atoms_in : forall id l args, In args (atoms id l) -> In (ST.GA id args) l.
Proof.
  intros id l args H. unfold atoms in H. apply in_map_iff in H as ([i a] & <- & Hin). apply filter_In in Hin as [Hin E].
  cbn [ST.g_id] in E. apply Nat.eqb_eq in E. subst. exact Hin.
Qed.

Variable GP : nat -> list word -> (word -> option byte) -> Prop.

Lemma src_gdm : forall E m src id args, Nat.leb 20 id = true -> SG.gholds (gpx segs GP) E m src -> In args (atoms id src) ->
  gdm segs id (map (edenot E) args) m.
Proof.
  intros E m src id args Hid HS Hin. pose proof (proj1 (Forall_forall _ _) HS _ (atoms_in id src args Hin)) as X.
  cbn [ST.g_id ST.g_args] in X. unfold gpx in X. rewrite Hid in X. exact X.
Qed.

Lemma gdb_step_sound : forall E m src A N X X', SG.gholds (gpx segs GP) E m src -> gdb_step src A N X X' = true ->
  u (edenot E A) + u (edenot E N) < 2 ^ 64 ->
  exists dd, mbr segs m (u (edenot E A) + u (edenot E N)) = dd + 48 /\ 0 <= dd <= 9
             /\ u (edenot E X') = (10 * u (edenot E X) + dd) mod 2 ^ 64.
Proof.
  intros E m src A N X X' HS H Hw. unfold gdb_step in H. apply SLin.lex_exists in H as (b & Hin & Hb).
  destruct b as [|P [|D [|? ?]]]; try discriminate. destruct (leqx P (eadd A N)) eqn:HP; [|discriminate].
  pose proof (src_gdm E m src 21 [P; D] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2).
  rewrite (leqx_sound E _ _ HP), u_eadd, Z.mod_small in G1 by (pose proof (u_rng (edenot E A)); pose proof (u_rng (edenot E N)); lia).
  exists (u (edenot E D)). split; [exact G1|]. split; [pose proof (u_rng (edenot E D)); lia|]. exact (step_val_sound E X X' D Hb G2).
Qed.

Lemma gdbm_ok_sound : forall E m kn path lg P' D', know_ok segs E m kn -> scs_denot segs m E path -> log_flat E lg ->
  gdbm_ok segs kn path lg P' D' = true -> gdm segs 21 [edenot E P'; edenot E D'] (mem_denot E m lg).
Proof.
  intros E m kn path lg P' D' HK HP HL H. unfold gdbm_ok in H.
  destruct (SG.log_apart kn lg [(P', 0, ELit 1)]) eqn:HA; [|discriminate].
  destruct (rd_at_sound E m path P' _ HP H) as (v & Hf & Hb & Hb256).
  destruct (dig_known segs kn v) eqn:Hd; [|discriminate]. pose proof (dig_known_sound E m kn v HK Hb256 Hd) as Dg.
  pose proof (leqx_sound E _ _ Hf) as HD. unfold isdig in Dg.
  assert (UD : u (edenot E D') = u (edenot E (x1 v)) - 48).
  { rewrite HD, mkAlu_denot, alu_sub. unfold v_sub. rewrite u_lit, edenot_lit, u_lit. change (48 mod 2 ^ 64) with 48.
    apply Z.mod_small. lia. }
  cbn [gdm]. split; [|lia].
  rewrite <- (Z.add_0_r (u (edenot E P'))). rewrite (mbr_log E m kn lg P' (ELit 1) HK HL HA 0).
  - rewrite Z.add_0_r, <- Hb. lia.
  - rewrite edenot_lit, u_lit. cbn. lia.
  - pose proof (u_rng (edenot E P')). lia.
Qed.

Lemma gdm_ok_sound : forall E m kn src lg A' N' X', know_ok segs E m kn -> log_flat E lg -> SG.gholds (gpx segs GP) E m src ->
  gdm_ok segs kn src lg A' N' X' = true -> gdm segs 20 [edenot E A'; edenot E N'; edenot E X'] (mem_denot E m lg).
Proof.
  intros E m kn src lg A' N' X' HK HL HS H. unfold gdm_ok in H. cbn [gdm].
  destruct (kimp segs kn (KRange N' 0 0)) eqn:H0.
  { pose proof (kimp_range E m kn _ _ _ HK H0) as R0. rewrite (leqx_sound E _ _ H), edenot_lit, u_lit.
    assert (u (edenot E N') = 0) by lia. rewrite H1. pose proof (u_rng (edenot E A')).
    split; [lia|]. split; [lia|]. split; [intros i Hi; lia|]. reflexivity. }
  destruct (SG.log_apart kn lg [(A', 0, N')]) eqn:HA; [|discriminate].
  apply SLin.lex_exists in H as (a & Hin & Ha).
  destruct a as [|A [|N [|X [|? ?]]]]; try discriminate.
  destruct (leqx A' A) eqn:C1; [|discriminate]. destruct (leqx N' (e1 N)) eqn:C2; [|discriminate].
  destruct (kimp segs kn (KRange N 0 (2 ^ 20 - 1))) eqn:C3; [|discriminate].
  destruct (kimp segs kn (KRange A 0 (2 ^ 62))) eqn:C4; [|discriminate].
  pose proof (kimp_range E m kn _ _ _ HK C3) as RN. pose proof (kimp_range E m kn _ _ _ HK C4) as RA.
  pose proof (src_gdm E m src 20 [A; N; X] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2 & G3 & G4).
  destruct (gdb_step_sound E m src A N X X' HS Ha G2) as (dd & D1 & D2 & D3).
  pose proof (leqx_sound E _ _ C1) as EA.
  assert (UN : u (edenot E N') = u (edenot E N) + 1) by (rewrite (leqx_sound E _ _ C2), u_e1; apply Z.mod_small; lia).
  split; [lia|]. split; [rewrite EA; lia|]. split.
  - intros i Hi. rewrite (mbr_log E m kn lg A' N' HK HL HA i) by (rewrite ?EA; lia). rewrite EA.
    destruct (Z.eq_dec i (u (edenot E N))) as [->|Hne]; [unfold isdig; rewrite D1; lia|]. apply G3. lia.
  - rewrite (mdec_log E m kn lg A' N' (u (edenot E N') ) HK HL HA) by (rewrite ?EA; lia). rewrite EA, UN.
    rewrite mdec_step by lia. rewrite D1, D3, G4.
    replace (dd + 48 - 48) with dd by lia.
    rewrite <- Zplus_mod_idemp_l. rewrite Z.mul_mod_idemp_r by lia. rewrite Zplus_mod_idemp_l. reflexivity.
Qed.

Lemma gdzm_ok_sound : forall E m kn path src lg A' Z' N' X', know_ok segs E m kn -> scs_denot segs m E path -> log_flat E lg ->
  SG.gholds (gpx segs GP) E m src ->
  gdzm_ok segs kn path src lg A' Z' N' X' = true -> gdm segs 22 [edenot E A'; edenot E Z'; edenot E N'; edenot E X'] (mem_denot E m lg).
Proof.
  intros E m kn path src lg A' Z' N' X' HK HP HL HS H. unfold gdzm_ok in H. cbn [gdm].
  destruct (SG.log_apart kn lg [(A', 0, e1 N')]) eqn:HA; [|discriminate].
  pose proof (u_rng (edenot E A')) as RA'. pose proof (u_rng (edenot E N')) as RN'.
  assert (FR : forall i, 0 <= i <= u (edenot E N') -> u (edenot E A') + u (edenot E N') + 1 < 2 ^ 64 ->
            mbr segs (mem_denot E m lg) (u (edenot E A') + i) = mbr segs m (u (edenot E A') + i)).
  { intros i Hi Hw. apply (mbr_log E m kn lg A' (e1 N') HK HL HA i); [|lia]. rewrite u_e1, Z.mod_small by lia. lia. }
  assert (FD : forall n, 0 <= n <= u (edenot E N') -> u (edenot E A') + u (edenot E N') + 1 < 2 ^ 64 ->
            mdec segs (mem_denot E m lg) (u (edenot E A')) n = mdec segs m (u (edenot E A')) n).
  { intros n Hn Hw. apply (mdec_log E m kn lg A' (e1 N') n HK HL HA); [|lia]. rewrite u_e1, Z.mod_small by lia. lia. }
  match type of H with (if ?b then true else _) = true => destruct b eqn:B1 end.
  - (* [comment removed for export] *)
    clear H. apply SLin.lex_exists in B1 as (a & Hin & Ha).
    destruct a as [|A [|N [|X [|? ?]]]]; try discriminate.
    destruct (leqx A' A) eqn:C1; [|discriminate]. destruct (leqx N' (e1 N)) eqn:C2; [|discriminate].
    destruct (leqx Z' (ELit 1)) eqn:C3; [|discriminate].
    destruct (kimp segs kn (KRange N 0 (2 ^ 20 - 2))) eqn:C4; [|discriminate].
    destruct (kimp segs kn (KRange A 0 (2 ^ 62))) eqn:C5; [|discriminate].
    destruct (gdb_step src A N X X') eqn:C6; [|discriminate].
    destruct (rd_at path (e1 (eadd A N)) (nodig_known segs kn)) eqn:C7; [|discriminate].
    pose proof (kimp_range E m kn _ _ _ HK C4) as RN. pose proof (kimp_range E m kn _ _ _ HK C5) as RA.
    pose proof (src_gdm E m src 20 [A; N; X] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2 & G3 & G4).
    destruct (gdb_step_sound E m src A N X X' HS C6 G2) as (dd & D1 & D2 & D3).
    destruct (rd_at_sound E m path _ _ HP C7) as (v1 & N1 & V1 & V1b). pose proof (nodig_known_sound E m kn v1 HK V1b N1) as ND.
    destruct (rd_at_sound E m path _ _ HP Ha) as (v0 & Z0 & V0 & V0b). pose proof (zero_known_sound E m kn v0 HK Z0) as ZZ.
    pose proof (leqx_sound E _ _ C1) as EA.
    assert (UN : u (edenot E N') = u (edenot E N) + 1) by (rewrite (leqx_sound E _ _ C2), u_e1; apply Z.mod_small; lia).
    assert (UZ : u (edenot E Z') = 1) by (rewrite (leqx_sound E _ _ C3), edenot_lit, u_lit; reflexivity).
    assert (UP1 : u (edenot E (e1 (eadd A N))) = u (edenot E A) + u (edenot E N) + 1).
    { rewrite u_e1, u_eadd. rewrite (Z.mod_small (u (edenot E A) + u (edenot E N)) (2 ^ 64)) by lia. apply Z.mod_small. lia. }
    assert (W : u (edenot E A') + u (edenot E N') + 1 < 2 ^ 64) by (rewrite EA, UN; lia).
    rewrite UZ, UN. split; [lia|]. split; [rewrite EA; lia|]. split; [|split; [|split]].
    + intros i Hi. rewrite FR by lia. rewrite EA. assert (i = 0) by lia. subst i. rewrite Z.add_0_r, <- V0, ZZ. reflexivity.
    + intros i Hi. rewrite FR by lia. rewrite EA.
      destruct (Z.eq_dec i (u (edenot E N))) as [->|Hne]; [unfold isdig; rewrite D1; lia|]. apply G3. lia.
    + rewrite <- UN. rewrite FR by lia. rewrite EA, UN. replace (u (edenot E A) + (u (edenot E N) + 1)) with (u (edenot E A) + u (edenot E N) + 1) by lia.
      rewrite <- UP1, <- V1. exact ND.
    + rewrite <- UN. rewrite FD by lia. rewrite EA, UN. rewrite mdec_step by lia. rewrite D1, D3, G4.
      replace (dd + 48 - 48) with dd by lia.
      rewrite <- Zplus_mod_idemp_l. rewrite Z.mul_mod_idemp_r by lia. rewrite Zplus_mod_idemp_l. reflexivity.
  - (* [comment removed for export] *)
    apply SLin.lex_exists in H as (a & Hin & Ha).
    destruct a as [|A [|Z [|N [|X [|? ?]]]]]; try discriminate.
    destruct (leqx A' A) eqn:C1; [|discriminate]. destruct (leqx N' N) eqn:C2; [|discriminate].
    destruct (leqx X' X) eqn:C3; [|discriminate]. destruct (leqx Z' (e1 Z)) eqn:C4; [|discriminate].
    pose proof (src_gdm E m src 22 [A; Z; N; X] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
    destruct (rd_at_sound E m path _ _ HP Ha) as (v0 & Z0 & V0 & V0b). pose proof (zero_known_sound E m kn v0 HK Z0) as ZZ.
    pose proof (leqx_sound E _ _ C1) as EA. pose proof (leqx_sound E _ _ C2) as EN. pose proof (leqx_sound E _ _ C3) as EX.
    pose proof (u_rng (edenot E Z)) as RZ. pose proof (u_rng (edenot E A)) as RA.
    assert (UAZ : u (edenot E (eadd A Z)) = u (edenot E A) + u (edenot E Z)) by (rewrite u_eadd; apply Z.mod_small; pose proof (u_rng (edenot E A)); pose proof (u_rng (edenot E Z)); lia).
    assert (ZN : u (edenot E Z) < u (edenot E N)).
    { destruct (Z.eq_dec (u (edenot E Z)) (u (edenot E N))) as [Heq|Hne]; [|lia].
      exfalso. apply G5. rewrite <- Heq, <- UAZ, <- V0, ZZ. unfold isdig. lia. }
    assert (UZ : u (edenot E Z') = u (edenot E Z) + 1) by (rewrite (leqx_sound E _ _ C4), u_e1; apply Z.mod_small; lia).
    assert (W : u (edenot E A') + u (edenot E N') + 1 < 2 ^ 64) by (rewrite EA, EN; lia).
    assert (W' : u (edenot E A') + u (edenot E N) + 1 < 2 ^ 64) by (rewrite <- EN; exact W).
    rewrite UZ, EN, EX. split; [lia|]. split; [rewrite EA; lia|]. split; [|split; [|split]].
    + intros i Hi. rewrite FR by (rewrite ?EN; lia). rewrite EA.
      destruct (Z.eq_dec i (u (edenot E Z))) as [->|Hne]; [rewrite <- UAZ, <- V0, ZZ; reflexivity|]. apply G3. lia.
    + intros i Hi. rewrite FR by (rewrite ?EN; lia). rewrite EA. apply G4. exact Hi.
    + rewrite <- EN. rewrite FR by (rewrite ?EN; lia). rewrite EA, EN. exact G5.
    + rewrite <- EN. rewrite FD by (rewrite ?EN; lia). rewrite EA, EN. exact G6.
Qed.

Lemma atom_ok_sound : forall E m kn path src lg g, know_ok segs E m kn -> scs_denot segs m E path -> log_flat E lg ->
  SG.gholds (gpx segs GP) E m src ->
  atom_ok segs kn path src lg g = true -> gdm segs (ST.g_id g) (map (edenot E) (ST.g_args g)) (mem_denot E m lg).
Proof.
  intros E m kn path src lg [id args] HK HP HL HS H. unfold atom_ok in H. cbn [ST.g_id ST.g_args] in *.
  do 20 (destruct id as [|id]; [destruct args as [|? [|? [|? [|? ?]]]]; discriminate|]).
  destruct id as [|[|[|id]]].
  - destruct args as [|A' [|N' [|X' [|? ?]]]]; try discriminate. exact (gdm_ok_sound E m kn src lg A' N' X' HK HL HS H).
  - destruct args as [|P' [|D' [|? ?]]]; try discriminate. exact (gdbm_ok_sound E m kn path lg P' D' HK HP HL H).
  - destruct args as [|A' [|Z' [|N' [|X' [|? ?]]]]]; try discriminate. exact (gdzm_ok_sound E m kn path src lg A' Z' N' X' HK HP HL HS H).
  - destruct args as [|? [|? [|? [|? ?]]]]; discriminate.
Qed.

Lemma pow10_18 : 10 ^ 18 = 1000000000000000000.
Proof. reflexivity. Qed.

Lemma mdec_small : forall M a n, 0 <= n <= 18 -> (forall i, 0 <= i < n -> isdig (mbr segs M (a + i))) ->
  0 <= mdec segs M a n <= 999999999999999999.
Proof.
  intros M a n Hn HD. pose proof (mdec_bound segs M a n ltac:(lia) HD) as B.
  assert (10 ^ n <= 10 ^ 18) by (apply Z.pow_le_mono_r; lia). rewrite pow10_18 in *. lia.
Qed.

Lemma fact_ok_sound : forall E m kn src K M', know_ok segs E m kn -> SG.gholds (gpx segs GP) E m src ->
  fact_ok segs kn src K = true -> kentry_ok segs E M' K.
Proof.
  intros E m kn src K M' HK HS H. unfold fact_ok in H.
  destruct K as [| | | | |X' lo hi| | | |]; try discriminate.
  destruct (Z.eqb lo 0) eqn:L0; [|discriminate]. destruct (Z.eqb hi 999999999999999999) eqn:H0; [|discriminate].
  apply Z.eqb_eq in L0, H0. subst lo hi. cbn [kentry_ok].
  match type of H with (if ?b then true else _) = true => destruct b eqn:B1 end.
  - clear H. apply SLin.lex_exists in B1 as (a & Hin & Ha).
    destruct a as [|A [|N [|X [|? ?]]]]; try discriminate.
    pose proof (src_gdm E m src 20 [A; N; X] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2 & G3 & G4).
    destruct (leqx X' X) eqn:C1.
    + pose proof (kimp_range E m kn _ _ _ HK Ha) as RN. rewrite (leqx_sound E _ _ C1), G4.
      pose proof (mdec_small m (u (edenot E A)) (u (edenot E N)) RN G3) as B. rewrite Z.mod_small by lia. exact B.
    + destruct (kimp segs kn (KRange N 0 17)) eqn:C2; [|discriminate].
      pose proof (kimp_range E m kn _ _ _ HK C2) as RN.
      destruct (gdb_step_sound E m src A N X X' HS Ha G2) as (dd & D1 & D2 & D3).
      assert (HD : forall i, 0 <= i < u (edenot E N) + 1 -> isdig (mbr segs m (u (edenot E A) + i))).
      { intros i Hi. destruct (Z.eq_dec i (u (edenot E N))) as [->|Hne]; [unfold isdig; rewrite D1; lia|]. apply G3. lia. }
      pose proof (mdec_small m (u (edenot E A)) (u (edenot E N) + 1) ltac:(lia) HD) as B.
      rewrite mdec_step in B by lia. rewrite D1 in B. replace (dd + 48 - 48) with dd in B by lia.
      rewrite D3, G4. rewrite <- Zplus_mod_idemp_l. rewrite Z.mul_mod_idemp_r by lia. rewrite Zplus_mod_idemp_l.
      rewrite Z.mod_small by lia. exact B.
  - apply SLin.lex_exists in H as (a & Hin & Ha).
    destruct a as [|A [|Z [|N [|X [|? ?]]]]]; try discriminate.
    destruct (leqx X' X) eqn:C1; [|discriminate].
    pose proof (src_gdm E m src 22 [A; Z; N; X] eq_refl HS Hin) as G. cbn [map gdm] in G. destruct G as (G1 & G2 & G3 & G4 & G5 & G6).
    assert (L18 : u (edenot E N) - u (edenot E Z) <= 18).
    { unfold le18 in Ha. pose proof (u_rng (edenot E Z)). pose proof (u_rng (edenot E N)).
      destruct (kimp segs kn (KRange (mkAlu ALU_SUB N Z) 0 18)) eqn:C2.
      - pose proof (kimp_range E m kn _ _ _ HK C2) as R. rewrite mkAlu_denot, alu_sub in R. unfold v_sub in R. rewrite u_lit in R.
        rewrite Z.mod_small in R by lia. lia.
      - pose proof (kimp_range E m kn _ _ _ HK Ha) as R. rewrite mkAlu_denot, alu_sub in R. unfold v_sub in R. rewrite u_lit in R.
        rewrite u_eadd, edenot_lit, u_lit in R. change (18 mod 2 ^ 64) with 18 in R.
        rewrite (Z.mod_small (u (edenot E Z) + 18)) in R by lia.
        destruct (Z_lt_ge_dec (u (edenot E Z) + 18 - u (edenot E N)) 0) as [Lt|Ge].
        + rewrite <- (Z.mod_unique (u (edenot E Z) + 18 - u (edenot E N)) (2 ^ 64) (-1) (u (edenot E Z) + 18 - u (edenot E N) + 2 ^ 64)) in R
            by (try (left; lia); lia). lia.
        + lia. }
    pose proof (u_rng (edenot E Z)) as RZ0.
    pose proof (mdec_zeros segs m (u (edenot E A)) (u (edenot E Z)) (u (edenot E N)) ltac:(lia) G3) as ZE.
    assert (HD : forall i, 0 <= i < u (edenot E N) - u (edenot E Z) -> isdig (mbr segs m (u (edenot E A) + u (edenot E Z) + i))).
    { intros i Hi. replace (u (edenot E A) + u (edenot E Z) + i) with (u (edenot E A) + (u (edenot E Z) + i)) by lia. apply G4. lia. }
    pose proof (mdec_small m (u (edenot E A) + u (edenot E Z)) (u (edenot E N) - u (edenot E Z)) ltac:(lia) HD) as B.
    rewrite (leqx_sound E _ _ C1), G6, ZE, Z.mod_small by lia. exact B.
Qed.

Theorem gsplit_ok : forall g0, (forall c, g0 c = true -> SG.vc_holds segs GP c) ->
  forall c, gsplit segs g0 c = true -> SG.vc_holds segs (gpx segs GP) c.
Proof.
  intros g0 Hg0 c H. unfold gsplit in H.
  destruct (SLin.lall (atom_ok segs (SG.vc_kn c) (SG.vc_path c) (SG.vc_src c) (SG.vc_log c)) (List.filter mine (SG.vc_tgt c))) eqn:Ha;
    [|discriminate].
  pose proof (Hg0 _ H) as V. intros E m HK HP HL HS.
  assert (HS' : SG.gholds GP E m (List.filter (fun g => negb (mine g)) (SG.vc_src c))).
  { unfold SG.gholds in *. apply Forall_forall. intros g Hg. apply filter_In in Hg as [Hin Hnm].
    pose proof (proj1 (Forall_forall _ _) HS g Hin) as X. unfold gpx in X. unfold mine in Hnm.
    destruct (Nat.leb 20 (ST.g_id g)); [discriminate | exact X]. }
  destruct (V E m HK HP HL HS') as [T F]. cbn [SG.vc_tgt SG.vc_facts SG.vc_log] in T, F.
  split.
  - unfold SG.gholds in *. apply Forall_forall. intros g Hg. destruct (mine g) eqn:Hm.
    + pose proof (SLin.lall_forall _ _ _ Ha g (proj2 (filter_In _ _ _) (conj Hg Hm))) as Hok.
      unfold gpx. unfold mine in Hm. rewrite Hm.
      exact (atom_ok_sound E m (SG.vc_kn c) (SG.vc_path c) (SG.vc_src c) (SG.vc_log c) g HK HP HL HS Hok).
    + assert (Hin' : In g (List.filter (fun g => negb (mine g)) (SG.vc_tgt c))) by (apply filter_In; split; [exact Hg | rewrite Hm; reflexivity]).
      pose proof (proj1 (Forall_forall _ _) T g Hin') as X.
      unfold gpx. unfold mine in Hm. rewrite Hm. exact X.
  - unfold know_ok in *. apply Forall_forall. intros K HKin.
    destruct (fact_ok segs (SG.vc_kn c) (SG.vc_src c) K) eqn:Hf.
    + exact (fact_ok_sound E m (SG.vc_kn c) (SG.vc_src c) K _ HK HS Hf).
    + assert (Hin' : In K (List.filter (fun K => negb (fact_ok segs (SG.vc_kn c) (SG.vc_src c) K)) (SG.vc_facts c)))
        by (apply filter_In; split; [exact HKin | rewrite Hf; reflexivity]).
      exact (proj1 (Forall_forall _ _) F K Hin').
Qed.

End Sound.
End SDGok.
