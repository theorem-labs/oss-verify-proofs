(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec CatSim StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec Hoare ZStores RefMemcpyLib.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound VStepMemSound VStepMemSound2 VCert VContract VContractSound VContractSound2 VContractSound3 VContractSound4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Stdlib.micromega.Lia.lia ::= first [ flia2 | Zify.zify; xlia zchecker ].  (* [comment removed for export] *)
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

Notation B0 := (Z_to_bv 8 0).

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma const_stop_byte_spec o val sz : forall i phi z,
  const_stop_byte o val i sz phi = Some z ->
  exists i', (i <= i' < i + sz)%nat /\ z = o + Z.of_nat i' /\ phi <= z /\
             strtoul_cont (Z.land (Z.shiftr val (8 * Z.of_nat i')) 255) = false.
Proof.
  induction sz as [|sz IH]; intros i phi z H; cbn [const_stop_byte] in H; [discriminate|].
  destruct (Z.leb_spec phi (o + Z.of_nat i)); destruct (strtoul_cont (Z.land (Z.shiftr val (8 * Z.of_nat i)) 255)) eqn:Ec; cbn [andb negb] in H.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
  - injection H as <-. exists i. repeat split; auto; lia.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
  - destruct (IH _ _ _ H) as [i' (A&B&C&D)]. exists i'. repeat split; auto; lia.
Qed.

Lemma slot_stop_bytes_spec slots phi z :
  In z (slot_stop_bytes slots phi) ->
  exists o sz v i', In (o, (sz, Some v)) slots /\ lin_is_const v = true /\ (i' < Z.to_nat sz)%nat /\
    z = o + Z.of_nat i' /\ phi <= z /\
    strtoul_cont (Z.land (Z.shiftr (Z.land (lc v) (2 ^ (8 * sz) - 1)) (8 * Z.of_nat i')) 255) = false.
Proof.
  unfold slot_stop_bytes. rewrite in_flat_map. intros [[o [sz [v|]]] [Hin Hz]]; [|destruct Hz].
  destruct (lin_is_const v && (phi <=? o + sz - 1)) eqn:E; [|destruct Hz]. apply andb_prop in E as [Ec _].
  destruct (const_stop_byte o _ 0 (Z.to_nat sz) phi) as [z0|] eqn:Ecz; [|destruct Hz].
  destruct Hz as [<-|[]]. destruct (const_stop_byte_spec _ _ _ _ _ _ Ecz) as [i' (A&B&C&D)].
  exists o, sz, v, i'. repeat split; auto. lia.
Qed.

(* [comment removed for export] *)
Lemma word_to_le_bytes_8_of_bytes (bs : list byte) :
  length bs = 8%nat -> word_to_le_bytes 8 (le_bytes_to_word bs) = bs.
Proof.
  intros Hlen. unfold word_to_le_bytes, le_bytes_to_word. rewrite Z_to_bv_unsigned.
  rewrite (Z_to_le_bytes_wrap 8 64) by (cbn; lia).
  rewrite <- Hlen. apply Z_to_le_bytes_lez.
Qed.

Section CS5.
  Variable SEGS : list Segment.  Variable P : vparams.  Variable E : venv.
  Variable mem0 : word -> option byte.  Variable rom : word -> option byte.  Variable CI : cimg.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  Variable a_strtoul : Z.      (* [comment removed for export] *)
  Variable a_got : Z.          (* [comment removed for export] *)
  Variable a_guard : Z.        (* [comment removed for export] *)
  Variables ro1_lo ro1_hi ro2_lo ro2_hi : Z.   (* [comment removed for export] *)
  Variable ro_min : Z.         (* [comment removed for export] *)

  (* [comment removed for export] *)
  Hypothesis GOT_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= a_got /\ a_got + 8 <= phi.
  Hypothesis GOT_BYTES : rdn SEGS (fun _ => None) (wordZ a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_guard)).
  Hypothesis GUARD_SEG : exists lo hi, In (lo, hi) (vp_segs P) /\ lo <= a_guard /\ a_guard + 8 <= hi.
  Hypothesis RO1_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= ro1_lo /\ ro1_hi <= phi.
  Hypothesis RO2_PRISTINE : exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= ro2_lo /\ ro2_hi <= phi.
  Hypothesis CI_ERRNO : ci_errno CI = ci_tp CI - 164.
  Hypothesis CI_TP : ro_min + 164 <= ci_tp CI < 2 ^ 64.
  Hypothesis RO_MIN : 0 <= ro_min <= vp_splo P - vp_frame P.
  Hypothesis GUARD_ERR : a_guard + 8 <= ci_errno CI \/ ci_errno CI + 4 <= a_guard.
  Hypothesis SPHI8 : vp_sphi P + 8 < 2 ^ 64.

  (* [comment removed for export] *)
  Hypothesis STRTOUL : forall mem (s sp tp CAN : word) (str : list byte) (A : Z) regs (ret : word),
    rdn SEGS mem s (length str) = Some str ->
    0 <= A < Z.of_nat (length str) ->
    strtoul_cont (bv_unsigned (nth (Z.to_nat A) str B0)) = false ->
    bv_unsigned s + Z.of_nat (length str) < 2 ^ 64 - 8 ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned sp - 368)) 368 = true ->
    368 <= bv_unsigned sp < 2 ^ 64 ->
    ro_min <= bv_unsigned sp - 368 ->
    (bv_unsigned sp <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned sp - 368) ->
    store_ok SEGS mem (Z_to_bv 64 (bv_unsigned tp - 164)) 4 = true ->
    ro_min + 164 <= bv_unsigned tp ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= bv_unsigned tp - 164) ->
    (bv_unsigned tp - 164 + 4 <= bv_unsigned s \/ bv_unsigned s + Z.of_nat (length str) <= bv_unsigned tp - 164) ->
    rdn SEGS mem (Z_to_bv 64 a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_guard)) ->
    a_got + 8 <= bv_unsigned sp - 368 ->
    rdn SEGS mem (wordZ a_guard) 8 = Some (word_to_le_bytes 8 CAN) ->
    (a_guard + 8 <= bv_unsigned sp - 368 \/ bv_unsigned sp <= a_guard) ->
    (a_guard + 8 <= bv_unsigned tp - 164 \/ bv_unsigned tp - 164 + 4 <= a_guard) ->
    a_guard + 8 < 2 ^ 64 ->
    (forall x, (ro1_lo <= x < ro1_hi \/ ro2_lo <= x < ro2_hi) -> mem (Z_to_bv 64 x) = None) ->
    ret_ok ret -> getr regs 1%bv = ret -> getr regs 2%bv = sp -> getr regs 4%bv = tp ->
    getr regs 10%bv = s -> getr regs 11%bv = Z_to_bv 64 0 -> getr regs 12%bv = Z_to_bv 64 10 ->
    exists regs' mem',
      msteps SEGS (mkst regs (wordZ a_strtoul) mem rom) (mkst regs' ret mem' rom)
      /\ (forall x : reg, bv_unsigned x <> 0 -> ~ In (bv_unsigned x) CALLER_SAVED -> getr regs' x = getr regs x)
      /\ getr regs' 1%bv = getr regs 1%bv
      /\ frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 368), 368); (Z_to_bv 64 (bv_unsigned tp - 164), 4)].

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="PO SPHI8"] Lemma rdn_pristine mem a (n : nat) :
    env_ok P E -> MCP mem -> (exists plo phi, In (plo, phi) (vp_pristine P) /\ plo <= a /\ a + Z.of_nat n <= phi) ->
    rdn SEGS mem (wordZ a) n = rdn SEGS (fun _ => None) (wordZ a) n.
  Proof.
    intros HE (MF&MD&MP&MFM) [plo [phi (Hin&Q1&Q2)]]. pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    destruct (PP _ _ Hin) as [R0 R1].
    apply rdn_ext; [rewrite u_wordZ; lia|].
    intros x Hx. rewrite u_wordZ in Hx by lia. rewrite <- (wordZ_u x). apply (MP plo phi); [exact Hin|lia].
  Qed.

  (* [comment removed for export] *)
  #[using="PO GOT_PRISTINE GOT_BYTES SPHI8"] Lemma got_read mem : env_ok P E -> MCP mem ->
    rdn SEGS mem (Z_to_bv 64 a_got) 8 = Some (word_to_le_bytes 8 (wordZ a_guard)).
  Proof.
    intros HE HM. change (Z_to_bv 64 a_got) with (wordZ a_got). rewrite (rdn_pristine mem a_got 8 HE HM).
    - exact GOT_BYTES.
    - destruct GOT_PRISTINE as [plo [phi X]]. exists plo, phi. cbn [Z.of_nat Pos.of_succ_nat Pos.succ]. exact X.
  Qed.

  #[using="CI PO ro_min GUARD_SEG CI_ERRNO CI_TP RO_MIN SPHI8"] Lemma guard_read mem : env_ok P E -> MCP mem ->
    exists CAN : word, rdn SEGS mem (wordZ a_guard) 8 = Some (word_to_le_bytes 8 CAN).
  Proof.
    intros HE HM. pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB). pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    destruct GUARD_SEG as [lo [hi (Hin&Q1&Q2)]]. destruct (PS _ _ Hin) as (S0&S1&SB).
    destruct (rdn_bytes SEGS mem a_guard 8 ltac:(lia) ltac:(cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia)) as [bs [Hbs Hlen]].
    { intros k Hk. apply rdn1_any. apply SB. cbn [Z.of_nat Pos.of_succ_nat Pos.succ] in Hk. lia. }
    exists (le_bytes_to_word bs). rewrite (word_to_le_bytes_8_of_bytes bs Hlen). exact Hbs.
  Qed.

  #[using="PO SPHI8"] Lemma errno_store_ok mem a : env_ok P E -> MCP mem -> in_cells (vp_wcells P) a 4 = true ->
    store_ok SEGS mem (Z_to_bv 64 a) 4 = true /\
    exists f, In f (vp_fcells P) /\ fst f <= a /\ a + 4 <= fst f + snd f /\ 0 <= fst f /\ fst f + snd f <= vp_splo P - vp_frame P /\
              (forall lo hi, In (lo, hi) (vp_pristine P) -> hi <= fst f \/ fst f + snd f <= lo).
  Proof.
    intros HE HM Hc. pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB). pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    destruct (in_cells_sound _ _ _ Hc) as [c (Hcin&C1&C2)]. destruct (PW _ Hcin) as [f (Hf&F1&F2)].
    destruct (PF _ Hf) as (G1&G2&G3&G4).
    split.
    - change (Z_to_bv 64 a) with (wordZ a). change 4%nat with (Z.to_nat 4). apply store_ok_bytes; [lia|lia|].
      intros k Hk. apply (MC_cell_ok SEGS P E mem0 PO mem f); [exact HM|exact Hf|lia].
    - exists f. repeat split; auto; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="SEGS mem0 PO ro_min RO_MIN SPHI8"] Lemma cell_R_ok a n :
    in_cells (vp_wcells P) a n = true -> 0 <= n -> env_ok P E ->
    forall x, ~ outside x [(wordZ a, n)] ->
      ~ outside x (unit_regions P E) /\ ~ outside x (footprint P E) /\
      forall plo phi, In (plo, phi) (vp_pristine P) -> ~ (plo <= bv_unsigned x < phi).
  Proof.
    intros Hc Hn HE x Hx.
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    destruct (in_cells_sound _ _ _ Hc) as [c (Hcin&C1&C2)]. destruct (PW _ Hcin) as [f (Hf&F1&F2)].
    destruct (PF _ Hf) as (G1&G2&G3&G4).
    cbn [outside] in Hx. unfold in_rng in Hx. rewrite u_wordZ in Hx by lia.
    assert (Hin : a <= bv_unsigned x < a + n).
    { destruct (Z_le_gt_dec a (bv_unsigned x)); destruct (Z_lt_ge_dec (bv_unsigned x) (a + n)); first [lia | exfalso; apply Hx; split; [lia|exact I]]. }
    split; [|split].
    - unfold unit_regions. rewrite outside_app. intros [_ Hs].
      clear -Hs Hcin Hin C1 C2 F1 F2 G1 G2 E2 E12 P0 P1.
      unfold cells_regions in Hs. induction (vp_wcells P) as [|c0 t IH]; [destruct Hcin|]. cbn [map outside] in Hs. destruct Hs as [Hs1 Hs2].
      destruct Hcin as [->|Hcin]; [|exact (IH Hcin Hs2)]. apply Hs1. unfold in_rng. cbn [fst snd]. rewrite u_wordZ by lia. lia.
    - unfold footprint. cbn [outside]. intros [_ Hs].
      clear -Hs Hf Hin C1 C2 F1 F2 G1 G2 E2 E12 P0 P1.
      unfold cells_regions in Hs. induction (vp_fcells P) as [|c0 t IH]; [destruct Hf|]. cbn [map outside] in Hs. destruct Hs as [Hs1 Hs2].
      destruct Hf as [->|Hf]; [|exact (IH Hf Hs2)]. apply Hs1. unfold in_rng. cbn [fst snd]. rewrite u_wordZ by lia. lia.
    - intros plo phi Hp. destruct (G4 _ _ Hp); lia.
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma stop_byte_sound A nu regs mem phi stop :
    gammaP A nu regs mem ->
    min_opt (slot_stop_bytes (vs_slots A) phi
             ++ map fst (List.filter (fun f : Z * Z => Z.leb phi (fst f) && Z.eqb (fst f) (snd f)) (vs_nul A)))%list = Some stop ->
    exists b, phi <= stop /\ (- vp_frame P <= stop < 0) /\
              rdn SEGS mem (wordZ (e_sp0 E + stop)) 1 = Some [b] /\ strtoul_cont (bv_unsigned b) = false.
  Proof.
    intros HGm Hm. pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    destruct (min_opt_spec _ _ Hm) as [Hin _]. apply in_app_or in Hin as [Hin|Hin].
    - (* [comment removed for export] *)
      destruct (slot_stop_bytes_spec _ _ _ Hin) as [o [sz [v [i' (Hsl&Hc&Hi&Ez&Hphi&Hbyte)]]]].
      destruct (HSl _ _ _ Hsl) as [(R1&R2&R3) CH]. cbn [cell_holds] in CH. destruct CH as [bs [Hbs Hval]].
      pose proof (rdn_length _ _ _ _ _ Hbs) as Hlen.
      pose proof (rdn_nth SEGS mem (Z.to_nat sz) (wordZ (e_sp0 E + o)) bs i' Hbs Hi) as Hb.
      rewrite wordZ_add_nat in Hb. rewrite Ez. replace (e_sp0 E + (o + Z.of_nat i')) with (e_sp0 E + o + Z.of_nat i') by lia.
      exists (nth i' bs B0). split; [lia|]. split; [lia|]. split; [exact Hb|].
      rewrite (nth_byte_val bs i') by lia. rewrite Hval, (eval_is_const nu v Hc).
      change 255 with (2 ^ 8 - 1) in Hbyte. rewrite !land_lowmask, Z.shiftr_div_pow2 in Hbyte by lia.
      unfold zwrap. change 256 with (2 ^ 8). exact Hbyte.
    - (* [comment removed for export] *)
      apply in_map_iff in Hin as [[lo hi] [Elo Hin]]. cbn [fst] in Elo. subst lo.
      apply filter_In in Hin as [Hin Hb]. cbn [fst snd] in Hb. apply andb_prop in Hb as [Hle Heq].
      apply Z.leb_le in Hle. apply Z.eqb_eq in Heq. subst hi.
      destruct (HN _ _ Hin) as [z [b (Q1&Q2&Q3&Q4)]]. assert (z = stop) by lia. subst z.
      exists b. split; [lia|]. split; [lia|]. split; [exact Q3|]. rewrite Q4. reflexivity.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  #[using="Type"] Theorem strtoul_dead : contract_dead SEGS P E mem0 CI C_strtoul.
  Proof.
    intros A spoff nu regs mem Happ HGm. pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    cbn [contract_apply] in Happ. unfold c_strtoul, getA in Happ.
    destruct (get_reg A A1r) as [ee|]; [|discriminate]. destruct (get_reg A A2r) as [be|]; [|discriminate].
    destruct (negb (lin_is_const ee && _)); [discriminate|]. destruct (negb (lin_is_const be && _)); [discriminate|].
    destruct (get_reg A A0r) as [pe|]; [|discriminate]. destruct (negb (is_sp_rel pe)); [discriminate|].
    destruct (dead_lin A (lsub pe (lsym SP0))) eqn:Ed; [exact (dead_lin_false A nu _ HL Ed)|].
    destruct (bnd A _) as [[plo|] [phi|]]; try discriminate.
    destruct (min_opt _); [|discriminate].
    repeat (destruct (negb _); [discriminate|]). repeat (destruct (Z.ltb _ _); [discriminate|]).
    repeat (destruct (negb _); [discriminate|]). destruct (afresh _ _); discriminate.
  Qed.

  #[using="PO a_got a_guard ro1_lo ro1_hi ro2_lo ro2_hi ro_min GOT_PRISTINE GOT_BYTES GUARD_SEG RO1_PRISTINE RO2_PRISTINE CI_ERRNO CI_TP RO_MIN GUARD_ERR SPHI8 STRTOUL"] Theorem strtoul_post : contract_post SEGS P E mem0 rom CI C_strtoul a_strtoul.
  Proof.
    intros A spoff A1 v nu regs mem ra Happ HGm Hsp HKw Hret Hra.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12). pose proof PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    (* [comment removed for export] *)
    destruct HKw as [HKw|HKw]; [cbn in HKw; lia|]. cbn [contract_K] in HKw.
    destruct (in_ranges_sound _ _ _ HKw) as [klo [khi (HKin&HK1&HK2)]]. destruct (PR _ HKin) as [HK3 HK4]. cbn [fst snd] in HK3, HK4.
    destruct (sp_word SEGS P E mem0 PO A nu regs mem spoff HGm Hsp ltac:(lia)) as (R2&U1&U2).
    set (usp := e_sp0 E + spoff) in *.
    (* [comment removed for export] *)
    cbn [contract_apply] in Happ. unfold c_strtoul, getA in Happ.
    destruct (get_reg A A1r) as [ee|] eqn:Eee; [|discriminate].
    destruct (get_reg A A2r) as [be|] eqn:Ebe; [|discriminate].
    destruct (lin_is_const ee && (lc ee =? 0)) eqn:Cee; [|discriminate]. cbn [negb] in Happ.
    destruct (lin_is_const be && (lc be =? 10)) eqn:Cbe; [|discriminate]. cbn [negb] in Happ.
    apply andb_prop in Cee as [Cee Zee]. apply Z.eqb_eq in Zee. apply andb_prop in Cbe as [Cbe Zbe]. apply Z.eqb_eq in Zbe.
    destruct (get_reg A A0r) as [pe|] eqn:Epe; [|discriminate].
    destruct (is_sp_rel pe); [|discriminate]. cbn [negb] in Happ.
    destruct (dead_lin A (lsub pe (lsym SP0))) eqn:Ed; [discriminate|].
    pose proof (bnd_sound A nu (lsub pe (lsym SP0)) HL) as Hbd.
    destruct (bnd A (lsub pe (lsym SP0))) as [[plo|] [phi|]]; try discriminate.
    destruct Hbd as [Hplo Hphi]; cbn [fst snd lo_le hi_ge] in Hplo, Hphi. rewrite eval_lsub, eval_lsym, (nu_SP0 E nu HF) in Hplo, Hphi.
    match type of Happ with context [min_opt ?l] => destruct (min_opt l) as [stop|] eqn:Est; [|discriminate] end.
    destruct (Z.ltb_spec 0 (stop + 1)); [discriminate|].
    destruct (Z.ltb_spec plo spoff); [discriminate|].
    destruct (Z.ltb_spec (spoff - STRTOUL_FRAME) (- vp_frame P)); [discriminate|]. unfold STRTOUL_FRAME in *.
    destruct (in_cells (vp_wcells P) (ci_errno CI) 4) eqn:Ecell; [|discriminate]. cbn [negb] in Happ.
    destruct (get_reg A 4) as [te|] eqn:Ete; [|discriminate].
    destruct (lin_eqb te (lconst (ci_tp CI))) eqn:Etp; [|discriminate]. cbn [negb] in Happ.
    (* [comment removed for export] *)
    destruct (stop_byte_sound A nu regs mem phi stop HGm Est) as [bst (Sb1&Sb2&Sb3&Sb4)].
    set (p := eval nu pe) in *. set (ov := p - e_sp0 E) in *.
    set (L := stop + 1 - ov).
    destruct (rdn_bytes_vals SEGS mem p (Z.to_nat L) (fun j b => j = stop - ov -> b = bst) ltac:(lia) ltac:(lia)) as [str (Hstr&Lstr&Qstr)].
    { intros j Hj. destruct (Z.eq_dec j (stop - ov)) as [->|Hne].
      - exists bst. replace (p + (stop - ov)) with (e_sp0 E + stop) by lia. split; [exact Sb3|auto].
      - destruct (MC_frame_ok SEGS P E mem0 mem (p + j) HM) as [_ [bb Rb]]; [lia|]. exists bb. split; [exact Rb|intros; lia]. }
    (* [comment removed for export] *)
    assert (R10 : getr regs 10%bv = wordZ p).
    { apply (reg_word SEGS P E mem0 A nu regs mem 10%bv pe _ HGm); [vm_compute; lia|exact Epe|reflexivity|lia]. }
    assert (R11 : getr regs 11%bv = Z_to_bv 64 0).
    { apply (reg_word SEGS P E mem0 A nu regs mem 11%bv ee 0 HGm); [vm_compute; lia|exact Eee|rewrite (eval_is_const nu ee Cee); exact Zee|lia]. }
    assert (R12 : getr regs 12%bv = Z_to_bv 64 10).
    { apply (reg_word SEGS P E mem0 A nu regs mem 12%bv be 10 HGm); [vm_compute; lia|exact Ebe|rewrite (eval_is_const nu be Cbe); exact Zbe|lia]. }
    assert (R4 : getr regs 4%bv = wordZ (ci_tp CI)).
    { apply (reg_word SEGS P E mem0 A nu regs mem 4%bv te _ HGm); [vm_compute; lia|exact Ete|rewrite (lin_eqb_sound nu _ _ Etp); apply eval_lconst|lia]. }
    (* [comment removed for export] *)
    assert (STK : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (wordZ usp) - 368)) 368 = true).
    { rewrite u_wordZ by lia. change (Z_to_bv 64 (usp - 368)) with (wordZ (usp - 368)). change 368%nat with (Z.to_nat 368).
      apply store_ok_bytes; [lia|lia|]. intros j Hj. apply (MC_frame_ok SEGS P E mem0 mem _ HM). unfold usp. lia. }
    destruct (errno_store_ok mem (ci_errno CI) HE HM Ecell) as [ERR [f (Hf&F1&F2&F3&F4&F5)]].
    destruct (guard_read mem HE HM) as [CAN Hcan].
    destruct GUARD_SEG as [glo [ghi (Gin&G1&G2)]]. destruct (PS _ _ Gin) as (GS0&GS1&_).
    destruct GOT_PRISTINE as [tlo [thi (Tin&T1&T2)]]. destruct (PP _ _ Tin) as [T3 T4].
    (* [comment removed for export] *)
    destruct (STRTOUL mem (wordZ p) (wordZ usp) (wordZ (ci_tp CI)) CAN str (stop - ov) regs ra
                ltac:(rewrite Lstr; exact Hstr) ltac:(rewrite Lstr; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite (Qstr (Z.to_nat (stop - ov)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia)) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))); exact Sb4)
                ltac:(rewrite u_wordZ, Lstr; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia)) STK ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia)) ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); left; unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); rewrite <- CI_ERRNO; exact ERR)
                ltac:(rewrite u_wordZ; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); left; rewrite <- CI_ERRNO; unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite !u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); left; rewrite <- CI_ERRNO; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                (got_read mem HE HM) ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                Hcan ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); left; unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(rewrite u_wordZ by (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia); rewrite <- CI_ERRNO; exact GUARD_ERR) ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia))
                ltac:(intros x Hx; destruct HM as (_&_&MP&_);
                      destruct Hx as [Hx|Hx];
                      [destruct RO1_PRISTINE as [rlo [rhi (Rin&Ra&Rb)]]; exact (MP rlo rhi x Rin ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia)))
                      |destruct RO2_PRISTINE as [rlo [rhi (Rin&Ra&Rb)]]; exact (MP rlo rhi x Rin ltac:((ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hphi; @Sb1; @Lstr; @SPHI8; @E2; @Sb2; @E12; @HK1; @HK3; @Hplo; @H0; @HK2; @HK4; @U1; @RO_MIN; @CI_ERRNO; @CI_TP; @G1; @GS0; @F2; @F4; @G2; @GS1; @T2; @T4; @H1; @Hx; @Ra; @Rb]); lia)))])
                Hret Hra R2 R4 R10 R11 R12)
      as [regs' [mem' (RUN&HKr&Hra'&FM)]].
    rewrite !u_wordZ in FM by (ltac2:(LK.k [@SPHI8; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK2; @HK4; @U1; @Lstr; @CI_ERRNO; @CI_TP; @RO_MIN; @G1; @GS0]); lia). rewrite <- CI_ERRNO in FM.
    change (Z_to_bv 64 (usp - 368)) with (wordZ (usp - 368)) in FM. change (Z_to_bv 64 (ci_errno CI)) with (wordZ (ci_errno CI)) in FM.
    set (R := [(wordZ (usp - 368), 368); (wordZ (ci_errno CI), 4)]) in FM.
    assert (ROUT : forall a w, (a + w <= usp - 368 \/ usp <= a) -> (a + w <= ci_errno CI \/ ci_errno CI + 4 <= a) ->
                               0 <= a -> a + w <= 2 ^ 64 -> range_outside R a w).
    { intros a w X Y Z0 Z1 x Hx. subst R. cbn [outside]. unfold in_rng. rewrite !u_wordZ by (ltac2:(LK.k [@CI_ERRNO; @CI_TP; @SPHI8; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK2; @HK3; @HK4; @Lstr; @F2; @F4; @Hx; @RO_MIN; @GUARD_ERR; @H1; @G1; @G2; @GS0; @GS1; @X; @Y; @Z0; @Z1]); lia). repeat split; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK3; @Lstr; @F2; @F4; @G2; @GS1; @X; @Hx; @Hphi; @Sb1; @Y]); lia). }
    (* [comment removed for export] *)
    set (A1' := set_globs A (cm_kill (vs_globs A) (ci_errno CI) (ci_errno CI + 4))) in Happ.
    assert (L1 : lgamma A1' nu).
    { destruct HL as (LS&LC&LM&LV&(Q0&Q1&Q2&Q3&Q4&Q5)). split; [exact LS|]. split; [exact LC|]. split; [exact LM|]. split; [exact LV|].
      split; [exact Q0|]. split; [exact Q1|]. split; [exact Q2|]. split; [exact Q3|].
      split; [intros k w e Hin; apply cm_kill_sub in Hin; exact (Q4 _ _ _ Hin)|exact Q5]. }
    set (x := bv_unsigned (getr regs' 10%bv)).
    pose proof (bv_unsigned_in_range 64 (getr regs' 10%bv)) as Xr. unfold bv_modulus in Xr.
    pose proof (afresh_sound A1' nu (Some 0, Some (2 ^ 64 - 1)) x L1 ltac:(subst x; split; cbn [fst snd lo_le hi_ge]; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Lstr; @Xr]); lia))) as AF.
    destruct (afresh A1' (Some 0, Some (2 ^ 64 - 1))) as [v1 A2]. injection Happ as <- <-.
    destruct AF as [nu' (X1&L2&V2)].
    exists regs', mem', nu'.
    destruct (gamma_call_post SEGS P E mem0 rom PO A (contract_frame C_strtoul A2 spoff v1) nu nu' regs regs' mem mem' R
                HGm (proj1 X1) ltac:(destruct (contract_frame_shape C_strtoul A2 spoff v1) as (_&_&_&_&F5'&_); rewrite F5'; exact (proj1 (proj2 X1)))
                ltac:(apply lgamma_contract_frame; [exact L2|destruct v1; [exact (proj2 V2)|exact I]]))
      as [HG' FM'].
    - eapply (gamma_regs_contract_frame SEGS P E mem0 C_strtoul A A2 spoff v1 nu nu' regs regs'); try eassumption.
      + right. split; [exact HR|destruct HB as (_&_&RB&_); exact RB].
      + exact (proj1 X1).
      + destruct X1 as (_&_&(SR&_)). exact SR.
      + destruct v1 as [e1|]; [|exact I]. rewrite (proj1 V2). subst x. symmetry. apply zwrap_id. lia.
    - intros off' w' v' Hin. destruct (contract_frame_shape C_strtoul A2 spoff v1) as (F1'&_). rewrite F1' in Hin. cbn -[Z.sub] in Hin.
      pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D1. apply cm_kill_sub in Hin.
      destruct X1 as (_&_&(_&SS&_)). rewrite SS in Hin. cbn in Hin.
      left. split; [exact Hin|]. destruct (HSl _ _ _ Hin) as [(Ra&Rb&Rc) _].
      apply ROUT; unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Lstr; @Xr; @D1; @E2; @HK1; @HK3; @Hphi; @Sb1; @F2; @F4; @G2; @GS1; @Ra; @CI_ERRNO; @CI_TP; @RO_MIN; @GUARD_ERR; @E12; @G1; @GS0; @SPHI8; @HK2; @HK4; @Rc]); lia).
    - intros ga gw gv Hin. destruct (contract_frame_shape C_strtoul A2 spoff v1) as (_&F2'&_). rewrite F2' in Hin.
      destruct X1 as (_&_&(_&_&SG&_)). rewrite SG in Hin. cbn in Hin.
      pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin) as D1. apply cm_kill_sub in Hin.
      split; [exact Hin|]. destruct (HG _ _ _ Hin) as [(Ra&Rb&Rc) _]. apply ROUT; unfold usp; (ltac2:(LK.k [@E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @HK3; @Lstr; @Xr; @Rc; @D1; @Ra; @SPHI8; @HK2; @HK4; @H1; @F2; @F4; @G2; @GS1]); lia).
    - intros mlo mhi Hin. destruct (contract_frame_shape C_strtoul A2 spoff v1) as (_&_&F3'&_). apply F3' in Hin as [Hin W1]. cbn -[Z.sub] in Hin, W1.
      destruct X1 as (_&_&(_&_&_&SN&_)). rewrite SN in Hin. cbn in Hin.
      destruct (HN _ _ Hin) as [z [b (Q1&Q2&Q3&Q4)]]. right. exists z, b.
      split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
      rewrite <- Q3. apply (rdn_unchanged SEGS mem0 rom mem mem' R (e_sp0 E + z) 1 (proj1 FM)); [(ltac2:(LK.k [@CI_ERRNO; @CI_TP; @RO_MIN; @GUARD_ERR; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK3; @Lstr; @F2; @F4; @G1; @G2; @GS0; @GS1; @Xr; @Q1; @Q2; @SPHI8; @Hplo; @Hphi; @H0; @Sb1; @Sb2]); lia)|(ltac2:(LK.k [@CI_ERRNO; @CI_TP; @RO_MIN; @GUARD_ERR; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @HK1; @HK3; @Lstr; @F2; @F4; @G1; @G2; @GS0; @GS1; @Xr; @Q1; @Q2; @SPHI8; @Hplo; @Hphi; @H0; @Sb1; @Sb2]); lia)|].
      apply ROUT; unfold usp; (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @Lstr; @Xr; @W1; @Q1; @E2; @HK1; @HK3; @F2; @F4; @G2; @GS1; @Q2; @CI_ERRNO; @CI_TP; @RO_MIN; @GUARD_ERR; @E12; @G1; @GS0; @SPHI8; @Hplo; @Hphi; @H0; @Sb1; @Sb2]); lia).
    - exact FM.
    - intros y Hy. destruct (not_outside_2 y _ _ Hy) as [Hy1|Hy2].
      + apply (stack_R_ok SEGS P E mem0 PO (spoff - 368) klo khi 368); auto; try (ltac2:(LK.k [@E3; @E4; @E5; @E7; @E8; @E9; @E11; @HK1; @Lstr; @Xr; @HK2]); lia).
        * exists (klo, khi). cbn [fst snd]. split; [exact HKin|lia].
        * replace (e_sp0 E + (spoff - 368)) with (usp - 368) by (unfold usp; lia). exact Hy1.
      + apply (cell_R_ok (ci_errno CI) 4 Ecell ltac:(lia) HE y Hy2).
    - split; [exact RUN|]. split; [exact HG'|]. split; [rewrite Hra'; exact Hra|].
      split; [exact (proj1 X1)|]. split; [|exact FM'].
      destruct (contract_frame_shape C_strtoul A2 spoff v1) as (_&_&_&_&F5'&_); rewrite F5'. exact (proj1 (proj2 X1)).
  Qed.
End CS5.
