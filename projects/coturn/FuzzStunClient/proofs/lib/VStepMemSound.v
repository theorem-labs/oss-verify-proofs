(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Bool Lia String.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec StoreOk.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import Frame.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import SeqExec.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib Require Import VLinalg VWord2 VState VLogic VAbs VAbsSound VAbsSound2 VAbsSound3 VStep VStepMem VGamma VStepSound.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import LiaKeep.  (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_wordZ a : 0 <= a < 2 ^ 64 -> bv_unsigned (wordZ a) = a.
Proof. intros. unfold wordZ. rewrite u_Z_to_bv64. apply zwrap_id. lia. Qed.

Lemma wordZ_u (x : word) : wordZ (bv_unsigned x) = x.
Proof. unfold wordZ. apply Z_to_bv_bv_unsigned. Qed.

Lemma wordZ_add1 a : 0 <= a -> a + 1 < 2 ^ 64 -> (wordZ a + 1)%bv = wordZ (a + 1).
Proof.
  intros. apply bv_eq. rewrite u_add1 by (rewrite u_wordZ; lia). rewrite !u_wordZ by lia. reflexivity.
Qed.

Lemma wordZ_eq_u (x : word) a : bv_unsigned x = a -> x = wordZ a.
Proof. intros <-. symmetry. apply wordZ_u. Qed.

Lemma of_to_nat_max w : Z.of_nat (Z.to_nat w) = Z.max 0 w.
Proof. destruct w; [reflexivity|rewrite Z2Nat.id by lia; lia|rewrite Z2Nat.inj_neg; lia]. Qed.

Section MemFacts.
  Variable SEGS : list Segment.

  Lemma rdn_1 mem (a : word) :
    rdn SEGS mem a 1 = match (match mem a with Some b => Some b | None => seg_rom SEGS a end) with
                       | Some b => Some [b] | None => None end.
  Proof. cbn [rdn]. destruct (match mem a with Some b => Some b | None => seg_rom SEGS a end); reflexivity. Qed.

  Lemma rdn1_grows m m' (a : word) :
    mem_grows m m' -> (exists b, rdn SEGS m a 1 = Some [b]) -> exists b, rdn SEGS m' a 1 = Some [b].
  Proof.
    intros Hg [b Hb]. rewrite rdn_1 in Hb |- *.
    destruct (m' a) as [b'|] eqn:E'; [eauto|].
    destruct (m a) as [b0|] eqn:E0.
    - exfalso. apply (Hg a); [rewrite E0; discriminate|exact E'].
    - destruct (seg_rom SEGS a); [eauto|discriminate].
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_bytes mem a n :
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall k, 0 <= k < Z.of_nat n -> exists b, rdn SEGS mem (wordZ (a + k)) 1 = Some [b]) ->
    exists bs, rdn SEGS mem (wordZ a) n = Some bs /\ length bs = n.
  Proof.
    revert a. induction n as [|n IH]; intros a Ha Hn Hk.
    - exists []. split; reflexivity.
    - destruct (Hk 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb. rewrite rdn_1 in Hb.
      cbn [rdn].
      destruct (match mem (wordZ a) with Some b0 => Some b0 | None => seg_rom SEGS (wordZ a) end) as [b0|]; [|discriminate].
      inversion Hb; subst.
      destruct n as [|n'].
      + exists [b]. split; reflexivity.
      + destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as [bs [Hbs Hlen]].
        { intros k Hk'. replace (a + 1 + k) with (a + (1 + k)) by lia. apply Hk. lia. }
        exists (b :: bs). rewrite wordZ_add1 by lia. rewrite Hbs. split; [reflexivity|cbn; lia].
  Qed.

  Lemma store_ok_bytes mem a n :
    0 <= a -> a + Z.of_nat n <= 2 ^ 64 ->
    (forall k, 0 <= k < Z.of_nat n -> store_ok SEGS mem (wordZ (a + k)) 1 = true) ->
    store_ok SEGS mem (wordZ a) n = true.
  Proof.
    revert a. induction n as [|n IH]; intros a Ha Hn Hk; [reflexivity|].
    pose proof (Hk 0 ltac:(lia)) as H0. rewrite Z.add_0_r in H0. cbn [store_ok] in H0 |- *.
    destruct (wview SEGS mem (wordZ a)); [|discriminate].
    destruct n as [|n']; [reflexivity|].
    rewrite wordZ_add1 by lia. apply IH; [lia|lia|].
    intros k Hk'. replace (a + 1 + k) with (a + (1 + k)) by lia. apply Hk. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma store_ok_any mem (a : word) : store_ok SEGS (fun _ => None) a 1 = true -> store_ok SEGS mem a 1 = true.
  Proof.
    intros H. eapply store_ok_mono; [|exact H]. intros x Hx. exfalso. apply Hx. reflexivity.
  Qed.

  Lemma rdn1_any mem (a : word) : (exists b, rdn SEGS (fun _ => None) a 1 = Some [b]) -> exists b, rdn SEGS mem a 1 = Some [b].
  Proof. apply rdn1_grows. intros x Hx. exfalso. apply Hx. reflexivity. Qed.
End MemFacts.

(* [comment removed for export] *)
(* [comment removed for export] *)

Definition params_ok (SEGS : list Segment) (P : vparams) : Prop :=
  0 <= vp_frame P /\ vp_sphi P < 2 ^ 64 /\
  (* [comment removed for export] *)
  (forall lo hi, In (lo, hi) (vp_segs P) ->
     0 <= lo /\ hi <= vp_splo P - vp_frame P /\
     forall a, lo <= a < hi -> exists b, rdn SEGS (fun _ => None) (wordZ a) 1 = Some [b]) /\
  (* [comment removed for export] *)
  (forall c, In c (vp_fcells P) ->
     0 <= fst c /\ fst c + snd c <= vp_splo P - vp_frame P /\
     (forall a, fst c <= a < fst c + snd c ->
        store_ok SEGS (fun _ => None) (wordZ a) 1 = true /\ exists b, rdn SEGS (fun _ => None) (wordZ a) 1 = Some [b]) /\
     (forall lo hi, In (lo, hi) (vp_pristine P) -> hi <= fst c \/ fst c + snd c <= lo)) /\
  (* [comment removed for export] *)
  (forall c, In c (vp_wcells P) -> exists f, In f (vp_fcells P) /\ fst f <= fst c /\ fst c + snd c <= fst f + snd f) /\
  (forall r, In r (vp_wstack P) -> - vp_frame P <= fst r /\ snd r <= 0) /\
  (* [comment removed for export] *)
  (forall lo hi, In (lo, hi) (vp_pristine P) -> 0 <= lo /\ hi <= vp_splo P - vp_frame P) /\
  (* [comment removed for export] *)
  (forall a b, 0 < a -> pm_get (Z.to_pos a) (vp_rom P) = Some b ->
     in_ranges (vp_pristine P) a 1 = true /\
     exists bb : byte, seg_rom SEGS (wordZ a) = Some bb /\ bv_unsigned bb = b).

Lemma in_ranges_sound l a n : in_ranges l a n = true -> exists lo hi, In (lo, hi) l /\ lo <= a /\ a + n <= hi.
Proof.
  unfold in_ranges. rewrite existsb_exists. intros [[lo hi] [Hin Hb]]. simpl in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
Qed.

Lemma in_cells_sound l a n : in_cells l a n = true -> exists c, In c l /\ fst c <= a /\ a + n <= fst c + snd c.
Proof.
  unfold in_cells. rewrite existsb_exists. intros [[ca cl] [Hin Hb]]. simpl in Hb.
  apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. exists (ca, cl); simpl; eauto.
Qed.

Section Sound.
  Variable SEGS : list Segment.
  Variable P : vparams.
  Variable E : venv.
  Variable mem0 : word -> option byte.
  Hypothesis PO : params_ok SEGS P.

  Notation gammaP := (gamma SEGS P E mem0).
  Notation MCP := (MC SEGS P E mem0).

  (* [comment removed for export] *)
  Definition writable_range (a len : Z) : Prop :=
    (e_sp0 E - vp_frame P <= a /\ a + len <= e_sp0 E /\
       exists r, In r (vp_wstack P) /\ e_sp0 E + fst r <= a /\ a + len <= e_sp0 E + snd r)
    \/ (exists c, In c (vp_wcells P) /\ fst c <= a /\ a + len <= fst c + snd c).

  Lemma writable_fcell a len c :
    In c (vp_wcells P) -> fst c <= a -> a + len <= fst c + snd c ->
    exists f, In f (vp_fcells P) /\ fst f <= a /\ a + len <= fst f + snd f.
  Proof.
    intros Hc H1 H2. destruct PO as (_&_&_&_&WC&_). destruct (WC _ Hc) as [f (Hf&F1&F2)]. exists f. split; auto. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma MC_frame_ok mem a : MCP mem -> e_sp0 E - vp_frame P <= a < e_sp0 E ->
    store_ok SEGS mem (wordZ a) 1 = true /\ exists b, rdn SEGS mem (wordZ a) 1 = Some [b].
  Proof. intros (F&_) Ha. exact (F a Ha). Qed.

  Lemma MC_cell_ok mem f a : MCP mem -> In f (vp_fcells P) -> fst f <= a < fst f + snd f ->
    store_ok SEGS mem (wordZ a) 1 = true /\ exists b, rdn SEGS mem (wordZ a) 1 = Some [b].
  Proof.
    intros HM Hf Ha. destruct PO as (_&_&_&FC&_). destruct (FC _ Hf) as (_&_&B&_).
    destruct (B a Ha) as [S1 R1]. split; [now apply store_ok_any|now apply rdn1_any].
  Qed.

  (* [comment removed for export] *)
  Lemma MC_wbytes mem (a : Z) (bs : list byte) :
    env_ok P E -> MCP mem -> writable_range a (Z.of_nat (length bs)) -> 0 < Z.of_nat (length bs) ->
    MCP (wbytes mem (wordZ a) bs)
    /\ frame_mod mem (wbytes mem (wordZ a) bs) (unit_regions P E)
    /\ 0 <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64.
  Proof.
    intros HE HM HW Hlen.
    destruct PO as (P0&P1&PS&PF&PW&PR&PP&PB).
    destruct HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    assert (Hrange : 0 <= a /\ a + Z.of_nat (length bs) <= 2 ^ 64 /\
                     (forall lo hi x, In (lo, hi) (vp_pristine P) -> lo <= x < hi -> ~ (a <= x < a + Z.of_nat (length bs)))).
    { destruct HW as [(W1&W2&_)|[c (Hc&W1&W2)]].
      - split; [lia|]. split; [lia|]. intros lo hi x Hp Hx. destruct (PP _ _ Hp). lia.
      - destruct (writable_fcell _ _ _ Hc W1 W2) as [f (Hf&F1&F2)]. destruct (PF _ Hf) as (G1&G2&_&G4).
        split; [lia|]. split; [lia|]. intros lo hi x Hp Hx. destruct (G4 _ _ Hp); lia. }
    destruct Hrange as (Ha0&Ha1&Hpr).
    assert (Hua : bv_unsigned (wordZ a) = a) by (apply u_wordZ; lia).
    pose proof (wbytes_grows bs mem (wordZ a)) as Hg.
    assert (FM : frame_mod mem (wbytes mem (wordZ a) bs) [(wordZ a, Z.of_nat (length bs))]).
    { apply frame_mod_wbytes. rewrite Hua. lia. }
    destruct HM as (MF&MD&MP&MFM).
    split; [|split; [|split; [exact Ha0|exact Ha1]]].
    - split; [|split; [|split]].
      + intros x Hx. destruct (MF x Hx) as [S1 R1]. split; [eapply store_ok_mono; eauto|eapply rdn1_grows; eauto].
      + intros i Hi. eapply rdn1_grows; eauto.
      + intros lo hi x Hp Hx. rewrite <- (MP lo hi x Hp Hx). apply wbytes_outside; [|rewrite Hua; lia].
        unfold in_rng. rewrite Hua, u_wordZ by (destruct (PP _ _ Hp); lia). intros C. apply (Hpr lo hi x Hp Hx). lia.
      + eapply frame_mod_trans_same; [exact MFM|]. eapply frame_mod_weaken; [|exact FM].
        intros x Hout. cbn [outside]. split; [|exact I].
        unfold footprint in Hout. cbn [outside] in Hout. destruct Hout as [Hstk Hcells].
        unfold in_rng in *. rewrite Hua. rewrite u_wordZ in Hstk by lia.
        destruct HW as [(W1&W2&_)|[c (Hc&W1&W2)]]; [lia|].
        destruct (writable_fcell _ _ _ Hc W1 W2) as [f (Hf&F1&F2)]. destruct (PF _ Hf) as (G1&G2&_).
        assert (Ho : ~ in_rng x (wordZ (fst f)) (snd f)).
        { clear -Hcells Hf. unfold cells_regions in Hcells. induction (vp_fcells P) as [|c0 t IH]; [destruct Hf|].
          cbn [map outside] in Hcells. destruct Hcells as [H1 H2]. destruct Hf as [->|Hf]; auto. }
        unfold in_rng in Ho. rewrite u_wordZ in Ho by lia. lia.
    - eapply frame_mod_weaken; [|exact FM]. intros x Hout. cbn [outside]. split; [|exact I].
      unfold unit_regions in Hout. rewrite outside_app in Hout. destruct Hout as [Hs Hc0].
      unfold in_rng. rewrite Hua.
      destruct HW as [(W1&W2&[r (Hr&R1&R2)])|[c (Hc&W1&W2)]].
      + assert (Ho : ~ in_rng x (wordZ (e_sp0 E + fst r)) (snd r - fst r)).
        { clear -Hs Hr. induction (vp_wstack P) as [|r0 t IH]; [destruct Hr|].
          cbn [map outside] in Hs. destruct Hs as [H1 H2]. destruct Hr as [->|Hr]; auto. }
        unfold in_rng in Ho. destruct (PR _ Hr). rewrite u_wordZ in Ho by lia. lia.
      + assert (Ho : ~ in_rng x (wordZ (fst c)) (snd c)).
        { clear -Hc0 Hc. rename Hc0 into Hs. unfold cells_regions in Hs. induction (vp_wcells P) as [|c0 t IH]; [destruct Hc|].
          cbn [map outside] in Hs. destruct Hs as [H1 H2]. destruct Hc as [->|Hc]; auto. }
        destruct (PW _ Hc) as [f (Hf&F1&F2)]. destruct (PF _ Hf) as (G1&G2&_).
        unfold in_rng in Ho. rewrite u_wordZ in Ho by lia. lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma classify_not_dead A nu addr n st : lgamma A nu -> classify P A addr n st = CDead -> False.
  Proof.
    intros HL. unfold classify.
    pose proof (bnd_dead_sound A nu (lsub addr (lsym SP0)) HL) as D1.
    pose proof (bnd_dead_sound A nu (lsub addr (lsym DATA)) HL) as D2.
    destruct (Z.eqb (lcoef addr SP0) 1 && Z.eqb (lcoef addr DATA) 0).
    - rewrite D1. destruct (negb (qge _ _ _)); [discriminate|]. destruct (negb (qle _ _ _)); [discriminate|].
      pose proof (bnd_sound A nu (lsub addr (lsym SP0)) HL) as Hb.
      destruct (bnd A (lsub addr (lsym SP0))) as [[lo|] [hi|]]; try discriminate.
      destruct (itv_empty (Some lo, Some hi)) eqn:Ee; [intros _; exact (itv_empty_sound _ _ Ee Hb)|].
      destruct (st && _); discriminate.
    - destruct (Z.eqb (lcoef addr DATA) 1 && Z.eqb (lcoef addr SP0) 0).
      + destruct st; [discriminate|]. rewrite D2. destruct (negb (qge _ _ _)); [discriminate|].
        destruct (negb (qle _ _ _)); discriminate.
      + destruct (negb _); [discriminate|].
        pose proof (bnd_sound A nu addr HL) as Hb.
        destruct (negb (lin_is_const addr) && itv_empty (bnd A addr)) eqn:Ee.
        { apply andb_prop in Ee as [_ Ee]. intros _. exact (itv_empty_sound _ _ Ee Hb). }
        destruct (bnd A addr) as [[lo|] [hi|]]; try discriminate. destruct st; destruct (in_cells _ _ _) || idtac; destruct (in_ranges _ _ _) || idtac; discriminate.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma addr_of_sound A nu regs mem (rs1 : reg) imm addr :
    gammaP A nu regs mem -> addr_of A (rz rs1) imm = Some addr ->
    lin_below addr (vs_next A) = true /\
    bv_unsigned (v_addi (getr regs rs1) imm) = zwrap 64 (eval nu addr).
  Proof.
    intros HGm Ha. unfold addr_of in Ha.
    pose proof (gamma_get_reg SEGS P E mem0 A nu regs mem rs1 HGm) as [Wa Ba].
    destruct (get_reg A (rz rs1)) as [e|]; [|discriminate]. inversion Ha; subst; clear Ha.
    split; [apply anorm_below, lin_below_laddc; exact Ba|].
    unfold v_addi. rewrite u_Z_to_bv64, (anorm_sound A nu) by (eapply gamma_lgamma; eauto).
    rewrite eval_laddc, (wval_some _ _ _ Wa). apply zwrap_add_l. lia.
  Qed.

  Lemma nu_SP0 nu : gamma_fix E nu -> nu SP0 = e_sp0 E.
  Proof. intros H. apply H. reflexivity. Qed.
  Lemma nu_DATA nu : gamma_fix E nu -> nu DATA = e_data E.
  Proof. intros H. apply H. reflexivity. Qed.
  Lemma nu_SIZE nu : gamma_fix E nu -> nu SIZE = e_size E.
  Proof. intros H. apply H. reflexivity. Qed.

  Lemma classify_stack_sound A nu addr n st off lo hi :
    lgamma A nu -> gamma_fix E nu -> 0 < n ->
    classify P A addr n st = COk (RStack off lo hi) ->
    off = lsub addr (lsym SP0) /\
    eval nu addr = e_sp0 E + eval nu off /\ lo <= eval nu off <= hi /\
    - vp_frame P <= eval nu off /\ eval nu off + n <= 0 /\
    (st = true -> in_ranges (vp_wstack P) lo (hi - lo + n) = true).
  Proof.
    intros HL HF Hn. unfold classify.
    destruct (Z.eqb (lcoef addr SP0) 1 && Z.eqb (lcoef addr DATA) 0).
    - destruct (qge A (lsub addr (lsym SP0)) (- vp_frame P)) eqn:Q1; cbn [negb]; [|destruct (bnd_dead _ _); discriminate].
      destruct (qle A (lsub addr (lsym SP0)) (- n)) eqn:Q2; cbn [negb]; [|destruct (bnd_dead _ _); discriminate].
      pose proof (qge_sound A nu _ _ HL Q1) as G1. pose proof (qle_sound A nu _ _ HL Q2) as G2.
      pose proof (bnd_sound A nu (lsub addr (lsym SP0)) HL) as Hb.
      destruct (bnd A (lsub addr (lsym SP0))) as [[lo'|] [hi'|]]; try discriminate.
      destruct (itv_empty _); [discriminate|].
      destruct (st && negb (in_ranges (vp_wstack P) lo' (hi' - lo' + n))) eqn:Ew; [discriminate|].
      intros X; inversion X; subst; clear X.
      destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
      rewrite eval_lsub, eval_lsym, (nu_SP0 nu HF) in *.
      split; [reflexivity|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
      intros ->. cbn [andb] in Ew. destruct (in_ranges _ _ _); [reflexivity|discriminate].
    - destruct (Z.eqb (lcoef addr DATA) 1 && Z.eqb (lcoef addr SP0) 0).
      + destruct st; [discriminate|]. destruct (negb _); [destruct (bnd_dead _ _); discriminate|].
        destruct (negb _); [destruct (bnd_dead _ _); discriminate|discriminate].
      + destruct (negb _); [discriminate|]. destruct (negb _ && _); [discriminate|].
        destruct (bnd A addr) as [[l|] [h|]]; try discriminate. destruct st; [destruct (in_cells _ _ _)|destruct (in_ranges _ _ _)]; discriminate.
  Qed.

  Lemma classify_data_sound A nu addr n st off :
    lgamma A nu -> gamma_fix E nu ->
    classify P A addr n st = COk (RData off) ->
    st = false /\ eval nu addr = e_data E + eval nu off /\ 0 <= eval nu off /\ eval nu off + n <= e_size E.
  Proof.
    intros HL HF. unfold classify.
    destruct (Z.eqb (lcoef addr SP0) 1 && Z.eqb (lcoef addr DATA) 0).
    { destruct (negb _); [destruct (bnd_dead _ _); discriminate|]. destruct (negb _); [destruct (bnd_dead _ _); discriminate|].
      destruct (bnd A _) as [[l|] [h|]]; try discriminate. destruct (itv_empty _); [discriminate|]. destruct (st && _); discriminate. }
    destruct (Z.eqb (lcoef addr DATA) 1 && Z.eqb (lcoef addr SP0) 0).
    - destruct st; [discriminate|].
      destruct (qge A (lsub addr (lsym DATA)) 0) eqn:Q1; cbn [negb]; [|destruct (bnd_dead _ _); discriminate].
      destruct (qle A (lsub (laddc (lsub addr (lsym DATA)) n) (lsym SIZE)) 0) eqn:Q2; cbn [negb]; [|destruct (bnd_dead _ _); discriminate].
      intros X; inversion X; subst; clear X.
      pose proof (qge_sound A nu _ _ HL Q1) as G1. pose proof (qle_sound A nu _ _ HL Q2) as G2.
      rewrite eval_lsub, eval_lsym, (nu_DATA nu HF) in G1.
      rewrite eval_lsub, eval_laddc, eval_lsub, !eval_lsym, (nu_DATA nu HF), (nu_SIZE nu HF) in G2.
      split; [reflexivity|]. rewrite eval_lsub, eval_lsym, (nu_DATA nu HF). lia.
    - destruct (negb _); [discriminate|]. destruct (negb _ && _); [discriminate|].
      destruct (bnd A addr) as [[l|] [h|]]; try discriminate. destruct st; [destruct (in_cells _ _ _)|destruct (in_ranges _ _ _)]; discriminate.
  Qed.

  Lemma classify_img_sound A nu addr n st lo hi :
    lgamma A nu ->
    classify P A addr n st = COk (RImg lo hi) ->
    lo <= eval nu addr <= hi /\
    (st = true -> in_cells (vp_wcells P) lo (hi - lo + n) = true) /\
    (st = false -> in_ranges (vp_segs P) lo (hi - lo + n) = true).
  Proof.
    intros HL. unfold classify.
    destruct (Z.eqb (lcoef addr SP0) 1 && Z.eqb (lcoef addr DATA) 0).
    { destruct (negb _); [destruct (bnd_dead _ _); discriminate|]. destruct (negb _); [destruct (bnd_dead _ _); discriminate|].
      destruct (bnd A _) as [[l|] [h|]]; try discriminate. destruct (itv_empty _); [discriminate|]. destruct (st && _); discriminate. }
    destruct (Z.eqb (lcoef addr DATA) 1 && Z.eqb (lcoef addr SP0) 0).
    { destruct st; [discriminate|]. destruct (negb _); [destruct (bnd_dead _ _); discriminate|].
      destruct (negb _); [destruct (bnd_dead _ _); discriminate|discriminate]. }
    destruct (negb _); [discriminate|]. destruct (negb _ && _); [discriminate|].
    pose proof (bnd_sound A nu addr HL) as Hb.
    destruct (bnd A addr) as [[l|] [h|]]; try discriminate. destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
    destruct st.
    - destruct (in_cells (vp_wcells P) l (h - l + n)) eqn:Ec; [|discriminate]. intros X; inversion X; subst; clear X.
      split; [lia|]. split; [auto|discriminate].
    - destruct (in_ranges (vp_segs P) l (h - l + n)) eqn:Ec; [|discriminate]. intros X; inversion X; subst; clear X.
      split; [lia|]. split; [discriminate|auto].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  Lemma msize_pos sz : 0 < msize_z sz <= 8.
  Proof. destruct sz; cbn; lia. Qed.

  Lemma step_store_any regs pc mem rom w sz (rs1 rs2 : reg) (imm : bv 12) :
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    store_ok SEGS mem (v_addi (getr regs rs1) (bv_signed imm)) (Z.to_nat (msize_z sz)) = true ->
    RiscvSemantics.step SEGS (mkst regs pc mem rom) =
    MachineOk (mkst regs (v_addi pc 4)
      (wbytes mem (v_addi (getr regs rs1) (bv_signed imm)) (word_to_le_bytes (Z.to_nat (msize_z sz)) (getr regs rs2))) rom).
  Proof.
    intros Hf He Hd Hok. destruct sz; cbn [msize_z Z.to_nat Pos.to_nat Pos.iter_op Nat.add] in Hok |- *.
    - eapply step_sb; eauto.
    - eapply step_sh_val; eauto.
    - eapply step_sw_val; eauto.
    - eapply step_sd_val; eauto.
  Qed.

  Lemma bytes_zero bs : bytes_le_to_Z bs = 0 -> forall j, (j < length bs)%nat -> bv_unsigned (nth j bs (Z_to_bv 8 0)) = 0.
  Proof.
    induction bs as [|b bs IH]; intros H j Hj; [cbn in Hj; lia|].
    cbn [bytes_le_to_Z] in H. apply Z.lor_eq_0_iff in H as [H1 H2].
    rewrite Z.shiftl_mul_pow2 in H2 by lia.
    assert (bytes_le_to_Z bs = 0) by lia.
    destruct j as [|j]; [exact H1|]. cbn [nth]. apply IH; auto. cbn in Hj. lia.
  Qed.

  Lemma u_word_zero (wv : word) e nu :
    bv_unsigned wv = zwrap 64 (eval nu e) -> eval nu e = 0 -> bv_unsigned wv = 0.
  Proof. intros -> ->. reflexivity. Qed.

  Lemma is_zero_val_sound A nu (v : absval) (wv : word) :
    lgamma A nu -> is_zero_val A v = true ->
    match v with Some e => bv_unsigned wv = zwrap 64 (eval nu e) | None => False end ->
    bv_unsigned wv = 0.
  Proof.
    intros HL Hz Hv. unfold is_zero_val in Hz. destruct v as [e|]; [|discriminate].
    destruct (lin_is_const e) eqn:Ec.
    - apply Z.eqb_eq in Hz. rewrite zm64_zwrap in Hz. rewrite Hv, (eval_is_const nu e Ec). exact Hz.
    - pose proof (bnd_sound A nu e HL) as Hb. destruct (bnd A e) as [[lo|] [hi|]]; try discriminate.
      apply andb_prop in Hz as [Z1 Z2]. apply Z.eqb_eq in Z1. apply Z.eqb_eq in Z2. subst.
      destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2. rewrite Hv. replace (eval nu e) with 0 by lia. reflexivity.
  Qed.

  Lemma is_zero_byte_sound A nu (v : absval) (wv : word) :
    lgamma A nu -> is_zero_byte A v = true ->
    match v with Some e => bv_unsigned wv = zwrap 64 (eval nu e) | None => False end ->
    bv_unsigned wv mod 256 = 0.
  Proof.
    intros HL Hz Hv. unfold is_zero_byte in Hz. destruct v as [e|]; [|discriminate].
    destruct (lin_is_const e) eqn:Ec.
    - apply Z.eqb_eq in Hz. change 255 with (2 ^ 8 - 1) in Hz. rewrite land_lowmask in Hz by lia.
      rewrite Hv, (eval_is_const nu e Ec). unfold zwrap. change 256 with (2 ^ 8).
      rewrite Z.mod_mod_divide; [exact Hz|]. exists (2 ^ 56). reflexivity.
    - pose proof (bnd_sound A nu e HL) as Hb. destruct (bnd A e) as [[lo|] [hi|]]; try discriminate.
      apply andb_prop in Hz as [Z1 Z2]. apply Z.eqb_eq in Z1. apply Z.eqb_eq in Z2. subst.
      destruct Hb as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2. rewrite Hv. replace (eval nu e) with 0 by lia. reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma rdn_wbytes_byte mem (a : Z) (bs : list byte) j :
    0 <= a -> a + Z.of_nat (length bs) <= 2 ^ 64 -> (j < length bs)%nat ->
    rdn SEGS (wbytes mem (wordZ a) bs) (wordZ (a + Z.of_nat j)) 1 = Some [nth j bs (Z_to_bv 8 0)].
  Proof.
    intros Ha Hl Hj.
    pose proof (rdn_wbytes_hit SEGS bs mem (wordZ a) ltac:(rewrite u_wordZ; lia)) as H.
    pose proof (rdn_nth SEGS _ _ _ _ j H Hj) as H1.
    replace (wordZ a + nat_to_word j)%bv with (wordZ (a + Z.of_nat j)) in H1; [exact H1|].
    apply bv_eq. unfold nat_to_word. rewrite bv_add_unsigned, bv_wrap64_zwrap, u_Z_to_bv64.
    unfold wordZ. rewrite !u_Z_to_bv64, (zwrap_id 64 a), (zwrap_id 64 (Z.of_nat j)) by lia.
    rewrite (zwrap_id 64 (a + Z.of_nat j)) by lia. reflexivity.
  Qed.

  Lemma cell_holds_unchanged nu mem mem' a w v :
    (forall n, rdn SEGS mem' (wordZ a) n = rdn SEGS mem (wordZ a) n) ->
    cell_holds SEGS nu mem a w v -> cell_holds SEGS nu mem' a w v.
  Proof. intros Hr. destruct v as [e|]; cbn [cell_holds]; [|auto]. rewrite Hr. auto. Qed.

  (* [comment removed for export] *)
  Lemma kill_nul_eq X lo hi v :
    exists l, kill_nul X lo hi v = set_nul X l /\
      (forall f, In f l -> In f (vs_nul X) /\ (is_zero_val X v = true \/ snd f < lo \/ hi < fst f)).
  Proof.
    unfold kill_nul. destruct (vs_nul X) as [|f0 t] eqn:En.
    - exists []. split; [destruct X; cbn in *; subst; reflexivity|]. intros f Hf; destruct Hf.
    - destruct (is_zero_val X v) eqn:Ez.
      + exists (f0 :: t). split; [destruct X; cbn in En |- *; subst; reflexivity|]. intros f Hf. split; [exact Hf|auto].
      + eexists. split; [reflexivity|]. intros f Hf. apply filter_In in Hf as [H1 H2]. split; [exact H1|].
        apply orb_prop in H2. destruct H2 as [H2|H2]; apply Z.ltb_lt in H2; auto.
  Qed.

  Lemma add_nul_eq X lo hi : exists l, add_nul X lo hi = set_nul X l /\ (forall f, In f l -> f = (lo, hi) \/ In f (vs_nul X)).
  Proof.
    unfold add_nul, nul_min. eexists. split; [reflexivity|]. intros f Hf. apply filter_In in Hf as [Hf _].
    destruct Hf as [<-|Hf]; auto.
  Qed.

  #[using="PO"] Theorem x_store_sound A nu regs mem pc rom w sz (rs1 rs2 : reg) (imm : bv 12) succs :
    gammaP A nu regs mem -> vs_pc A = bv_unsigned pc ->
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Store sz rs1 rs2 imm, 4) ->
    x_store P A sz (rz rs1) (rz rs2) (bv_signed imm) = VR_next succs ->
    step_post SEGS P E mem0 A nu succs regs mem pc rom.
  Proof.
    intros HGm Hpc Hf He Hd Hx. unfold x_store in Hx.
    pose proof (gamma_lgamma _ _ _ _ _ _ _ _ HGm) as HL.
    pose proof HGm as (HE&HM&HF&HS&HC&HMo&HV&HR&HSl&HG&HN&HB).
    pose proof (msize_pos sz) as Hn. set (n := msize_z sz) in *.
    destruct (addr_of A (rz rs1) (bv_signed imm)) as [addr|] eqn:Ea; [|discriminate].
    destruct (addr_of_sound A nu regs mem rs1 (bv_signed imm) addr HGm Ea) as [Baddr Ua].
    destruct (classify P A addr n true) as [r| |m] eqn:Ecl; [|exfalso; exact (classify_not_dead A nu addr n true HL Ecl)|discriminate].
    destruct (do_store A r n (get_reg A (rz rs2))) as [A1|] eqn:Eds; [|discriminate]. inversion Hx; subst; clear Hx.
    pose proof (gamma_get_reg SEGS P E mem0 A nu regs mem rs2 HGm) as [Wv Bv].
    set (wv := getr regs rs2) in *. set (val := get_reg A (rz rs2)) in *.
    set (k := Z.to_nat n). assert (Hk : Z.of_nat k = n) by (unfold k; lia).
    assert (Hlen : length (word_to_le_bytes k wv) = k) by apply length_N_to_le_bytes.
    destruct PO as (P0&P1&PS&PF&PW&PR&PP&PB) eqn:EPO. clear EPO.
    pose proof HE as (E1&E2&E3&E4&E5&E6&E7&E8&E9&E11&E12).
    destruct r as [off lo hi|doff|lo hi].
    - (* [comment removed for export] *)
      destruct (classify_stack_sound A nu addr n true off lo hi HL HF ltac:((ltac2:(LK.k [@Hn; @Hlen; @E3; @E7; @E8; @E9; @E11]); lia)) Ecl) as (Eoff&Eaddr&Hlohi&Hlo&Hhi&Hws).
      specialize (Hws eq_refl). apply in_ranges_sound in Hws as [rlo [rhi (Hr&R1&R2)]].
      set (ov := eval nu off) in *. set (a := e_sp0 E + ov) in *.
      assert (Ha : 0 <= a /\ a + n <= 2 ^ 64) by (unfold a; (ltac2:(LK.k [@Hn; @Hlen; @P1; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hlo; @Hhi]); lia)).
      assert (Eaw : v_addi (getr regs rs1) (bv_signed imm) = wordZ a).
      { apply wordZ_eq_u. rewrite Ua, Eaddr. apply zwrap_id. unfold a in Ha. lia. }
      assert (Hok : store_ok SEGS mem (wordZ a) k = true).
      { apply store_ok_bytes; [(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Hn; @P1; @E1; @E2; @Hhi]); lia)|(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Hn; @P1; @E1; @E2; @Hhi]); lia)|]. intros j Hj. apply (MC_frame_ok mem (a + j) HM). unfold a; lia. }
      assert (WR : writable_range (a) (Z.of_nat (length (word_to_le_bytes k wv)))).
      { rewrite Hlen, Hk. left. unfold a. split; [lia|]. split; [lia|]. exists (rlo, rhi). cbn [fst snd]. split; [exact Hr|lia]. }
      destruct (MC_wbytes mem a (word_to_le_bytes k wv) HE HM WR ltac:(rewrite Hlen; lia)) as (MC'&FM'&_).
      set (mem' := wbytes mem (wordZ a) (word_to_le_bytes k wv)) in *.
      exists regs, (v_addi pc 4), mem', (set_pc A1 (npc_of A)), nu.
      split. { unfold mem'. rewrite <- Eaw. eapply step_store_any; [eassumption|eassumption|eassumption|]. rewrite Eaw. exact Hok. }
      split; [left; reflexivity|]. split.
      { cbn. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap, Hpc. reflexivity. }
      split; [apply ext_refl|].
      (* [comment removed for export] *)
      cbn [do_store] in Eds.
      (* [comment removed for export] *)
      set (sl1 := if lo =? hi then match val with Some e => cm_set (cm_kill (vs_slots A) lo (lo + n)) lo (n, Some e)
                                               | None => cm_kill (vs_slots A) lo (lo + n) end
                  else cm_kill (vs_slots A) lo (hi + n)).
      set (klo := lo). set (khi := if lo =? hi then lo + n - 1 else hi + n - 1).
      assert (HA0 : exists l1, (if lo =? hi
                 then kill_nul (set_slots A match val with Some e => cm_set (cm_kill (vs_slots A) lo (lo + n)) lo (n, Some e) | None => cm_kill (vs_slots A) lo (lo + n) end) lo (lo + n - 1) val
                 else kill_nul (set_slots A (cm_kill (vs_slots A) lo (hi + n))) lo (hi + n - 1) val)
                 = set_nul (set_slots A sl1) l1 /\
                 (forall f, In f l1 -> In f (vs_nul A) /\ (is_zero_val A val = true \/ snd f < klo \/ khi < fst f))).
      { unfold sl1, khi, klo. destruct (lo =? hi).
        - destruct (kill_nul_eq (set_slots A match val with Some e => cm_set (cm_kill (vs_slots A) lo (lo + n)) lo (n, Some e) | None => cm_kill (vs_slots A) lo (lo + n) end) lo (lo + n - 1) val) as [l1 [EK1 H1]].
          exists l1. split; [exact EK1|]. intros f Hfl. destruct (H1 f Hfl) as [X1 X2]. cbn in X1. split; [exact X1|].
          destruct X2 as [X2|X2]; [left|right; exact X2]. unfold is_zero_val in *. destruct val; [|exact X2]. exact X2.
        - destruct (kill_nul_eq (set_slots A (cm_kill (vs_slots A) lo (hi + n))) lo (hi + n - 1) val) as [l1 [EK1 H1]].
          exists l1. split; [exact EK1|]. intros f Hfl. destruct (H1 f Hfl) as [X1 X2]. cbn in X1. split; [exact X1|].
          destruct X2 as [X2|X2]; [left|right; exact X2]. unfold is_zero_val in *. destruct val; [|exact X2]. exact X2. }
      destruct HA0 as [l1 [EA0 Hl1]]. rewrite EA0 in Eds.
      assert (HA1 : exists l2, A1 = set_nul (set_slots A sl1) l2 /\
                (forall f, In f l2 -> (f = (lo, hi) /\ n = 1 /\ is_zero_byte (set_nul (set_slots A sl1) l1) val = true) \/ In f l1)).
      { destruct ((n =? 1) && is_zero_byte (set_nul (set_slots A sl1) l1) val) eqn:Ezb.
        - inversion Eds; subst. apply andb_prop in Ezb as [En1 Ezb]. apply Z.eqb_eq in En1.
          destruct (add_nul_eq (set_nul (set_slots A sl1) l1) lo hi) as [l2 [EK2 H2]].
          exists l2. split; [rewrite EK2; destruct A; reflexivity|]. intros f Hfl. destruct (H2 f Hfl) as [X|X]; [left; auto|right; exact X].
        - inversion Eds; subst. exists l1. split; [reflexivity|]. intros f Hfl. right; exact Hfl. }
      destruct HA1 as [l2 [EA1 Hl2]]. subst A1.
      split; [cbn; (ltac2:(LK.k [@Hlen; @E3; @E7; @E8; @E9; @E11]); lia)|]. split; [exact FM'|].
      (* [comment removed for export] *)
      split; [exact HE|]. split; [exact MC'|]. split; [exact HF|]. split; [exact HS|]. split; [exact HC|]. split; [exact HMo|]. split; [exact HV|].
      assert (Hua : bv_unsigned (wordZ a) = a) by (apply u_wordZ; lia).
      assert (OUT : forall (c : Z) (cw : nat), 0 <= c -> c + Z.of_nat cw <= 2 ^ 64 ->
                (c + Z.of_nat cw <= a \/ a + n <= c) ->
                rdn SEGS mem' (wordZ c) cw = rdn SEGS mem (wordZ c) cw).
      { intros c cw Hc1 Hc2 Hdisj. destruct cw as [|cw']; [reflexivity|]. unfold mem'.
        apply rdn_wbytes_out; rewrite ?Hua, ?Hlen, ?u_wordZ by (ltac2:(LK.k [@Hn; @Hlen; @P1; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hhi; @Ha; @Hc1; @Hc2; @Hdisj]); lia); (ltac2:(LK.k [@Hn; @Hlen; @P1; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hhi; @Ha; @Hc1; @Hc2; @Hdisj]); lia). }
      split; [|split; [|split; [|split]]].
      + (* [comment removed for export] *) intros r' e Hr' Hg. cbn in Hg. exact (HR r' e Hr' Hg).
      + (* [comment removed for export] *)
        intros off' w' v' Hin. cbn [vs_slots set_nul set_slots] in Hin.
        assert (OLD : In (off', (w', v')) (vs_slots A) -> ~ (off' < klo + (khi - klo + 1) /\ klo < off' + w') ->
                  (- vp_frame P <= off' /\ 0 < w' /\ off' + w' <= 0) /\ cell_holds SEGS nu mem' (e_sp0 E + off') w' v').
        { intros Hold Hdisj. destruct (HSl _ _ _ Hold) as [Hrg Hch]. split; [exact Hrg|].
          destruct v' as [e'|]; [|exact I]. cbn [cell_holds] in Hch |- *.
          rewrite OUT; [exact Hch|unfold a; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hhi; @Ha; @Hrg; @P1; @E2; @Hlohi; @Hdisj; @e; @n0]); lia)|unfold a; rewrite of_to_nat_max; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hhi; @Ha; @Hrg; @P1; @E2; @Hlohi; @Hdisj; @e; @n0]); lia)|unfold a, khi, klo in *; rewrite of_to_nat_max; destruct (Z.eqb_spec lo hi); (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hhi; @Ha; @Hrg; @P1; @E2; @Hlohi; @Hdisj; @e; @n0]); lia)]. }
        unfold sl1 in Hin. destruct (Z.eqb_spec lo hi) as [Elh|Elh].
        * assert (Eov : ov = lo) by lia.
          assert (NEW : forall e, val = Some e -> (off', (w', v')) = (lo, (n, Some e)) ->
                    (- vp_frame P <= off' /\ 0 < w' /\ off' + w' <= 0) /\ cell_holds SEGS nu mem' (e_sp0 E + off') w' v').
          { intros e Hval X. inversion X; subst off' w' v'. split; [lia|]. cbn [cell_holds].
            exists (word_to_le_bytes k wv). split.
            - unfold mem', a. rewrite Eov. replace (Z.to_nat n) with k by lia.
              rewrite <- Hlen at 2. apply rdn_wbytes_hit. rewrite u_wordZ by lia. rewrite Hlen. lia.
            - rewrite bytes_le_N, Hk. subst val. rewrite Hval in Wv. rewrite (wval_some _ _ _ Wv). unfold zwrap.
              apply Z.mod_mod_divide. exists (2 ^ (64 - 8 * n)). rewrite <- Z.pow_add_r by (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hhi; @Ha]); lia). f_equal. lia. }
          destruct val as [e|].
          -- apply cm_set_in in Hin. destruct Hin as [Hin|Hin]; [exact (NEW e eq_refl Hin)|].
             apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). unfold klo, khi. try rewrite (proj2 (Z.eqb_eq lo hi) Elh). cbn. lia.
          -- apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). unfold klo, khi. try rewrite (proj2 (Z.eqb_eq lo hi) Elh). cbn. (ltac2:(LK.k [@Bv; @Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @H]); lia).
        * apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). unfold klo, khi.
          try rewrite (proj2 (Z.eqb_neq lo hi) Elh). cbn. lia.
      + (* [comment removed for export] *)
        intros ga gw gv Hin. cbn in Hin. destruct (HG _ _ _ Hin) as [Hrg Hch]. split; [exact Hrg|].
        destruct gv as [e'|]; [|exact I]. cbn [cell_holds] in Hch |- *.
        rewrite OUT; [exact Hch|(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P1; @E1; @E2; @Hlo; @Hhi]); lia)|rewrite of_to_nat_max; (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P1; @E1; @E2; @Hlo; @Hhi]); lia)|unfold a; rewrite of_to_nat_max; (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P1; @E1; @E2; @Hlo; @Hhi]); lia)].
      + (* [comment removed for export] *)
        intros nlo nhi Hin. cbn [vs_nul set_nul] in Hin.
        assert (ZB : forall j, (j < k)%nat -> bv_unsigned wv = 0 ->
                  rdn SEGS mem' (wordZ (a + Z.of_nat j)) 1 = Some [nth j (word_to_le_bytes k wv) (Z_to_bv 8 0)] /\
                  bv_unsigned (nth j (word_to_le_bytes k wv) (Z_to_bv 8 0)) = 0).
        { intros j Hj Hz. split.
          - unfold mem'. apply rdn_wbytes_byte; rewrite ?Hlen; (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Hj; @Hn; @P1; @E1; @E2; @Hhi]); lia).
          - apply bytes_zero; [|rewrite Hlen; exact Hj]. rewrite bytes_le_N, Hz. reflexivity. }
        destruct (Hl2 _ Hin) as [[Ef [En1 Ezb]]|Hin1].
        * (* [comment removed for export] *)
          inversion Ef; subst nlo nhi. exists ov, (nth 0 (word_to_le_bytes k wv) (Z_to_bv 8 0)).
          assert (Hbz : bv_unsigned wv mod 256 = 0).
          { change (is_zero_byte (set_nul (set_slots A sl1) l1) val) with (is_zero_byte A val) in Ezb.
            apply (is_zero_byte_sound A nu val wv HL Ezb). subst val.
            destruct (get_reg A (rz rs2)) as [e|]; [exact (wval_some _ _ _ Wv)|]. cbn in Ezb. discriminate. }
          assert (Hk1 : k = 1%nat) by (unfold k; rewrite En1; reflexivity).
          assert (Hlen1 : length (word_to_le_bytes k wv) = 1%nat) by (rewrite Hlen; exact Hk1).
          split; [lia|]. split; [(ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hlo; @Hhi; @Ha; @Hk1; @Hlen1]); lia)|]. split.
          -- unfold mem', a. replace (e_sp0 E + ov) with (e_sp0 E + ov + Z.of_nat 0) at 2 by (ltac2:(LK.k [@Hlen; @E3; @E7; @E8; @E9; @E11; @Hk1; @Hlen1]); lia).
             apply rdn_wbytes_byte; rewrite ?Hlen1; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hhi; @Ha; @Hk1; @Hlen1; @P1; @E2]); lia).
          -- rewrite <- bytes_le_single.
             assert (Hbs : word_to_le_bytes k wv = [nth 0 (word_to_le_bytes k wv) (Z_to_bv 8 0)]).
             { destruct (word_to_le_bytes k wv) as [|b0 [|b1 t]]; cbn in Hlen1; try discriminate. reflexivity. }
             rewrite <- Hbs, bytes_le_N, Hk1. exact Hbz.
        * destruct (Hl1 _ Hin1) as [Hold Hcase]. destruct (HN _ _ Hold) as [off0 [b0 (Q1&Q2&Q3&Q4)]].
          destruct (Z_lt_le_dec off0 ov) as [Hlt|Hge]; [|destruct (Z_lt_le_dec off0 (ov + n)) as [Hmid|Hge2]].
          -- exists off0, b0. split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
             rewrite OUT; [exact Q3|(ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Q2; @P1; @E2; @Hlt]); lia)|cbn; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Q2; @P1; @E2; @Hlt]); lia)|unfold a; cbn; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Q2; @P1; @E2; @Hlt]); lia)].
          -- (* [comment removed for export] *)
             assert (Hz : is_zero_val A val = true).
             { destruct Hcase as [Hz|[Hc|Hc]]; [exact Hz|exfalso|exfalso]; unfold klo, khi in Hc; cbn in Hc, Q1;
                 destruct (Z.eqb_spec lo hi); cbn in Hc; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hlohi; @Hhi; @Ha; @Hc; @Q1; @Hge; @n0; @Hmid; @e]); lia). }
             assert (Hw0 : bv_unsigned wv = 0).
             { apply (is_zero_val_sound A nu val wv HL Hz). subst val. destruct (get_reg A (rz rs2)) as [e|]; [exact (wval_some _ _ _ Wv)|].
               unfold is_zero_val in Hz. discriminate. }
             assert (Hj : exists j, (j < k)%nat /\ e_sp0 E + off0 = a + Z.of_nat j).
             { exists (Z.to_nat (off0 - ov)). unfold a.
               split; [apply Nat2Z.inj_lt; rewrite Z2Nat.id by (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hge; @Hn; @E1; @Ha; @Q2; @Hmid]); lia); (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hge; @Hn; @E1; @Ha; @Q2; @Hmid]); lia)|rewrite Z2Nat.id by (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hge; @Hn; @E1; @Ha; @Q2; @Hmid]); lia); (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hge; @Hn; @E1; @Ha; @Q2; @Hmid]); lia)]. }
             destruct Hj as [j [Hj Eo]]. destruct (ZB j Hj Hw0) as [Z1 Z2].
             exists off0, (nth j (word_to_le_bytes k wv) (Z_to_bv 8 0)). split; [exact Q1|]. split; [exact Q2|].
             rewrite Eo. split; [exact Z1|exact Z2].
          -- exists off0, b0. split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
             rewrite OUT; [exact Q3|(ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Q2; @Hge; @Hge2; @P1; @E2]); lia)|cbn; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Q2; @Hge; @Hge2; @P1; @E2]); lia)|unfold a; cbn; (ltac2:(LK.k [@Hn; @Hlen; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Q2; @Hge; @Hge2; @P1; @E2]); lia)].
      + (* [comment removed for export] *)
        destruct HB as (B0&B1&B2&B3&B4&B5). split; [exact B0|]. split; [exact B1|]. split; [exact B2|].
        split; [|split; [exact B4|exact B5]].
        intros k' w' e' Hin. cbn [vs_slots set_nul set_slots vs_next] in Hin |- *. unfold sl1 in Hin.
        destruct (lo =? hi); [destruct val as [e|]|].
        * apply cm_set_in in Hin. destruct Hin as [Hin|Hin]; [inversion Hin; subst; exact Bv|]. apply cm_kill_sub in Hin. exact (B3 _ _ _ Hin).
        * apply cm_kill_sub in Hin. exact (B3 _ _ _ Hin).
        * apply cm_kill_sub in Hin. exact (B3 _ _ _ Hin).
    - (* [comment removed for export] *) destruct (classify_data_sound A nu addr n true doff HL HF Ecl) as [X _]. discriminate.
    - (* [comment removed for export] *)
      destruct (classify_img_sound A nu addr n true lo hi HL Ecl) as (Hrng&Hwc&_). specialize (Hwc eq_refl).
      apply in_cells_sound in Hwc as [c (Hc&C1&C2)].
      destruct (PW _ Hc) as [f (Hff&F1&F2)]. destruct (PF _ Hff) as (G1&G2&G3&G4).
      set (av := eval nu addr) in *.
      assert (Ha : 0 <= av /\ av + n <= 2 ^ 64) by lia.
      assert (Eaw : v_addi (getr regs rs1) (bv_signed imm) = wordZ av).
      { apply wordZ_eq_u. rewrite Ua. apply zwrap_id. lia. }
      assert (Hok : store_ok SEGS mem (wordZ av) k = true).
      { apply store_ok_bytes; [(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Hn; @P0; @P1; @E1; @E2; @Hrng; @C2; @F2; @G2]); lia)|(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Ha; @Hn; @P0; @P1; @E1; @E2; @Hrng; @C2; @F2; @G2]); lia)|]. intros j Hj. apply (MC_cell_ok mem f (av + j) HM Hff). lia. }
      assert (WR : writable_range av (Z.of_nat (length (word_to_le_bytes k wv)))).
      { rewrite Hlen, Hk. right. exists c. split; [exact Hc|lia]. }
      destruct (MC_wbytes mem av (word_to_le_bytes k wv) HE HM WR ltac:(rewrite Hlen; lia)) as (MC'&FM'&_).
      set (mem' := wbytes mem (wordZ av) (word_to_le_bytes k wv)) in *.
      cbn [do_store] in Eds.
      set (gl1 := if lo =? hi then cm_set (cm_kill (vs_globs A) lo (lo + n)) lo (n, val) else cm_kill (vs_globs A) lo (hi + n)).
      assert (EA1 : A1 = set_globs A gl1).
      { unfold gl1. destruct (lo =? hi); inversion Eds; reflexivity. }
      subst A1. clear Eds.
      exists regs, (v_addi pc 4), mem', (set_pc (set_globs A gl1) (npc_of A)), nu.
      split. { unfold mem'. rewrite <- Eaw. eapply step_store_any; [eassumption|eassumption|eassumption|]. rewrite Eaw. exact Hok. }
      split; [left; reflexivity|]. split.
      { cbn. unfold npc_of, v_addi. rewrite u_Z_to_bv64, wrap64_zwrap, Hpc. reflexivity. }
      split; [apply ext_refl|]. split; [cbn; lia|]. split; [exact FM'|].
      split; [exact HE|]. split; [exact MC'|]. split; [exact HF|]. split; [exact HS|]. split; [exact HC|]. split; [exact HMo|]. split; [exact HV|].
      assert (Hua : bv_unsigned (wordZ av) = av) by (apply u_wordZ; lia).
      assert (OUT : forall (c0 : Z) (cw : nat), 0 <= c0 -> c0 + Z.of_nat cw <= 2 ^ 64 ->
                (c0 + Z.of_nat cw <= av \/ av + n <= c0) ->
                rdn SEGS mem' (wordZ c0) cw = rdn SEGS mem (wordZ c0) cw).
      { intros c0 cw Hc1 Hc2 Hdisj. destruct cw as [|cw']; [reflexivity|]. unfold mem'.
        apply rdn_wbytes_out; rewrite ?Hua, ?Hlen, ?u_wordZ by (ltac2:(LK.k [@Hn; @Hlen; @P0; @P1; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrng; @C2; @F2; @G2; @Hc1; @Hc2; @Hdisj]); lia); (ltac2:(LK.k [@Hn; @Hlen; @P0; @P1; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrng; @C2; @F2; @G2; @Hc1; @Hc2; @Hdisj]); lia). }
      split; [|split; [|split; [|split]]].
      + intros r' e Hr' Hg. cbn in Hg. exact (HR r' e Hr' Hg).
      + (* [comment removed for export] *)
        intros off' w' v' Hin. cbn in Hin. destruct (HSl _ _ _ Hin) as [Hrg Hch]. split; [exact Hrg|].
        destruct v' as [e'|]; [|exact I]. cbn [cell_holds] in Hch |- *.
        rewrite OUT; [exact Hch|(ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrg; @P1; @E2; @Hrng; @C2; @F2; @G2; @Ha]); lia)|rewrite of_to_nat_max; (ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrg; @P1; @E2; @Hrng; @C2; @F2; @G2; @Ha]); lia)|rewrite of_to_nat_max; (ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrg; @P1; @E2; @Hrng; @C2; @F2; @G2; @Ha]); lia)].
      + (* [comment removed for export] *)
        intros ga gw gv Hin. cbn [vs_globs set_pc set_globs] in Hin.
        assert (OLD : In (ga, (gw, gv)) (vs_globs A) -> ~ (ga < lo + (if lo =? hi then n else hi - lo + n) /\ lo < ga + gw) ->
                  (0 <= ga /\ 0 < gw /\ ga + gw <= vp_splo P - vp_frame P) /\ cell_holds SEGS nu mem' ga gw gv).
        { intros Hold Hdisj. destruct (HG _ _ _ Hold) as [Hrg Hch]. split; [exact Hrg|].
          destruct gv as [e'|]; [|exact I]. cbn [cell_holds] in Hch |- *.
          rewrite OUT; [exact Hch|(ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P0; @P1; @E1; @E2; @E12; @Hrng; @Hdisj; @e]); lia)|rewrite of_to_nat_max; (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P0; @P1; @E1; @E2; @E12; @Hrng; @Hdisj; @e]); lia)|rewrite of_to_nat_max; destruct (Z.eqb_spec lo hi); (ltac2:(LK.k [@Hlen; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrg; @Hn; @P0; @P1; @E1; @E2; @E12; @Hrng; @Hdisj; @e]); lia)]. }
        unfold gl1 in Hin. destruct (Z.eqb_spec lo hi) as [Elh|Elh].
        * apply cm_set_in in Hin. destruct Hin as [Hin|Hin].
          -- inversion Hin; subst ga gw gv. split; [lia|]. destruct val as [e|]; [|exact I]. cbn [cell_holds].
             exists (word_to_le_bytes k wv). split.
             ++ unfold mem'. replace lo with av by lia. replace (Z.to_nat n) with k by lia.
                rewrite <- Hlen at 2. apply rdn_wbytes_hit. rewrite u_wordZ by lia. rewrite Hlen. lia.
             ++ rewrite bytes_le_N, Hk. rewrite (wval_some _ _ _ Wv). unfold zwrap.
                apply Z.mod_mod_divide. exists (2 ^ (64 - 8 * n)). rewrite <- Z.pow_add_r by (ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @Hrng; @C2; @F2; @G2; @Ha; @E12]); lia). f_equal. lia.
          -- apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). lia.
        * apply OLD; [eapply cm_kill_sub; exact Hin|]. pose proof (cm_kill_disjoint _ _ _ _ _ _ Hin). lia.
      + (* [comment removed for export] *)
        intros nlo nhi Hin. cbn in Hin. destruct (HN _ _ Hin) as [off0 [b0 (Q1&Q2&Q3&Q4)]].
        exists off0, b0. split; [exact Q1|]. split; [exact Q2|]. split; [|exact Q4].
        rewrite OUT; [exact Q3|(ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrng; @C2; @F2; @G2; @Ha; @Q2; @P1]); lia)|cbn; (ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrng; @C2; @F2; @G2; @Ha; @Q2; @P1]); lia)|cbn; (ltac2:(LK.k [@Hn; @Hlen; @P0; @E1; @E2; @E3; @E4; @E5; @E7; @E8; @E9; @E11; @E12; @Hrng; @C2; @F2; @G2; @Ha; @Q2; @P1]); lia)].
      + destruct HB as (B0&B1&B2&B3&B4&B5). split; [exact B0|]. split; [exact B1|]. split; [exact B2|].
        split; [exact B3|]. split; [|exact B5].
        intros k' w' e' Hin. cbn [vs_globs set_pc set_globs vs_next] in Hin |- *. unfold gl1 in Hin.
        destruct (lo =? hi).
        * apply cm_set_in in Hin. destruct Hin as [Hin|Hin].
          -- assert (Hv : val = Some e') by congruence. clearbody val. subst val. exact Bv.
          -- apply cm_kill_sub in Hin. exact (B4 _ _ _ Hin).
        * apply cm_kill_sub in Hin. exact (B4 _ _ _ Hin).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  Definition ldval (sg : bool) (n : Z) (X : Z) : Z :=
    if sg && Z.ltb n 8 then zwrap 64 (zswrap (8 * n) X) else X.

  Lemma step_load_any regs pc mem rom w sz sg (rd rs1 : reg) (imm : bv 12) bs :
    fetch_word SEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load sz sg rd rs1 imm, 4) ->
    (sz = SZ8 -> sg = true) ->
    rdn SEGS mem (v_addi (getr regs rs1) (bv_signed imm)) (Z.to_nat (msize_z sz)) = Some bs ->
    exists wl : word,
      bv_unsigned wl = ldval sg (msize_z sz) (bytes_le_to_Z bs) /\
      RiscvSemantics.step SEGS (mkst regs pc mem rom) =
      MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd wl) (v_addi pc 4) mem rom).
  Proof.
    intros Hf He Hd Hsz Hrd.
    pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    pose proof (bytes_le_to_Z_bound bs) as HB. pose proof (bytes_le_to_Z_nonneg bs) as HB0. rewrite Hlen in HB.
    assert (HX64 : 0 <= bytes_le_to_Z bs < 2 ^ 64).
    { split; [lia|]. eapply Z.lt_le_trans; [exact HB|]. apply Z.pow_le_mono_r; [lia|]. destruct sz; cbn; lia. }
    set (v := Z_to_bv 64 (bytes_le_to_Z bs)).
    assert (Hv : bytes_le_to_Z bs = bv_unsigned v) by (unfold v; rewrite u_Z_to_bv64, zwrap_id by lia; reflexivity).
    destruct sz; destruct sg; cbn [msize_z ldval andb Z.ltb Z.compare Pos.compare Pos.compare_cont] in *.
    - destruct bs as [|b [|b' t]]; cbn in Hlen; try discriminate.
      exists (v_lb b). split; [|eapply step_lb; eauto].
      unfold v_lb. rewrite u_Z_to_bv64. f_equal. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r.
      unfold bv_signed, bv_swrap, zswrap. reflexivity.
    - destruct bs as [|b [|b' t]]; cbn in Hlen; try discriminate.
      exists (Z_to_bv 64 (bv_unsigned b)). split; [|eapply step_lbu; eauto].
      rewrite u_Z_to_bv64. cbn [bytes_le_to_Z]. rewrite Z.shiftl_0_l, Z.lor_0_r. apply zwrap_id.
      pose proof (bv_unsigned_in_range 8 b) as Hb8. unfold bv_modulus in Hb8. cbn in Hb8. lia.
    - exists (v_lh v). split; [|eapply step_lh; eauto]. unfold v_lh. rewrite u_Z_to_bv64, Hv. reflexivity.
    - exists v. split; [|eapply step_lhu; eauto]. symmetry; exact Hv.
    - exists (v_lw v). split; [|eapply step_lw; eauto]. unfold v_lw. rewrite u_Z_to_bv64, Hv. reflexivity.
    - exists v. split; [|eapply step_lwu; eauto]. symmetry; exact Hv.
    - exists v. split; [|eapply step_ld; eauto]. symmetry; exact Hv.
    - discriminate (Hsz eq_refl).
  Qed.

  Lemma fresh_loaded_sound A nu n sg X :
    lgamma A nu -> 0 < n <= 8 -> 0 <= X < 2 ^ (8 * n) ->
    res_word A nu (fresh_loaded A n sg) (ldval sg n X).
  Proof.
    intros HL Hn HX. unfold fresh_loaded, ldval.
    destruct (Z.eqb_spec n 8) as [->|Hn8].
    { cbn [andb Z.ltb Z.compare Pos.compare Pos.compare_cont]. destruct sg; apply res_top; exact HL. }
    assert (Hlt : (n <? 8) = true) by (apply Z.ltb_lt; lia). rewrite Hlt.
    unfold range_of. destruct sg; cbn [andb].
    - apply res_exact_word. apply res_exact_fresh; auto. unfold srange.
      pose proof (zswrap_range (8 * n) X ltac:(lia)) as Hr. split; cbn [fst snd lo_le hi_ge]; lia.
    - assert (X64 : 0 <= X < 2 ^ 64).
      { split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HX)|]. apply Z.pow_le_mono_r; lia. }
      apply res_word_fresh; auto. unfold urange. split; cbn [fst snd lo_le hi_ge]; lia.
  Qed.

  (* [comment removed for export] *)
  Lemma areinterp_sound A nu v n sg X :
    lgamma A nu -> 0 < n <= 8 -> lin_below v (vs_next A) = true ->
    X = zwrap (8 * n) (eval nu v) ->
    res_word A nu (areinterp A v n sg) (ldval sg n X).
  Proof.
    intros HL Hn Hb HX. unfold areinterp, ldval.
    pose proof (zwrap_range (8 * n) (eval nu v) ltac:(lia)) as HXr. rewrite <- HX in HXr.
    destruct (Z.eqb_spec n 8) as [->|Hn8].
    { cbn [andb Z.ltb Z.compare Pos.compare Pos.compare_cont].
      destruct sg; apply res_word_same; auto; rewrite HX; symmetry; apply zwrap_idem; lia. }
    assert (Hlt : (n <? 8) = true) by (apply Z.ltb_lt; lia). rewrite Hlt.
    destruct sg; cbn [andb].
    - assert (Hs : zswrap (8 * n) X = zswrap (8 * n) (eval nu v)).
      { rewrite HX. apply zswrap_zwrap. lia. }
      rewrite Hs.
      pose proof (bnd_sound A nu v HL) as Hbd.
      destruct (negb (lin_is_const v) && itv_empty (bnd A v)) eqn:Ed.
      { apply andb_prop in Ed as [E1 E2]. destruct (lin_is_const v) eqn:Ec; [discriminate|].
        unfold bnd in E2. rewrite Ec in E2. rewrite (lp_bounds_not_empty' A nu v HL) in E2. discriminate. }
      destruct (bnd A v) as [[lo|] [hi|]];
        try (apply res_exact_word; apply res_exact_fresh; auto; unfold srange; pose proof (zswrap_range (8 * n) (eval nu v) ltac:(lia)); split; cbn [fst snd lo_le hi_ge]; lia).
      destruct Hbd as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
      destruct (Z.leb (- 2 ^ (8 * n - 1)) lo && Z.ltb hi (2 ^ (8 * n - 1))) eqn:E1.
      + apply andb_prop in E1 as [E1a E1b]. apply Z.leb_le in E1a. apply Z.ltb_lt in E1b.
        apply res_word_same; auto. rewrite zswrap_id; [reflexivity|lia|lia].
      + destruct (Z.leb (2 ^ (8 * n - 1)) lo && Z.ltb hi (2 * 2 ^ (8 * n - 1))) eqn:E2.
        * apply andb_prop in E2 as [E2a E2b]. apply Z.leb_le in E2a. apply Z.ltb_lt in E2b.
          apply res_word_same; [exact HL| |now apply lin_below_laddc]. rewrite eval_laddc.
          f_equal. rewrite <- (zswrap_congr (8 * n) (eval nu v + - (2 * 2 ^ (8 * n - 1))) (eval nu v)).
          -- rewrite zswrap_id; [reflexivity|lia|lia].
          -- lia.
          -- exists (-1). rewrite (pow2_half (8 * n)) by lia. lia.
        * apply res_exact_word. apply res_exact_fresh; auto. unfold srange.
          pose proof (zswrap_range (8 * n) (eval nu v) ltac:(lia)). split; cbn [fst snd lo_le hi_ge]; lia.
    - assert (X64 : X = zwrap 64 X).
      { symmetry. apply zwrap_id. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HXr)|]. apply Z.pow_le_mono_r; lia. }
      rewrite X64, HX. apply res_exact_word. apply azext_sound; [exact HL|lia|split; [reflexivity|exact Hb]].
  Qed.

  Lemma atruncate_sound A nu v n sg X :
    lgamma A nu -> 0 < n <= 8 -> lin_below v (vs_next A) = true ->
    X = zwrap (8 * n) (eval nu v) ->
    res_word A nu (atruncate A v n sg) (ldval sg n X).
  Proof.
    intros HL Hn Hb HX. unfold atruncate, ldval.
    pose proof (zwrap_range (8 * n) (eval nu v) ltac:(lia)) as HXr. rewrite <- HX in HXr.
    destruct sg; cbn [andb].
    - destruct (Z.ltb_spec n 8).
      + assert (Hs : zswrap (8 * n) X = zswrap (8 * n) (eval nu v)) by (rewrite HX; apply zswrap_zwrap; lia).
        rewrite Hs.
        pose proof (bnd_sound A nu v HL) as Hbd.
        destruct (negb (lin_is_const v) && itv_empty (bnd A v)) eqn:Ed.
        { apply andb_prop in Ed as [E1 E2]. destruct (lin_is_const v) eqn:Ec; [discriminate|].
          unfold bnd in E2. rewrite Ec in E2. rewrite (lp_bounds_not_empty' A nu v HL) in E2. discriminate. }
        destruct (bnd A v) as [[lo|] [hi|]];
          try (apply res_exact_word; apply res_exact_fresh; auto; unfold srange; pose proof (zswrap_range (8 * n) (eval nu v) ltac:(lia)); split; cbn [fst snd lo_le hi_ge]; lia).
        destruct Hbd as [H1 H2]; cbn [fst snd lo_le hi_ge] in H1, H2.
        destruct (Z.leb (- 2 ^ (8 * n - 1)) lo && Z.ltb hi (2 ^ (8 * n - 1))) eqn:E1.
        * apply andb_prop in E1 as [E1a E1b]. apply Z.leb_le in E1a. apply Z.ltb_lt in E1b.
          apply res_word_same; auto. rewrite zswrap_id; [reflexivity|lia|lia].
        * apply res_exact_word. apply res_exact_fresh; auto. unfold srange.
          pose proof (zswrap_range (8 * n) (eval nu v) ltac:(lia)). split; cbn [fst snd lo_le hi_ge]; lia.
      + (* [comment removed for export] *)
        assert (n = 8) by lia. subst n.
        assert (X64 : 0 <= X < 2 ^ 64) by exact HXr.
        assert (FR : res_word A nu (afresh A (srange 8)) X).
        { pose proof (res_exact_fresh A nu (srange 8) (zswrap 64 X) HL) as R.
          assert (Hin : in_itv (zswrap 64 X) (srange 8)).
          { unfold srange. pose proof (zswrap_range 64 X ltac:(lia)). split; cbn [fst snd lo_le hi_ge]; lia. }
          specialize (R Hin). apply res_exact_word in R. rewrite zwrap_of_zswrap, (zwrap_id 64 X) in R by lia. exact R. }
        destruct (negb (lin_is_const v) && itv_empty (bnd A v)) eqn:Ed; [exact FR|].
        destruct (bnd A v) as [[lo|] [hi|]]; try exact FR.
        destruct (Z.leb (- 2 ^ (8 * 8 - 1)) lo && Z.ltb hi (2 ^ (8 * 8 - 1))); [|exact FR].
        apply res_word_same; auto.
    - assert (X64 : X = zwrap 64 X).
      { symmetry. apply zwrap_id. split; [lia|]. eapply Z.lt_le_trans; [apply (proj2 HXr)|]. apply Z.pow_le_mono_r; lia. }
      rewrite X64, HX. apply res_exact_word. apply azext_sound; [exact HL|lia|split; [reflexivity|exact Hb]].
  Qed.

End Sound.
