(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith List Bool Lia.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZProg ZIface InflateState Inftrees InflateFast InflateArms Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InftreesCoverage AdlerModel RefInflateSafeD RefInflateSafeT RefInflateSafeH RefInflateSafeK.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import RefInflateSafeA1 RefInflateSafeA3 RefInflateSafeA5 RefInflateSafeA6.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import InflateStall.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Definition RS (r r' : iregs) : Prop :=
  ir_left r' = ir_left r /\ ir_out r' = ir_out r /\ ir_in r' = ir_in r /\ ir_have r' = 0 /\ ir_ret r' = ir_ret r /\ ir_put r' = ir_put r.

Lemma RS_refl : forall r, ir_have r = 0 -> RS r r.
Proof. intros r H. unfold RS. repeat split; first [reflexivity | exact H]. Qed.

Lemma RS_pulled : forall r r', ir_have r = 0 -> pulled r r' -> RS r r'.
Proof.
  intros r r' H0 HP. destruct (pulled_have0 r r' HP H0) as (_ & A2 & _ & _ & A5 & A6 & A7 & A8 & A9).
  unfold RS. repeat split; assumption.
Qed.

Lemma RS_trans : forall r1 r2 r3, RS r1 r2 -> RS r2 r3 -> RS r1 r3.
Proof. intros r1 r2 r3 (A1 & A2 & A3 & A4 & A5 & A6) (B1 & B2 & B3 & B4 & B5 & B6). unfold RS. rewrite B1, B2, B3, B5, B6. repeat split; assumption. Qed.

Definition restall (M : Z) (arm : AM unit) : Prop :=
  forall s c r, WINV (mkW s c r) -> is_wrap s <> 0 -> is_mode s = M -> ir_have r = 0 -> SC s (ir_hold r) (ir_bits r) ->
  exists s' r', arm (mkW s c r) = ALeave (mkW s' c r') /\ RS r r'.

Lemma NEEDBITS_k_stall : forall k n s c r, ir_have r = 0 -> ir_bits r < n -> (0 < k)%nat ->
  NEEDBITS_k k n (mkW s c r) = ALeave (mkW s c r).
Proof.
  intros k n s c r H0 Hb Hk. destruct k as [|k]; [lia|]. rewrite NEEDBITS_k_S.
  replace (ir_bits r <? n) with true by (symmetry; apply Z.ltb_lt; exact Hb). rewrite H0. reflexivity.
Qed.

Lemma NEEDBITS_stall : forall n s c r, ir_have r = 0 -> ir_bits r < n -> NEEDBITS n (mkW s c r) = ALeave (mkW s c r).
Proof. intros. unfold NEEDBITS. apply NEEDBITS_k_stall; [assumption|assumption|lia]. Qed.

Section Simple.
  Variable iv : ivariant.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Ltac sc_open E HS := unfold SC in HS; rewrite E in HS; sc_red_in HS.

  Lemma restall_HEAD : restall HEAD (arm_HEAD iv).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_HEAD. mrun gs_eq.
    replace (is_wrap s =? 0) with false by (symmetry; apply Z.eqb_neq; exact HWR).
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 16 s c r H0 HS). reflexivity.
  Qed.

  Lemma restall_DICTID : restall DICTID (arm_DICTID iv flush).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_DICTID.
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 32 s c r H0 HS). reflexivity.
  Qed.

  Lemma restall_TYPEDO_core : forall M, (M = TYPE \/ M = TYPEDO) -> restall M (arm_TYPEDO iv flush).
  Proof.
    intros M HM s c r HW HWR E H0 HS.
    assert (HS' : is_last s = 0 /\ ir_bits r < 3) by (unfold SC in HS; rewrite E in HS; destruct HM as [-> | ->]; sc_red_in HS; exact HS).
    destruct HS' as [L0 B3]. unfold arm_TYPEDO. mrun gs_eq. rewrite L0. change (negb (0 =? 0)) with false. cbv iota.
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 3 s c r H0 B3). reflexivity.
  Qed.

  Lemma restall_TYPEDO : restall TYPEDO (arm_TYPEDO iv flush).
  Proof. apply restall_TYPEDO_core. right; reflexivity. Qed.

  Lemma restall_TYPE : restall TYPE (arm_TYPE iv flush).
  Proof.
    intros s c r HW HWR E H0 HS. unfold arm_TYPE. destruct Hfl as [F1 F2]. rewrite F1, F2. cbn [orb]. rewrite Bool.andb_false_r.
    exact (restall_TYPEDO_core TYPE (or_introl eq_refl) s c r HW HWR E H0 HS).
  Qed.

  Lemma restall_STORED : restall STORED (arm_STORED iv flush).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. destruct HS as [M8 B32]. unfold arm_STORED.
    winv_open2 HW E HC HR. regs_open HR.
    mrun BYTEBITS_eq. pose proof (land7_mod (ir_bits r) ltac:(lia)) as L7. rewrite L7, M8.
    rewrite Z.shiftr_0_r, Z.sub_0_r. rewrite (wrap32_id (ir_bits r)) by lia.
    set (rb := irset_bits (irset_hold r (ir_hold r)) (ir_bits r)).
    assert (Erb : rb = r) by (subst rb; destruct r; reflexivity). rewrite Erb.
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 32 s c r H0 B32). reflexivity.
  Qed.

  Lemma restall_COPY : restall COPY arm_COPY.
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_COPY. mrun gs_eq. cbv zeta.
    replace (negb (is_length s =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; lia).
    mrun gr_eq. cbv zeta. rewrite H0.
    replace (0 <? is_length s) with true by (symmetry; apply Z.ltb_lt; exact HS).
    winv_open2 HW E HC HR. regs_open HR.
    replace (ir_left r <? 0) with false by (symmetry; apply Z.ltb_ge; exact RL).
    change (0 =? 0) with true. cbv iota. exists s, r. split; [reflexivity|apply RS_refl; exact H0].
  Qed.

  Lemma restall_COPY_ : restall COPY_ arm_COPY_.
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_COPY_. mrun set_mode_eq.
    winv_open2 HW E HC HR.
    destruct (restall_COPY (iset_mode s COPY) c r) as (s' & r' & EQ & HRS); [| sacc; exact HWR | reflexivity | exact H0 | unfold SC; sacc; sc_red; exact HS |].
    - winv_split; [core_keep HC; apply CORE_length; exact HC | exact HR | exact HMF | exact HWF | exact HWB].
    - exists s', r'. exact (conj EQ HRS).
  Qed.

  Lemma restall_TABLE : restall TABLE (arm_TABLE iv flush).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_TABLE.
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 14 s c r H0 HS). reflexivity.
  Qed.

  Lemma restall_LENLENS : restall LENLENS (arm_LENLENS iv flush).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. destruct HS as [Hlt B3]. unfold arm_LENLENS.
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite lenlens_while1_S. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    replace (is_have s <? is_ncode s) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 3 s c r H0 B3). reflexivity.
  Qed.

  Lemma restall_LENEXT : restall LENEXT (arm_LENEXT iv).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. destruct HS as [Xnz Bx]. unfold arm_LENEXT. mrun gs_eq.
    replace (negb (is_extra s =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Xnz).
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall (is_extra s) s c r H0 Bx). reflexivity.
  Qed.

  Lemma restall_DISTEXT : restall DISTEXT (arm_DISTEXT iv).
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. destruct HS as [Xnz Bx]. unfold arm_DISTEXT. mrun gs_eq.
    replace (negb (is_extra s =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact Xnz).
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall (is_extra s) s c r H0 Bx). reflexivity.
  Qed.

  Lemma restall_CHECK : restall CHECK arm_CHECK.
  Proof.
    intros s c r HW HWR E H0 HS. sc_open E HS. unfold arm_CHECK. mrun gs_eq.
    replace (negb (is_wrap s =? 0)) with true by (symmetry; apply Bool.negb_true_iff; apply Z.eqb_neq; exact HWR).
    exists s, r. split; [|apply RS_refl; exact H0].
    rewrite ?abind_assoc. unfold abind at 1. rewrite (NEEDBITS_stall 32 s c r H0 HS). reflexivity.
  Qed.
End Simple.

Section Decoders.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Lemma decode_pair_stall : forall ty (linkt : Z -> bool) s c r p root used (K : Z -> AM unit),
    TBLg ty (code_at s p) root used -> ty <> CODES -> REGS c r -> ir_have r = 0 ->
    ir_bits r < lneedg (code_at s p) root (ir_hold r) ->
    (forall here, linkt here = true ->
       ((exists sy, 0 <= sy < nsyms ty /\ code_op here = fst (sym_entry ty sy) /\ code_val here = snd (sym_entry ty sy)) \/ code_op here = 64) -> False) ->
    (forall here, linkt here = false -> 1 <= code_op here <= 15 -> False) ->
    exists r', (do here <- DECODE1 p root ;
                do here <- (if linkt here then
                              let last := here in
                              do here <- DECODE2 p last ;
                              DROPBITS (code_bits last) ;; add_back ivar_ref (code_bits last) ;; aret here
                            else aret here) ;
                K here)%am (mkW s c r) = ALeave (mkW s c r') /\ RS r r'.
  Proof.
    intros ty linkt s c r p root used K HT Hty HR H0 Hb Hlk Hnl. regs_open HR.
    pose proof (T_root _ _ _ _ HT) as HR15.
    unfold abind at 1.
    destruct (DECODE1_spec c s p ty root used HT r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    2:{ rewrite EQ. exists r1. split; [reflexivity|exact (RS_pulled r r1 H0 HP1)]. }
    rewrite EQ. cbv beta iota.
    destruct (pulled_have0 r r1 HP1 H0) as (_ & Hh1 & Eb1 & Ehd1 & _).
    destruct (root_cell ty _ _ used HT (ir_hold r1 mod 2 ^ root) (ridx_range _ _ _ _ HT _)) as (Hbits & RLk & RNk).
    rewrite <- Eh in Hbits, RLk, RNk.
    unfold abind at 1. destruct (linkt here) eqn:Clink.
    - assert (HLk : is_linkb here = true).
      { destruct (is_linkb here) eqn:Lk; [reflexivity|]. exfalso. destruct (RNk eq_refl) as [_ SH]. exact (Hlk here Clink SH). }
      rewrite ?abind_assoc. unfold abind at 1.
      destruct (DECODE2_spec c s p ty root used HT r1 here HR1 Eh HLk Hle)
        as [(r2 & here2 & EQ2 & HR2 & HP2 & Eh2 & Hsb & Hle2 & Hb2)|(r2 & EQ2 & HR2 & HP2 & Hh2 & Hb2)].
      + exfalso. destruct (pulled_have0 r1 r2 HP2 Hh1) as (_ & _ & Eb2 & Ehd2 & _).
        unfold lneedg in Hb. rewrite <- Ehd1, <- Eh, HLk in Hb. unfold subix in Eh2. rewrite Ehd2 in Eh2. rewrite <- Eh2 in Hb. lia.
      + rewrite EQ2. exists r2. split; [reflexivity|]. exact (RS_trans r r1 r2 (RS_pulled r r1 H0 HP1) (RS_pulled r1 r2 Hh1 HP2)).
    - exfalso. assert (HLk : is_linkb here = false).
      { destruct (is_linkb here) eqn:Lk; [|reflexivity]. exfalso. destruct (RLk eq_refl) as (_ & Hop & _). exact (Hnl here Clink ltac:(lia)). }
      unfold lneedg in Hb. rewrite <- Ehd1, <- Eh, HLk in Hb. lia.
  Qed.

  Lemma restall_LEN : restall LEN (arm_LEN ivar_ref).
  Proof.
    intros s c r HW HWR E H0 HS. unfold SC in HS. rewrite E in HS. sc_red_in HS. unfold arm_LEN.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb).
    mrun gr_eq. rewrite H0. change (6 <=? 0) with false. rewrite Bool.andb_false_r. cbn [andb].
    mrun set_back_ref.
    destruct (cpok_TBLg LENS s (is_lencode s) (is_lenbits s) (proj1 Htb)) as (used & HT & _).
    mrun gs_eq. sacc.
    destruct (decode_pair_stall LENS (fun here => negb (code_op here =? 0) && (Z.land (code_op here) 240 =? 0))
                (iset_back s 0) c r (is_lencode s) (is_lenbits s) used
                (fun here => DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
                             us (fun s0 => iset_length s0 (code_val here)) ;;
                             if code_op here =? 0 then set_mode LIT
                             else if negb (Z.land (code_op here) 32 =? 0) then set_back ivar_ref (-1) ;; set_mode TYPE
                             else if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_literal_length_code
                             else us (fun s0 => iset_extra s0 (Z.land (code_op here) 15)) ;; set_mode LENEXT ;; arm_LENEXT ivar_ref)%am
                HT ltac:(discriminate) HR H0) as (r' & EQ & HRS).
    - rewrite <- lneed_lneedg. exact HS.
    - intros here C SH. apply andb_prop in C as [C1 C2]. apply Bool.negb_true_iff in C1. apply Z.eqb_neq in C1. apply Z.eqb_eq in C2.
      exact (notlink_land240 LENS here SH ltac:(discriminate) C1 C2).
    - intros here C Hop. rewrite (land240_small (code_op here) ltac:(lia)) in C.
      replace (code_op here =? 0) with false in C by (symmetry; apply Z.eqb_neq; lia). discriminate C.
    - exists (iset_back s 0), r'. split; [exact EQ|exact HRS].
  Qed.

  Lemma restall_LEN_ : restall LEN_ (arm_LEN_ ivar_ref).
  Proof.
    intros s c r HW HWR E H0 HS. unfold SC in HS. rewrite E in HS. sc_red_in HS. unfold arm_LEN_. mrun set_mode_eq.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hb8 & Htb).
    destruct (restall_LEN (iset_mode s LEN) c r) as (s' & r' & EQ & HRS); [| sacc; exact HWR | reflexivity | exact H0 | unfold SC; sacc; sc_red; exact HS |].
    - winv_split; [core_keep HC; apply CORE_length; exact HC | exact HR | | exact HWF | exact HWB].
      split; [common_keep HCm|]. split; [left; exact Hb8|tables_keep Htb].
    - exists s', r'. exact (conj EQ HRS).
  Qed.

  Lemma restall_DIST : restall DIST (arm_DIST ivar_ref).
  Proof.
    intros s c r HW HWR E H0 HS. unfold SC in HS. rewrite E in HS. sc_red_in HS. unfold arm_DIST.
    winv_open2 HW E HC HR. destruct HMF as (HCm & Hbx & Htb & HL).
    destruct (cpok_TBLg DISTS s (is_distcode s) (is_distbits s) (proj2 Htb)) as (used & HT & _).
    mrun gs_eq.
    destruct (decode_pair_stall DISTS (fun here => Z.land (code_op here) 240 =? 0)
                s c r (is_distcode s) (is_distbits s) used
                (fun here => DROPBITS (code_bits here) ;; add_back ivar_ref (code_bits here) ;;
                             if negb (Z.land (code_op here) 64 =? 0) then go_bad MSG_invalid_distance_code
                             else us (fun s0 => iset_extra (iset_offset s0 (code_val here)) (Z.land (code_op here) 15)) ;;
                                  set_mode DISTEXT ;; arm_DISTEXT ivar_ref)%am
                HT ltac:(discriminate) HR H0) as (r' & EQ & HRS).
    - rewrite <- lneed_lneedg. exact HS.
    - intros here C SH. apply Z.eqb_eq in C.
      apply (notlink_land240 DISTS here SH ltac:(discriminate)); [|exact C].
      destruct SH as [[sy (Hsy & Hop & _)]|Hop]; [|rewrite Hop; discriminate].
      cbn [nsyms] in Hsy. pose proof (dists_sym_cases sy Hsy) as L. destruct (sym_entry DISTS sy) as [op v]. cbn [fst] in Hop. rewrite Hop. lia.
    - intros here C Hop. rewrite (land240_small (code_op here) ltac:(lia)) in C. discriminate C.
    - exists s, r'. split; [exact EQ|exact HRS].
  Qed.
End Decoders.

Section Codelens.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Lemma codelens_body_restall : forall s c r,
    CL s c r -> is_have s < is_nlen s + is_ndist s -> ir_have r = 0 -> ir_bits r < cneed s (ir_hold r) ->
    exists r', codelens_body (mkW s c r) = ALeave (mkW s c r') /\ RS r r'.
  Proof.
    intros s c r HCL Hlt H0 HS. pose proof HCL as (HC & HR & E & HCm & Hbx & Hnl & Hnd & Hh & HLs & HT & HWF & HWB).
    regs_open HR.
    destruct (cpok_TBLg CODES s (is_lencode s) (is_lenbits s) HT) as (used & HTg & _).
    pose proof (T_root _ _ _ _ HTg) as HR15.
    unfold codelens_body. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    destruct (DECODE1_spec c s (is_lencode s) CODES (is_lenbits s) used HTg r HR)
      as [(r1 & here & EQ & HR1 & HP1 & Eh & Hle & Hb1)|(r1 & EQ & HR1 & HP1 & Hh1 & Hb1)].
    2:{ unfold abind at 1. rewrite EQ. exists r1. split; [reflexivity|exact (RS_pulled r r1 H0 HP1)]. }
    unfold abind at 1. rewrite EQ. cbv beta.
    destruct (pulled_have0 r r1 HP1 H0) as (_ & Hh1 & Eb1 & Ehd1 & _).
    rewrite cneed_cneedg in HS. unfold cneedg in HS. rewrite <- Ehd1, <- Eh in HS.
    destruct (Z.ltb_spec (code_val here) 16) as [V16|V16].
    - exfalso. rewrite (cl_ext_lt16 _ V16) in HS. lia.
    - exists r1. split; [|exact (RS_pulled r r1 H0 HP1)].
      assert (GEN : forall e (m1 : AM (option (Z * Z))) (f : option (Z * Z) -> AM bool), cl_ext (code_val here) = e ->
                (abind (NEEDBITS (code_bits here + e) ;; m1) f (mkW s c r1))%am = ALeave (mkW s c r1)).
      { intros e m1 f He. rewrite abind_assoc. unfold abind at 1.
        rewrite (NEEDBITS_stall (code_bits here + e) s c r1 Hh1 ltac:(rewrite Eb1, <- He; exact HS)). reflexivity. }
      destruct (Z.eqb_spec (code_val here) 16) as [E16|E16].
      + apply GEN. rewrite E16. reflexivity.
      + destruct (Z.eqb_spec (code_val here) 17) as [E17|E17].
        * apply GEN. rewrite E17. reflexivity.
        * apply GEN. apply cl_ext_ge18. lia.
  Qed.

  Lemma restall_CODELENS : restall CODELENS (arm_CODELENS ivar_ref flush).
  Proof.
    intros s c r HW HWR E H0 HS. unfold SC in HS. rewrite E in HS. sc_red_in HS. destruct HS as [Hlt HS]. unfold arm_CODELENS.
    pose proof HW as HW0. winv_open2 HW E HC HR.
    destruct HMF as (HCm & Hbx & Hnl & Hnd & Hh & HLs & HT).
    assert (HCL : CL s c r).
    { unfold CL. repeat (split; [first [assumption | lia]|]). exact HWB. }
    destruct (codelens_body_restall s c r HCL Hlt H0 HS) as (r' & EQ & HRS).
    exists s, r'. split; [|exact HRS].
    unfold abind at 1. rewrite codelens_while_S. unfold abind at 1. rewrite gs_eq. cbn [w_s].
    replace (is_have s <? is_nlen s + is_ndist s) with true by (symmetry; apply Z.ltb_lt; exact Hlt).
    unfold abind at 1. rewrite EQ. reflexivity.
  Qed.
End Codelens.

Section Dispatch.
  Variable flush : Z.
  Hypothesis Hfl : (flush =? Z_BLOCK) = false /\ (flush =? Z_TREES) = false.

  Theorem dispatch_restall : forall s c r,
    WINV (mkW s c r) -> is_wrap s <> 0 -> ir_have r = 0 -> SC s (ir_hold r) (ir_bits r) ->
    exists s' r', dispatch ivar_ref flush (mkW s c r) = ALeave (mkW s' c r') /\ RS r r'.
  Proof.
    intros s c r HW HWR H0 HS. unfold dispatch. unfold abind. rewrite gs_eq. cbv beta zeta.
    Ltac try_mode lem HW HWR H0 HS :=
      lazymatch goal with |- exists s' r', ((if is_mode ?s =? ?M then _ else _) (mkW _ ?c ?r)) = _ /\ _ =>
        destruct (Z.eqb_spec (is_mode s) M) as [E|?NE];
        [first [ exact (lem s c r HW HWR E H0 HS)
               | exfalso; unfold SC in HS; rewrite E in HS; sc_red_in HS; exact HS ] |] end.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_DICTID ivar_ref flush) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_TYPE ivar_ref flush Hfl) HW HWR H0 HS. try_mode (restall_TYPEDO ivar_ref flush) HW HWR H0 HS.
    try_mode (restall_STORED ivar_ref flush) HW HWR H0 HS.
    try_mode restall_COPY_ HW HWR H0 HS. try_mode restall_COPY HW HWR H0 HS.
    try_mode (restall_TABLE ivar_ref flush) HW HWR H0 HS. try_mode (restall_LENLENS ivar_ref flush) HW HWR H0 HS.
    try_mode (restall_CODELENS flush) HW HWR H0 HS.
    try_mode restall_LEN_ HW HWR H0 HS. try_mode restall_LEN HW HWR H0 HS.
    try_mode (restall_LENEXT ivar_ref) HW HWR H0 HS. try_mode restall_DIST HW HWR H0 HS. try_mode (restall_DISTEXT ivar_ref) HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode restall_CHECK HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.
    try_mode (restall_HEAD ivar_ref) HW HWR H0 HS. try_mode (restall_HEAD ivar_ref) HW HWR H0 HS.

    exfalso. unfold SC in HS.
    repeat match goal with N : is_mode s <> ?K |- _ => rewrite (proj2 (Z.eqb_neq _ _) N) in HS; clear N end.
    cbn [orb] in HS. exact HS.
  Qed.
End Dispatch.
