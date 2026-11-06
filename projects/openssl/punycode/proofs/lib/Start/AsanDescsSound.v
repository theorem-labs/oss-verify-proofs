(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.openssl.punycode.lib.Common Require Import PropExec SeqExec StoreOk ShapeAlg AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSound2 AsanPlanSoundSums.
From OSSVerify.Proofs.openssl.punycode.lib.Start Require Import AsanDescs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import AX2. Import AX2S. Import AP. Import APS. Import DSC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Module DSS.

Record dfields := DF { f_b : Z; f_sz : Z; f_w : Z; f_dy : Z; f_lo : Z; f_od : Z }.
Definition tof (od : Z) : Z := (od + 1) mod DBIG.

(* [comment removed for export] *)
Definition ds_in (s : dstat) (f : dfields) : Prop :=
  (d_b0 s <= f_b f <= d_b1 s) /\ (d_s0 s <= f_sz f <= d_s1 s) /\ (d_w0 s <= f_w f <= d_w1 s)
  /\ (d_dy0 s <= f_dy f <= d_dy1 s) /\ (d_lo0 s <= f_lo f <= d_lo1 s)
  /\ (d_t0 s <= tof (f_od f) <= d_t1 s) /\ (2 <= tof (f_od f) -> d_p0 s <= tof (f_od f))
  /\ (d_n0 s <= f_w f / 8 - f_sz f / 8 <= d_n1 s)
  /\ (d_e0 s <= (f_b f + f_w f) / 8 <= d_e1 s)
  /\ (d_al s = true -> f_b f mod 32 = 0 /\ f_w f mod 32 = 0).
Definition ds_le (s s' : dstat) : Prop := forall f, ds_in s f -> ds_in s' f.

Lemma ds_add_le : forall s b sz w dy lo od, ds_le s (ds_add s b sz w dy lo od).
Proof.
  intros s b sz w dy lo od f (H1 & H2 & H3 & H4 & H5 & H6 & H7 & H8 & H8e & H9).
  unfold ds_in, ds_add. cbn [d_b0 d_b1 d_s0 d_s1 d_w0 d_w1 d_dy0 d_dy1 d_lo0 d_lo1 d_t0 d_t1 d_p0 d_n0 d_n1 d_e0 d_e1 d_al].
  repeat split; try lia.
  - intros Ht. specialize (H7 Ht). destruct (Z.leb 2 ((od + 1) mod DBIG)); lia.
  - apply H9. destruct (d_al s); [reflexivity | discriminate].
  - apply H9. destruct (d_al s); [reflexivity | discriminate].
Qed.

Lemma ds_add_in : forall s b sz w dy lo od, ds_in (ds_add s b sz w dy lo od) (DF b sz w dy lo od).
Proof.
  intros s b sz w dy lo od. unfold ds_in, ds_add, tof.
  cbn [d_b0 d_b1 d_s0 d_s1 d_w0 d_w1 d_dy0 d_dy1 d_lo0 d_lo1 d_t0 d_t1 d_p0 d_n0 d_n1 d_e0 d_e1 d_al f_b f_sz f_w f_dy f_lo f_od].
  repeat split; try lia.
  all: intros Ht; destruct (Z.leb 2 ((od + 1) mod DBIG)) eqn:Hb; [lia | apply Z.leb_gt in Hb; lia].
Qed.

Section Scan.
Variable segs : list Segment.
#[local] Notation rd64 := (DSC.rd64 segs).
#[local] Notation dscan := (DSC.dscan segs).

Definition fields_at (a : Z) (f : dfields) : Prop :=
  rd64 a = Some (f_b f) /\ rd64 (a + 8) = Some (f_sz f) /\ rd64 (a + 16) = Some (f_w f)
  /\ rd64 (a + 40) = Some (f_dy f) /\ rd64 (a + 48) = Some (f_lo f) /\ rd64 (a + 56) = Some (f_od f).

Lemma dscan_spec : forall n a s s', dscan n a s = Some s' ->
  ds_le s s' /\ forall j, (j < n)%nat -> exists f, fields_at (a + 64 * Z.of_nat j) f /\ ds_in s' f.
Proof.
  induction n as [|n IH]; intros a s s' H; cbn [DSC.dscan] in H.
  - injection H as <-. split; [intros f Hf; exact Hf | intros j Hj; lia].
  - destruct (rd64 a) as [b|] eqn:R0; [|discriminate].
    destruct (rd64 (a + 8)) as [sz|] eqn:R1; [|discriminate].
    destruct (rd64 (a + 16)) as [w|] eqn:R2; [|discriminate].
    destruct (rd64 (a + 40)) as [dy|] eqn:R3; [|discriminate].
    destruct (rd64 (a + 48)) as [lo|] eqn:R4; [|discriminate].
    destruct (rd64 (a + 56)) as [od|] eqn:R5; [|discriminate].
    destruct (IH _ _ _ H) as [Hle Hall]. split.
    + intros f Hf. apply Hle. apply ds_add_le. exact Hf.
    + intros j Hj. destruct j as [|j].
      * exists (DF b sz w dy lo od). split.
        -- unfold fields_at. cbn [f_b f_sz f_w f_dy f_lo f_od]. change (Z.of_nat 0) with 0. rewrite Z.mul_0_r, Z.add_0_r.
           repeat split; assumption.
        -- apply Hle. apply ds_add_in.
      * destruct (Hall j ltac:(lia)) as [f [Hf Hin]]. exists f. split; [|exact Hin].
        replace (a + 64 * Z.of_nat (S j)) with (a + 64 + 64 * Z.of_nat j) by lia. exact Hf.
Qed.

(* [comment removed for export] *)
Lemma rd64_rdn : forall (M : word -> option byte) a z,
  0 <= a -> a + 8 <= 2 ^ 64 ->
  (forall i, a <= i < a + 8 -> M (Z_to_bv 64 i) = None) ->
  rd64 a = Some z ->
  rdn segs M (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z)) /\ 0 <= z < 2 ^ 64.
Proof.
  intros M a z Ha0 Ha1 Hnone H. unfold DSC.rd64 in H.
  destruct (img_bytes segs a 8) as [zs|] eqn:Hi; [|discriminate]. injection H as <-.
  assert (Hu : bv_unsigned (Z_to_bv 64 a) = a) by (apply u64_lit; lia).
  destruct (rdn_img segs M 8 (Z_to_bv 64 a) zs) as (bs & Hrd & Hmap).
  - rewrite Hu. change (Z.of_nat 8) with 8. lia.
  - intros j Hj. rewrite Hu. apply Hnone. lia.
  - rewrite Hu. exact Hi.
  - pose proof (rdn_length _ _ _ _ _ Hrd) as Hlen.
    rewrite <- Hmap, zbytes_map. split.
    + rewrite Hrd. f_equal. symmetry. apply APSX.word_to_le_bytes_of_bytes_n; [exact Hlen | lia].
    + pose proof (AX2S.bytes_le_to_Z_bound bs) as Hb. rewrite Hlen in Hb. change (2 ^ (8 * Z.of_nat 8)) with (2 ^ 64) in Hb. exact Hb.
Qed.
End Scan.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable ISP : Z.
Variable FS0 : Fs.Fs.
Hypothesis NX0_spw : AP.expr_vars_lt nx0 e_spw = true.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Variable ST : Z -> Z -> option dstat.
Hypothesis ST_ok : DSC.st_ok SEGS ST.

#[local] Notation cs_ok := (APS.cs_ok SEGS A LIMIT SINV argH ISP FS0).

Lemma img_cov_none : forall E M k a b,
  know_ok SEGS E M k -> img_cov k a b = true -> forall i, a <= i < b -> M (Z_to_bv 64 i) = None.
Proof.
  intros E M k a b HK H i Hi. unfold img_cov in H. apply existsb_exists in H as [K [HinK HKb]].
  destruct K as [| | |lo hi| | | | | |]; try discriminate.
  apply andb_prop in HKb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2.
  pose proof (proj1 (Forall_forall _ _) HK _ HinK) as HK1. cbn [kentry_ok] in HK1. destruct HK1 as (_ & _ & HK1).
  apply HK1. lia.
Qed.

(* [comment removed for export] *)
Lemma descs_pre_sound : forall E cs R FULL model tb n J s,
  cs_ok E cs R FULL model -> descs_pre nx0 cs tb n J = true -> ST tb n = Some s ->
  fresh_ok nx0 cs = true /\ (J < nxt cs)%nat /\ 0 <= tb /\ tb + 64 * n < 2 ^ 40 /\
  exists f, 0 <= bv_unsigned (ev E J) < n /\ ds_in s f /\
    forall off z, In (off, z) [(0, f_b f); (8, f_sz f); (16, f_w f); (40, f_dy f); (48, f_lo f); (56, f_od f)] ->
      rdn SEGS (Mr A argH E cs model FULL) (Z_to_bv 64 (tb + 64 * bv_unsigned (ev E J) + off)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z))
      /\ 0 <= z < 2 ^ 64.
Proof.
  intros E cs R FULL model tb n J s HC Hpre Hst. unfold descs_pre in Hpre.
  repeat match type of Hpre with (_ && _)%bool = true => apply andb_prop in Hpre as [Hpre ?X] end.
  apply Z.leb_le in Hpre. apply Z.ltb_lt in X3. apply Nat.ltb_lt in X2.
  destruct (erange (kn cs) (EVar J)) as [[lo hi]|] eqn:Hr; [|discriminate].
  apply andb_prop in X as [Hlo Hhi]. apply Z.leb_le in Hlo. apply Z.ltb_lt in Hhi.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (erange_sound SEGS E _ (kn cs) (EVar J) lo hi HK Hr) as HJ. cbn [edenot] in HJ.
  split; [exact X0|]. split; [exact X2|]. split; [exact Hpre|]. split; [exact X3|].
  set (j := bv_unsigned (ev E J)) in *.
  pose proof (ST_ok tb n s Hst) as Hscan. unfold DSC.st_scan in Hscan.
  destruct (dscan_spec SEGS _ _ _ _ Hscan) as [_ Hall].
  destruct (Hall (Z.to_nat j) ltac:(lia)) as [f [Hf Hin]]. rewrite Z2Nat.id in Hf by lia.
  exists f. split; [lia|]. split; [exact Hin|].
  intros off z Hoz.
  assert (Hnone : forall i, tb <= i < tb + 64 * n -> Mr A argH E cs model FULL (Z_to_bv 64 i) = None)
    by (apply (img_cov_none E _ (kn cs)); assumption).
  destruct Hf as (F0 & F1 & F2 & F3 & F4 & F5).
  cbn [In] in Hoz.
  assert (Hrd : DSC.rd64 SEGS (tb + 64 * j + off) = Some z /\ 0 <= off <= 56).
  { destruct Hoz as [Hoz|[Hoz|[Hoz|[Hoz|[Hoz|[Hoz|[]]]]]]]; injection Hoz as <- <-; (split; [|lia]); rewrite ?Z.add_0_r; assumption. }
  destruct Hrd as [Hrd Hoff].
  apply (rd64_rdn SEGS); [lia | lia | | exact Hrd].
  intros i Hi. apply Hnone. lia.
Qed.

(* [comment removed for export] *)
Lemma desc_kword : forall E' M tb n J j off z e,
  bv_unsigned (ev E' J) = j -> 0 <= j < n -> 0 <= tb -> tb + 64 * n < 2 ^ 40 -> 0 <= off <= 56 ->
  rdn SEGS M (Z_to_bv 64 (tb + 64 * j + off)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z)) ->
  edenot E' e = Z_to_bv 64 z ->
  kentry_ok SEGS E' M (KWord (SA (escale 64 (EVar J)) (tb + off)) 8 e).
Proof.
  intros E' M tb n J j off z e HJ Hj Htb Hn Hoff Hrd He. cbn [kentry_ok].
  assert (Hb : bv_unsigned (edenot E' (escale 64 (EVar J))) = 64 * j).
  { unfold escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u64_lit, HJ by lia. apply Z.mod_small. lia. }
  assert (Hfl : flat E' (SA (escale 64 (EVar J)) (tb + off)) (Z.of_nat 8)).
  { unfold flat, estart. cbn [a_base a_off]. rewrite Hb. change (Z.of_nat 8) with 8. lia. }
  split; [lia|]. split; [exact Hfl|].
  assert (Had : adenot E' (SA (escale 64 (EVar J)) (tb + off)) = Z_to_bv 64 (tb + 64 * j + off)).
  { apply bv_eq. rewrite (flat_u E' _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite Hb, u64_lit by lia. lia. }
  rewrite Had, He. exact Hrd.
Qed.

Theorem node_descs_sound : forall args, node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => DSC.node_descs ST nx0 cs args).
Proof using All.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold DSC.node_descs in Hn.
  destruct args as [|[tb| | | | | | |] [|[n| | | | | | |] [|[|J| | | | | |] [|? ?]]]]; try discriminate.
  destruct (descs_pre nx0 cs tb n J) eqn:Hpre; [|discriminate]. cbn [negb] in Hn.
  destruct (ST tb n) as [s|] eqn:Hst; [|discriminate].
  destruct (stat_pre s) eqn:Hsp; [|discriminate]. cbn [negb] in Hn.
  destruct (descs_pre_sound E cs R FULL model tb n J s HC Hpre Hst) as (Hfresh & HJv & Htb & Hn40 & f & Hj & Hin & Hrd).
  unfold stat_pre in Hsp.
  repeat match type of Hsp with (_ && _)%bool = true => apply andb_prop in Hsp as [Hsp ?X] end.
  apply Z.ltb_lt in X, X0, X1. apply Z.leb_le in X2. apply Z.eqb_eq in X3, X4.
  destruct Hin as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I8e & I9). destruct (I9 Hsp) as [Ib32 Iw32].
  pose proof (Hrd 0 _ ltac:(cbn [In]; tauto)) as [Rb Bb].
  pose proof (Hrd 8 _ ltac:(cbn [In]; tauto)) as [Rsz Bsz].
  pose proof (Hrd 16 _ ltac:(cbn [In]; tauto)) as [Rw Bw].
  pose proof (Hrd 40 _ ltac:(cbn [In]; tauto)) as [Rdy Bdy].
  pose proof (Hrd 48 _ ltac:(cbn [In]; tauto)) as [Rlo Blo].
  pose proof (Hrd 56 _ ltac:(cbn [In]; tauto)) as [Rod Bod].
  set (j := bv_unsigned (ev E J)) in *.
  destruct (APS.fresh_ok_parts nx0 cs Hfresh) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  set (v := nxt cs) in *.
  set (E' := ext_list E v [Z_to_bv 64 (f_b f / 32); Z_to_bv 64 (f_sz f / 8); Z_to_bv 64 (f_w f / 32); Z_to_bv 64 (f_sz f mod 8);
                           Z_to_bv 64 (tof (f_od f))]).
  assert (Hag : env_agree v E E') by apply ext_list_agree.
  pose proof (APS.cs_ok_agree SEGS A nx0 LIMIT NX0_spw SINV argH ISP argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hfresh HC) as HC'.
  assert (HMr : APS.Mr A argH E' cs model FULL = APS.Mr A argH E cs model FULL).
  { unfold APS.Mr. rewrite (APS.hid_agree A nx0 argH argH_agree v E E' cs model Hag Fle Fallow). reflexivity. }
  assert (HJ' : bv_unsigned (ev E' J) = j) by (unfold j; f_equal; symmetry; apply (proj1 Hag); exact HJv).
  assert (EV0 : ev E' v = Z_to_bv 64 (f_b f / 32)) by (unfold E'; rewrite <- (Nat.add_0_r v) at 2; rewrite ext_list_at by (cbn; lia); reflexivity).
  assert (EV1 : ev E' (S v) = Z_to_bv 64 (f_sz f / 8)) by (unfold E'; replace (S v) with (v + 1)%nat by lia; rewrite ext_list_at by (cbn; lia); reflexivity).
  assert (EV2 : ev E' (S (S v)) = Z_to_bv 64 (f_w f / 32)) by (unfold E'; replace (S (S v)) with (v + 2)%nat by lia; rewrite ext_list_at by (cbn; lia); reflexivity).
  assert (EV3 : ev E' (S (S (S v))) = Z_to_bv 64 (f_sz f mod 8)) by (unfold E'; replace (S (S (S v))) with (v + 3)%nat by lia; rewrite ext_list_at by (cbn; lia); reflexivity).
  assert (EV4 : ev E' (S (S (S (S v)))) = Z_to_bv 64 (tof (f_od f))) by (unfold E'; replace (S (S (S (S v)))) with (v + 4)%nat by lia; rewrite ext_list_at by (cbn; lia); reflexivity).
  assert (Q32 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 32 < 2 ^ 64) by (intros x Hx; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Q8 : forall x, 0 <= x < 2 ^ 64 -> 0 <= x / 8 < 2 ^ 64) by (intros x Hx; split; [apply Z.div_pos; lia | apply Z.div_lt_upper_bound; lia]).
  assert (Ht : 0 <= tof (f_od f) < 2 ^ 64) by (unfold tof, DBIG; apply Z.mod_pos_bound; lia).
  (* [comment removed for export] *)
  assert (Vb : edenot E' (escale 32 (EVar v)) = Z_to_bv 64 (f_b f)).
  { apply bv_eq. unfold escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite EV0, !u64_lit by (try apply Q32; lia).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Q32; lia] | pose proof (Z.mul_div_le (f_b f) 32 ltac:(lia)); lia]].
    pose proof (Z.div_mod (f_b f) 32 ltac:(lia)). lia. }
  assert (Vw : edenot E' (escale 32 (EVar (S (S v)))) = Z_to_bv 64 (f_w f)).
  { apply bv_eq. unfold escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite EV2, !u64_lit by (try apply Q32; lia).
    rewrite Z.mod_small; [|split; [apply Z.mul_nonneg_nonneg; [lia | apply Q32; lia] | pose proof (Z.mul_div_le (f_w f) 32 ltac:(lia)); lia]].
    pose proof (Z.div_mod (f_w f) 32 ltac:(lia)). lia. }
  assert (Vsz : edenot E' (eadd (escale 8 (EVar (S v))) (EVar (S (S (S v))))) = Z_to_bv 64 (f_sz f)).
  { apply bv_eq. unfold eadd, escale. rewrite mkAlu_denot, u_add64, mkMd_denot, u_mul64. cbn [edenot]. rewrite EV1, EV3.
    pose proof (Z.mod_pos_bound (f_sz f) 8 ltac:(lia)) as Hm. pose proof (Z.div_mod (f_sz f) 8 ltac:(lia)) as Hd.
    pose proof (Z.mul_div_le (f_sz f) 8 ltac:(lia)) as Hle.
    rewrite !u64_lit by (try apply Q8; lia).
    rewrite (Z.mod_small (8 * (f_sz f / 8))) by (split; [apply Z.mul_nonneg_nonneg; [lia | apply Q8; lia] | lia]).
    rewrite Z.mod_small by lia. lia. }
  assert (Vn : bv_unsigned (edenot E' (esub (escale 4 (EVar (S (S v)))) (EVar (S v)))) = f_w f / 8 - f_sz f / 8).
  { unfold esub, escale. rewrite mkAlu_denot, u_sub64, mkMd_denot, u_mul64. cbn [edenot]. rewrite EV2, EV1.
    rewrite !u64_lit by (try apply Q32; try apply Q8; lia).
    assert (Hw8 : f_w f / 8 = 4 * (f_w f / 32)).
    { pose proof (Z.div_mod (f_w f) 32 ltac:(lia)) as Hd. rewrite Iw32, Z.add_0_r in Hd.
      rewrite Hd at 1. replace (32 * (f_w f / 32)) with ((4 * (f_w f / 32)) * 8) by lia. apply Z.div_mul. lia. }
    pose proof (Q8 (f_w f) Bw) as Hq. pose proof (Q8 (f_sz f) Bsz) as Hq'.
    rewrite (Z.mod_small (4 * (f_w f / 32))) by lia. rewrite Z.mod_small by lia. lia. }
  assert (Ve : bv_unsigned (edenot E' (eadd (escale 4 (EVar v)) (escale 4 (EVar (S (S v)))))) = (f_b f + f_w f) / 8).
  { unfold eadd, escale. rewrite mkAlu_denot, u_add64, !mkMd_denot, !u_mul64. cbn [edenot]. rewrite EV0, EV2.
    rewrite !u64_lit by (try apply Q32; lia).
    pose proof (Z.div_mod (f_b f) 32 ltac:(lia)) as Hdb. rewrite Ib32, Z.add_0_r in Hdb.
    pose proof (Z.div_mod (f_w f) 32 ltac:(lia)) as Hdw. rewrite Iw32, Z.add_0_r in Hdw.
    pose proof (Q32 (f_b f) Bb) as Hqb. pose proof (Q32 (f_w f) Bw) as Hqw.
    assert (Hsum : (f_b f + f_w f) / 8 = 4 * (f_b f / 32) + 4 * (f_w f / 32)).
    { rewrite Hdb at 1. rewrite Hdw at 1. replace (32 * (f_b f / 32) + 32 * (f_w f / 32)) with ((4 * (f_b f / 32) + 4 * (f_w f / 32)) * 8) by lia.
      apply Z.div_mul. lia. }
    rewrite (Z.mod_small (4 * (f_b f / 32))) by lia. rewrite (Z.mod_small (4 * (f_w f / 32))) by lia.
    rewrite Z.mod_small by lia. lia. }
  (* [comment removed for export] *)
  assert (KW : forall off z e, 0 <= off <= 56 ->
             rdn SEGS (Mr A argH E cs model FULL) (Z_to_bv 64 (tb + 64 * j + off)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 z)) ->
             edenot E' e = Z_to_bv 64 z ->
             kentry_ok SEGS E' (Mr A argH E' cs model FULL) (KWord (SA (escale 64 (EVar J)) (tb + off)) 8 e)).
  { intros off z e Hoff Hr He. rewrite HMr. apply (desc_kword E' _ tb n J j off z e); assumption. }
  assert (HKf : know_ok SEGS E' (Mr A argH E' cs model FULL)
                  ([KWord (SA (escale 64 (EVar J)) tb) 8 (escale 32 (EVar v));
                    KWord (SA (escale 64 (EVar J)) (tb + 8)) 8 (eadd (escale 8 (EVar (S v))) (EVar (S (S (S v)))));
                    KWord (SA (escale 64 (EVar J)) (tb + 16)) 8 (escale 32 (EVar (S (S v))));
                    KWord (SA (escale 64 (EVar J)) (tb + 40)) 8 (ELit (d_dy0 s)); KWord (SA (escale 64 (EVar J)) (tb + 48)) 8 (ELit (d_lo0 s))])).
  { unfold know_ok. repeat (apply Forall_cons; [|]); [ | | | | | apply Forall_nil].
    - pose proof (KW 0 (f_b f) (escale 32 (EVar v)) ltac:(lia) Rb Vb) as X5. rewrite Z.add_0_r in X5. exact X5.
    - apply (KW 8 (f_sz f)); [lia | exact Rsz | exact Vsz].
    - apply (KW 16 (f_w f)); [lia | exact Rw | exact Vw].
    - apply (KW 40 (f_dy f)); [lia | exact Rdy | cbn [edenot]; f_equal; lia].
    - apply (KW 48 (f_lo f)); [lia | exact Rlo | cbn [edenot]; f_equal; lia]. }
  assert (HKr : know_ok SEGS E' (Mr A argH E' cs model FULL)
                  [KRange (EVar v) (d_b0 s / 32) (d_b1 s / 32); KRange (EVar (S v)) (d_s0 s / 8) (d_s1 s / 8);
                   KRange (EVar (S (S v))) (d_w0 s / 32) (d_w1 s / 32); KRange (EVar (S (S (S v)))) 0 7;
                   KRange (esub (escale 4 (EVar (S (S v)))) (EVar (S v))) (d_n0 s) (d_n1 s);
                       KRange (eadd (escale 4 (EVar v)) (escale 4 (EVar (S (S v))))) (d_e0 s) (d_e1 s)]).
  { unfold know_ok. repeat (apply Forall_cons; [|]); [ | | | | | | apply Forall_nil]; cbn [kentry_ok].
    - cbn [edenot]. rewrite EV0, u64_lit by (apply Q32; lia). split; apply Z.div_le_mono; lia.
    - cbn [edenot]. rewrite EV1, u64_lit by (apply Q8; lia). split; apply Z.div_le_mono; lia.
    - cbn [edenot]. rewrite EV2, u64_lit by (apply Q32; lia). split; apply Z.div_le_mono; lia.
    - cbn [edenot]. rewrite EV3. pose proof (Z.mod_pos_bound (f_sz f) 8 ltac:(lia)). rewrite u64_lit by lia. lia.
    - rewrite Vn. lia.
    - rewrite Ve. lia. }
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC') as HK'.
  assert (Hag2 : env_agree nx0 E E' /\ env_agree (nxt cs) E E') by (split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]).
  destruct (Z.eqb (d_t0 s) (d_t1 s)) eqn:Hteq.
  - (* [comment removed for export] *)
    apply Z.eqb_eq in Hteq.
    apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
    apply (Hk E' R FULL model Hag2); [|reflexivity].
    assert (HKo : kentry_ok SEGS E' (Mr A argH E' cs model FULL) (KWord (SA (escale 64 (EVar J)) (tb + 56)) 8 (ELit ((d_t0 s - 1) mod DBIG)))).
    { apply (KW 56 (f_od f)); [lia | exact Rod |]. cbn [edenot].
      replace ((d_t0 s - 1) mod DBIG) with (f_od f); [reflexivity|].
      assert (Hto : tof (f_od f) = d_t0 s) by lia. rewrite <- Hto. unfold tof, DBIG in *.
      destruct (Z.eq_dec (f_od f) (2 ^ 64 - 1)) as [Heq|Hne].
      - rewrite Heq. reflexivity.
      - rewrite (Z.mod_small (f_od f + 1)) by lia. replace (f_od f + 1 - 1) with (f_od f) by lia. rewrite Z.mod_small by lia. reflexivity. }
    assert (HKall : know_ok SEGS E' (Mr A argH E' cs model FULL)
              (([KWord (SA (escale 64 (EVar J)) tb) 8 (escale 32 (EVar v));
                 KWord (SA (escale 64 (EVar J)) (tb + 8)) 8 (eadd (escale 8 (EVar (S v))) (EVar (S (S (S v)))));
                 KWord (SA (escale 64 (EVar J)) (tb + 16)) 8 (escale 32 (EVar (S (S v))));
                 KWord (SA (escale 64 (EVar J)) (tb + 40)) 8 (ELit (d_dy0 s)); KWord (SA (escale 64 (EVar J)) (tb + 48)) 8 (ELit (d_lo0 s))]
                ++ KWord (SA (escale 64 (EVar J)) (tb + 56)) 8 (ELit ((d_t0 s - 1) mod DBIG))
                   :: [KRange (EVar v) (d_b0 s / 32) (d_b1 s / 32); KRange (EVar (S v)) (d_s0 s / 8) (d_s1 s / 8);
                       KRange (EVar (S (S v))) (d_w0 s / 32) (d_w1 s / 32); KRange (EVar (S (S (S v)))) 0 7;
                       KRange (esub (escale 4 (EVar (S (S v)))) (EVar (S v))) (d_n0 s) (d_n1 s);
                       KRange (eadd (escale 4 (EVar v)) (escale 4 (EVar (S (S v))))) (d_e0 s) (d_e1 s)]) ++ kn cs)).
    { unfold know_ok. apply Forall_app. split; [|exact HK']. apply Forall_app. split; [exact HKf|]. constructor; [exact HKo | exact HKr]. }
    destruct HC'; constructor; cbn [bump add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know s_pc s_next kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
  - (* [comment removed for export] *)
    apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
    apply (Hk E' R FULL model Hag2); [|reflexivity].
    assert (HKo : kentry_ok SEGS E' (Mr A argH E' cs model FULL) (KWord (SA (escale 64 (EVar J)) (tb + 56)) 8 (eaddz (EVar (S (S (S (S v))))) (-1)))).
    { apply (KW 56 (f_od f)); [lia | exact Rod |]. apply bv_eq. unfold eaddz. rewrite mkAlu_denot, u_add64. cbn [edenot]. rewrite EV4.
      change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1). rewrite !u64_lit by lia. unfold tof, DBIG in *.
      destruct (Z.eq_dec (f_od f) (2 ^ 64 - 1)) as [Heq|Hne].
      - rewrite Heq. reflexivity.
      - rewrite (Z.mod_small (f_od f + 1)) by lia. replace (f_od f + 1 + (2 ^ 64 - 1)) with (f_od f + 1 * 2 ^ 64) by lia.
        rewrite Z.mod_add by lia. apply Z.mod_small. lia. }
    assert (HKt : kentry_ok SEGS E' (Mr A argH E' cs model FULL) (KRange (EVar (S (S (S (S v))))) (d_t0 s) (d_t1 s))).
    { cbn [kentry_ok edenot]. rewrite EV4, u64_lit by lia. lia. }
    assert (HKall : know_ok SEGS E' (Mr A argH E' cs model FULL)
              (([KWord (SA (escale 64 (EVar J)) tb) 8 (escale 32 (EVar v));
                 KWord (SA (escale 64 (EVar J)) (tb + 8)) 8 (eadd (escale 8 (EVar (S v))) (EVar (S (S (S v)))));
                 KWord (SA (escale 64 (EVar J)) (tb + 16)) 8 (escale 32 (EVar (S (S v))));
                 KWord (SA (escale 64 (EVar J)) (tb + 40)) 8 (ELit (d_dy0 s)); KWord (SA (escale 64 (EVar J)) (tb + 48)) 8 (ELit (d_lo0 s))]
                ++ KWord (SA (escale 64 (EVar J)) (tb + 56)) 8 (eaddz (EVar (S (S (S (S v))))) (-1))
                   :: KRange (EVar (S (S (S (S v))))) (d_t0 s) (d_t1 s)
                   :: [KRange (EVar v) (d_b0 s / 32) (d_b1 s / 32); KRange (EVar (S v)) (d_s0 s / 8) (d_s1 s / 8);
                       KRange (EVar (S (S v))) (d_w0 s / 32) (d_w1 s / 32); KRange (EVar (S (S (S v)))) 0 7;
                       KRange (esub (escale 4 (EVar (S (S v)))) (EVar (S v))) (d_n0 s) (d_n1 s);
                       KRange (eadd (escale 4 (EVar v)) (escale 4 (EVar (S (S v))))) (d_e0 s) (d_e1 s)]) ++ kn cs)).
    { unfold know_ok. apply Forall_app. split; [|exact HK']. apply Forall_app. split; [exact HKf|]. constructor; [exact HKo|]. constructor; [exact HKt | exact HKr]. }
    destruct HC'; constructor; cbn [bump add_kn set_kn with_ss a_ss mk_ss s_regs s_log s_know s_pc s_next kn a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset]; try assumption; try reflexivity.
Qed.

(* [comment removed for export] *)
Theorem node_descs_refine_sound : forall args,
  node1_stmt SEGS A nx0 LIMIT SINV argH ISP FS0 always (fun cs => DSC.node_descs_refine SEGS ST nx0 cs args).
Proof using All.
  intros args cs cs' E R FULL model T HC _ Hn Hk. cbv beta in Hn. unfold DSC.node_descs_refine in Hn.
  destruct args as [|[tb| | | | | | |] [|[n| | | | | | |] [|[|J| | | | | |] [|[|t| | | | | |] [|? ?]]]]]; try discriminate.
  destruct (descs_pre nx0 cs tb n J) eqn:Hpre; [|discriminate]. cbn [negb] in Hn.
  destruct (ST tb n) as [s|] eqn:Hst; [|discriminate].
  destruct (kread8e SEGS (kn cs) (escale 64 (EVar J)) (tb + 56)) as [e|] eqn:Hrd8; [|discriminate].
  destruct (erange (kn cs) (EVar t)) as [[lo hi]|] eqn:Hrt; [|discriminate].
  destruct (expr_eqb e (eaddz (EVar t) (-1)) && Z.leb 2 lo)%bool eqn:Hc; [|discriminate].
  apply andb_prop in Hc as [He Hlo]. apply expr_eqb_eq in He. subst e. apply Z.leb_le in Hlo.
  apply (f_equal (fun o => match o with Some x => x | None => cs end)) in Hn. cbn in Hn. subst cs'.
  destruct (descs_pre_sound E cs R FULL model tb n J s HC Hpre Hst) as (Hfresh & HJv & Htb & Hn40 & f & Hj & Hin & Hrd).
  destruct Hin as (I1 & I2 & I3 & I4 & I5 & I6 & I7 & I8 & I8e & I9).
  pose proof (Hrd 56 _ ltac:(cbn [In]; tauto)) as [Rod Bod].
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (erange_sound SEGS E _ (kn cs) (EVar t) lo hi HK Hrt) as HT. cbn [edenot] in HT.
  set (j := bv_unsigned (ev E J)) in *.
  (* [comment removed for export] *)
  assert (Hb : bv_unsigned (edenot E (escale 64 (EVar J))) = 64 * j).
  { unfold escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u64_lit by lia. fold j. apply Z.mod_small. lia. }
  assert (Hfl : flat E (SA (escale 64 (EVar J)) (tb + 56)) (Z.of_nat 8)).
  { unfold flat, estart. cbn [a_base a_off]. rewrite Hb. change (Z.of_nat 8) with 8. lia. }
  assert (Had : adenot E (SA (escale 64 (EVar J)) (tb + 56)) = Z_to_bv 64 (tb + 64 * j + 56)).
  { apply bv_eq. rewrite (flat_u E _ _ Hfl). unfold estart. cbn [a_base a_off]. rewrite Hb, u64_lit by lia. lia. }
  unfold kread8e in Hrd8.
  pose proof (know_lookup_sound SEGS E _ (kn cs) (escale 64 (EVar J)) (tb + 56) 8 false [] [] HK ltac:(lia) ltac:(lia)) as X.
  destruct (know_lookup SEGS (kn cs) (escale 64 (EVar J)) (tb + 56) 8 false [] []) as [v0 scs hs|scs hs|] eqn:HL; try discriminate.
  destruct scs; [|discriminate]. injection Hrd8 as ->.
  destruct (X ltac:(constructor) Hfl) as (bs & Hrdk & Hlen & Hval).
  rewrite Had, Rod in Hrdk. injection Hrdk as <-.
  cbn [extz] in Hval. rewrite bytes_le_to_Z_8, Z_to_bv_bv_unsigned in Hval.
  (* [comment removed for export] *)
  assert (Htv : bv_unsigned (ev E t) = tof (f_od f)).
  { apply (f_equal bv_unsigned) in Hval. unfold eaddz in Hval. rewrite mkAlu_denot, u_add64 in Hval. cbn [edenot] in Hval.
    change (bv_unsigned (Z_to_bv 64 (-1))) with (2 ^ 64 - 1) in Hval. rewrite u64_lit in Hval by lia.
    pose proof (u64_range (ev E t)) as Ht. unfold tof, DBIG.
    destruct (Z.eq_dec (bv_unsigned (ev E t)) 0) as [H0|H0].
    - rewrite H0 in Hval. change ((0 + (2 ^ 64 - 1)) mod 2 ^ 64) with (2 ^ 64 - 1) in Hval. rewrite Hval, H0. reflexivity.
    - replace (bv_unsigned (ev E t) + (2 ^ 64 - 1)) with (bv_unsigned (ev E t) - 1 + 1 * 2 ^ 64) in Hval by lia.
      rewrite Z.mod_add, Z.mod_small in Hval by lia. rewrite Hval. replace (bv_unsigned (ev E t) - 1 + 1) with (bv_unsigned (ev E t)) by lia.
      symmetry. apply Z.mod_small. lia. }
  apply (Hk E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _))); [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH ISP FS0); [exact HC|].
  apply Forall_app. split; [|exact HK]. constructor; [|constructor].
  cbn [kentry_ok edenot]. rewrite Htv. split; [apply I7; lia | lia].
Qed.

End Sound.
End DSS.
