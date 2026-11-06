(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StoreOk RefMemcpyLib AgentLib AsanAcct.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanNodesMmLib.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2 AX2S APC AP APS APSX.
Open Scope Z_scope.

Module SDN.
Section X.
  Variable segs : list Segment.
  Variable A : atable.
  Variable nx0 : N.

  (* [comment removed for export] *)
  Fixpoint find_map (ms : list amap) (b : expr) : option amap :=
    match ms with
    | [] => None
    | m :: rest => if (negb (is_fog m) && expr_eqb (am_base m) b)%bool then Some m else find_map rest b
    end.

  Definition sd_tests (cs : acs) (b1 b2 : expr) (m1 m2 : amap) : list bool :=
    let k := kn cs in
    let n1 := am_len m1 in let n2 := am_len m2 in
    let '(sb1, sk1, sn1) := shadow_of A k b1 n1 in let '(sb2, sk2, sn2) := shadow_of A k b2 n2 in
    [ negb (expr_eqb b1 b2)
    ; Z.leb 3 (ealign k b1); Z.leb 3 (ealign k n1); Z.leb 3 (ealign k b2); Z.leb 3 (ealign k n2)
    ; flat_x k sb1 sk1 sn1; flat_x k sb2 sk2 sn2
    ; match xhi k b1, xhi k n1, xhi k b2, xhi k n2 with
      | Some h1, Some l1, Some h2, Some l2 =>
          (* [comment removed for export] *)
          (if Z.leb (h1 + l1) (2 ^ 47) then true else match xhi k (eadd b1 n1) with Some e => Z.leb e (2 ^ 47) | None => false end)
          && (if Z.leb (h2 + l2) (2 ^ 47) then true else match xhi k (eadd b2 n2) with Some e => Z.leb e (2 ^ 47) | None => false end)
      | _, _, _, _ => false end ]%bool.

  (* [comment removed for export] *)
  Definition node_shdisjm (cs : acs) (b1 b2 : expr) : option acs :=
    match find_map (a_maps cs) b1, find_map (a_maps cs) b2 with
    | Some m1, Some m2 =>
        if forallb (fun b : bool => b) (sd_tests cs b1 b2 m1 m2) then
          let k := kn cs in
          let '(sb1, sk1, sn1) := shadow_of A k b1 (am_len m1) in let '(sb2, sk2, sn2) := shadow_of A k b2 (am_len m2) in
          Some (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2])
        else None
    | _, _ => None
    end.

  Fixpoint first_false (i : nat) (l : list bool) : nat :=
    match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.
  (* [comment removed for export] *)
  Definition diag_shdisjm (cs : acs) (b1 b2 : expr) : nat :=
    match find_map (a_maps cs) b1, find_map (a_maps cs) b2 with
    | Some m1, Some m2 => first_false 1 (sd_tests cs b1 b2 m1 m2)
    | _, _ => 100%nat
    end.

  Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
    match id, args with
    | 120%nat, [b1; b2] => node_shdisjm cs b1 b2
    | _, _ => None
    end.
End X.
End SDN.

Section Sound.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : N.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis RES_len : res_len_ok SEGS A.
Hypothesis SHADOW_ok : shadow_ok A.

Lemma find_map_spec : forall ms b m, SDN.find_map ms b = Some m -> In m ms /\ is_fog m = false /\ am_base m = b.
Proof.
  intros ms b m. induction ms as [|h t IH]; cbn [SDN.find_map]; intros H; [discriminate|].
  destruct (negb (is_fog h) && expr_eqb (am_base h) b)%bool eqn:Hc.
  - injection H as <-. apply andb_prop in Hc as [Hf Hb]. apply Bool.negb_true_iff in Hf. apply expr_eqb_eq in Hb.
    split; [left; reflexivity | split; [exact Hf | exact Hb]].
  - destruct (IH H) as (Hin & Hf & Hb). split; [right; exact Hin | split; assumption].
Qed.

Lemma node_shdisjm_sound : forall b1 b2,
  node1_stmt SEGS A nx0 LIMIT SINV argH FS0 always (fun cs => SDN.node_shdisjm A cs b1 b2).
Proof.
  intros b1 b2 cs cs' E R FULL model T HC _ Hn Hk.
  unfold SDN.node_shdisjm in Hn.
  destruct (SDN.find_map (a_maps cs) b1) as [m1|] eqn:F1; [|discriminate].
  destruct (SDN.find_map (a_maps cs) b2) as [m2|] eqn:F2; [|discriminate].
  destruct (find_map_spec _ _ _ F1) as (In1 & Nf1 & B1e). destruct (find_map_spec _ _ _ F2) as (In2 & Nf2 & B2e).
  unfold SDN.sd_tests in Hn.
  destruct (shadow_of A (kn cs) b1 (am_len m1)) as [[sb1 sk1] sn1] eqn:H1.
  destruct (shadow_of A (kn cs) b2 (am_len m2)) as [[sb2 sk2] sn2] eqn:H2.
  match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end. injection Hn as <-.
  cbn [forallb] in Hc.
  apply andb_prop in Hc as [Hne Hc]. apply andb_prop in Hc as [Lb1 Hc]. apply andb_prop in Hc as [Ln1 Hc].
  apply andb_prop in Hc as [Lb2 Hc]. apply andb_prop in Hc as [Ln2 Hc]. apply andb_prop in Hc as [Fs1 Hc].
  apply andb_prop in Hc as [Fs2 Hc]. apply andb_prop in Hc as [Hhi _].
  apply Bool.negb_true_iff in Hne.
  apply Z.leb_le in Lb1. apply Z.leb_le in Ln1. apply Z.leb_le in Lb2. apply Z.leb_le in Ln2.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  assert (Hmm : m1 <> m2).
  { intros ->. rewrite B2e in B1e. subst b1. rewrite expr_eqb_refl in Hne. discriminate. }
  pose proof (maps_match_disjoint SEGS A RES_len E (a_maps cs) _ m1 m2 (co_maps _ _ _ _ _ _ _ _ _ _ _ HC) (co_seps _ _ _ _ _ _ _ _ _ _ _ HC) In1 In2 Nf1 Nf2 Hmm) as DISJ.
  unfold iv_disjoint, amap_den in DISJ. cbn [fst snd] in DISJ. rewrite B1e, B2e in DISJ.
  destruct (xhi (kn cs) b1) as [h1|] eqn:Xh1; [|discriminate]. destruct (xhi (kn cs) (am_len m1)) as [l1|] eqn:Xl1; [|discriminate].
  destruct (xhi (kn cs) b2) as [h2|] eqn:Xh2; [|discriminate]. destruct (xhi (kn cs) (am_len m2)) as [l2|] eqn:Xl2; [|discriminate].
  clear Hhi.   (* [comment removed for export] *)
  pose proof (xhi_sound SEGS E _ (kn cs) b1 h1 HK Xh1) as XB1. pose proof (xhi_sound SEGS E _ (kn cs) (am_len m1) l1 HK Xl1) as XL1.
  pose proof (xhi_sound SEGS E _ (kn cs) b2 h2 HK Xh2) as XB2. pose proof (xhi_sound SEGS E _ (kn cs) (am_len m2) l2 HK Xl2) as XL2.
  destruct (shadow_of_val SEGS A SHADOW_ok E _ (kn cs) b1 (am_len m1) sb1 sk1 sn1 HK H1 Fs1) as [V1 L1].
  destruct (shadow_of_val SEGS A SHADOW_ok E _ (kn cs) b2 (am_len m2) sb2 sk2 sn2 HK H2 Fs2) as [V2 L2].
  pose proof SHADOW_ok as SO; unfold shadow_ok in SO.
  assert (HKD : kentry_ok SEGS E (Mr A argH E cs model FULL) (KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2)).
  { cbn [kentry_ok]. rewrite V1, V2, L1, L2.
    destruct (ealign_sound SEGS E _ (kn cs) b1 HK) as [_ D1]. destruct (ealign_sound SEGS E _ (kn cs) (am_len m1) HK) as [_ D2].
    destruct (ealign_sound SEGS E _ (kn cs) b2 HK) as [_ D3]. destruct (ealign_sound SEGS E _ (kn cs) (am_len m2) HK) as [_ D4].
    assert (P8 : forall e, 3 <= ealign (kn cs) e -> (2 ^ ealign (kn cs) e | bv_unsigned (edenot E e)) -> (8 | bv_unsigned (edenot E e))).
    { intros e He Hd. eapply Z.divide_trans; [|exact Hd]. change 8 with (2 ^ 3). apply pow2_divide_le. lia. }
    pose proof (P8 _ Lb1 D1) as [q1 Q1]. pose proof (P8 _ Ln1 D2) as [q2 Q2]. pose proof (P8 _ Lb2 D3) as [q3 Q3]. pose proof (P8 _ Ln2 D4) as [q4 Q4].
    pose proof (u64_range (edenot E b1)) as Rb1. pose proof (u64_range (edenot E b2)) as Rb2.
    pose proof (u64_range (edenot E (am_len m1))) as Rn1. pose proof (u64_range (edenot E (am_len m2))) as Rn2.
    generalize dependent DISJ. rewrite Q1, Q2, Q3, Q4. rewrite Q1 in Rb1, XB1. rewrite Q2 in Rn1, XL1. rewrite Q3 in Rb2, XB2. rewrite Q4 in Rn2, XL2.
    rewrite !Z.div_mul by lia. intros DISJ.
    rewrite (Z.mod_small (q1 + shadow_off A)) by lia. rewrite (Z.mod_small (q3 + shadow_off A)) by lia.
    clear - DISJ Rb1 Rb2 Rn1 Rn2 SO. lia. }
  assert (HC' : cs_ok SEGS A LIMIT SINV argH FS0 E (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2]) R FULL model).
  { unfold add_kn. apply cs_ok_set_kn; [exact HC|]. constructor; [exact HKD | exact HK]. }
  assert (Hpc' : pc (add_kn cs [KDisj (SA sb1 sk1) sn1 (SA sb2 sk2) sn2]) = pc cs) by reflexivity.
  rewrite <- Hpc'. apply (Hk E R FULL model); [split; apply env_agree_refl | exact HC' | reflexivity].
Qed.

Theorem sd_xn_sound : ext_stmt SEGS A nx0 LIMIT (SDN.xn A) SINV argH FS0.
Proof.
  intros id args. destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate H|].
  do 119 (destruct id as [|id]; [intros cs cs' E R FULL model T _ _ H; discriminate H|]).
  destruct id as [|id]; [|intros cs cs' E R FULL model T _ _ H; discriminate H].
  destruct args as [|b1 [|b2 [|? ?]]]; try (intros cs cs' E R FULL model T _ _ H; discriminate H).
  exact (node_shdisjm_sound b1 b2).
Qed.
End Sound.
