(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.Common Require Import PropExec ShapeAlg ShapeAlgCfg.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.yajl_ruby.json_fuzzer.lib.XQ Require Import StoreOk AgentLib AsanAcct AsanAcctShape AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition XE0 (id : nat) (args : list expr) (cs : acs) : option (Z * list spiece * acs) := None.
Definition XB0 (id : nat) (args : list expr) (cs : acs) : option (acs * acs) := None.

Section Defs.
Variable SEGS : list Segment.
Variable A : atable.
Variable nx0 : nat.

(* [comment removed for export] *)
Definition absword (cs : acs) (args : list expr) : option acs :=
  match args with
  | [b; ELit n] =>
      let '(bb, bo) := split_lit b in
      let k := kn cs in
      if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) bb && Z.leb 1 n && Z.leb n 8
          && kn_readable SEGS (facts_of k) k bb bo (Z.to_nat n))%bool
      then Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs)) (KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout k bb bo (ELit n)) (S (nxt cs)))
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition varlb (cs : acs) (args : list expr) : option acs :=
  match args with
  | [a; n; ELit lo'] =>
      let k := kn cs in
      let '(ab, ao) := split_lit a in
      match ab with
      | EMd M_MUL (ELit c) (EVar v) =>
          match xlo k ab, xlo k n, xhi k (EVar v) with
          | Some alo, Some nlo, Some vhi =>
              if (Z.ltb 0 c && Z.ltb c two64 && Z.leb 0 ao && Z.ltb (c * vhi + ao) two64 && Z.leb 0 (z_lo A) && Z.leb (z_lo A) (z_hi A) && Z.ltb (z_hi A) two64
                  && ranges_apart_x k ab ao n (ELit 0) (z_lo A) (ELit (z_hi A - z_lo A))
                  && Z.ltb (z_lo A) (alo + ao + nlo)
                  && Z.ltb (c * (lo' - 1) + ao) (z_hi A) && Z.leb lo' vhi)%bool
              then Some (add_kn cs [KRange (EVar v) lo' vhi])
              else Some cs    (* [comment removed for export] *)
          | _, _, _ => None
          end
      | _ => None
      end
  | _ => None
  end.


(* [comment removed for export] *)
Definition zroundup (x m : Z) : Z := - ((- x) / m) * m.
Definition regrange (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit r] =>
      if (Z.leb 1 r && Z.ltb r 32)%bool then
        let k := kn cs in let e := reg cs (Z.to_nat r) in
        match xb2 k e with
        | Some (lo, hi) =>
            let j := Z.min (ealign k e) 40 in let m := 2 ^ j in
            let lo' := zroundup lo m in let hi' := (hi / m) * m in
            if (Z.leb 0 j && Z.leb 0 lo && Z.leb lo' hi')%bool then Some (add_kn cs [KRange e lo' hi']) else None
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Definition intropage (cs : acs) (args : list expr) : option acs :=
  match args with
  | [ELit lo; ELit hi; ELit len] =>
      if (fresh_ok nx0 cs && Z.leb 1 lo && Z.leb lo hi && Z.ltb 0 len && Z.leb (4096 * lo + len) (z_lo A)
          && Z.leb (z_lo A) (z_hi A) && Z.ltb (z_hi A) two64 && Z.ltb (4096 * hi) two64 && Z.ltb len two64)%bool
      then let v := nxt cs in
           Some (ACS (mk_ss (pc cs) (s_regs (a_ss cs))
                        (KRange (EVar v) lo hi
                         :: KDisj (SA (escale 4096 (EVar v)) 0) (ELit len) (SA (ELit 0) (z_lo A)) (ELit (z_hi A - z_lo A))
                         :: kn cs) (S v))
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) (a_brk cs) (a_fd cs) (a_tidset cs))
      else None
  | _ => None
  end.

Definition XN5 (id : nat) (args : list expr) (cs : acs) : option acs :=
  match id with
  | 1%nat => absword cs args
  | 3%nat => varlb cs args
  | 4%nat => regrange cs args
  | 5%nat => intropage cs args
  | _ => None
  end.
End Defs.

Section Sound.
Variable SEGS : list Segment.
Variable SC : SpuriousCfg.
Variable A : atable.
Variable nx0 : nat.
Variable LIMIT : Z.
Variable SINV : env -> (word -> option byte) -> Prop.
Variable argH : env -> word -> bool.
Variable FS0 : Fs.Fs.
Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
Hypothesis NX0_S : nx0_sp_ok nx0.

Let cs_ok_agree' := APS.cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree NX0_S FS0.
Let hid_agree' := APS.hid_agree A nx0 argH argH_agree.

Lemma absword_sound : forall args cs cs' E R FULL model,
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> absword SEGS nx0 cs args = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros args cs cs' E R FULL model HC H. unfold absword in H.
  destruct args as [|b [|[n| | | | | | |] [|? ?]]]; try discriminate H.
  destruct (split_lit b) as [bb bo] eqn:Hsp.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate H] end.
  injection H as <-.
  apply andb_prop in Hcond as [Hcond Hrd]. apply andb_prop in Hcond as [Hcond Hn8]. apply andb_prop in Hcond as [Hcond Hn1].
  apply andb_prop in Hcond as [Hf Hbb]. apply Z.leb_le in Hn1. apply Z.leb_le in Hn8.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  destruct (kn_readable_sound SEGS E _ (facts_of (kn cs)) _ (kn cs) bb bo (Z.to_nat n) (facts_of_ok SEGS E _ _ HK) HK ltac:(lia) ltac:(lia) Hrd)
    as (Hfl & bs & Hbs & Hlen).
  set (w := Z_to_bv 64 (bytes_le_to_Z bs)).
  set (E' := ext1 E (nxt cs) w).
  assert (Hag : env_agree (nxt cs) E E') by apply ext1_agree.
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree' E E' cs R FULL model Hag Hf HC) as HC2.
  match goal with |- cs_ok _ _ _ _ _ _ _ ?X _ _ _ =>
    replace X with (set_kn (bump cs 1) (KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout (kn cs) bb bo (ELit n)))
      by (unfold set_kn, bump; cbn; rewrite Nat.add_1_r; reflexivity) end.
  apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0).
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid A argH E' (bump cs 1) model) with (hid A argH E' cs model).
    rewrite (hid_agree' (nxt cs) E E' cs model Hag Fle Fallow).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC2) as HK2. unfold Mr in HK2.
    rewrite (hid_agree' (nxt cs) E E' cs model Hag Fle Fallow) in HK2.
    assert (Ebb : edenot E' bb = edenot E bb) by (symmetry; apply (edenot_agree' (nxt cs)); [exact Hag | exact Hbb]).
    constructor.
    + cbn [kentry_ok]. split; [lia|]. split.
      * unfold flat, estart in *. cbn [a_base a_off] in *. rewrite Ebb. exact Hfl.
      * unfold adenot, estart in *. cbn [a_base a_off] in *. rewrite Ebb.
        unfold adenot, estart, Mr in Hbs. cbn [a_base a_off] in Hbs. rewrite Hbs.
        cbn [edenot]. unfold E'. rewrite ext1_at. unfold w.
        rewrite (APSX.word_to_le_bytes_of_bytes_n (Z.to_nat n) bs Hlen ltac:(lia)). reflexivity.
    + eapply (know_ok_cutout SEGS); [exact HK2 | intros; reflexivity].
Qed.

Lemma varlb_sound : forall args cs cs' E R FULL model,
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> varlb A cs args = Some cs' ->
  cs_ok SEGS A LIMIT SINV argH FS0 E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros args cs cs' E R FULL model HC H. unfold varlb in H.
  destruct args as [|a [|n [|[lo'| | | | | | |] [|? ?]]]]; try discriminate H.
  destruct (split_lit a) as [ab ao] eqn:Hsp.
  destruct ab as [?|?|? ? ?|? ? ?|op ca cb|? ? ?|? ? ? ?|? ? ? ?]; try discriminate H.
  destruct op; try discriminate H. destruct ca as [c|?|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate H.
  destruct cb as [?|v|? ? ?|? ? ?|? ? ?|? ? ?|? ? ? ?|? ? ? ?]; try discriminate H.
  destruct (xlo (kn cs) (EMd M_MUL (ELit c) (EVar v))) as [alo|] eqn:Halo; [|discriminate H].
  destruct (xlo (kn cs) n) as [nlo|] eqn:Hnlo; [|discriminate H].
  destruct (xhi (kn cs) (EVar v)) as [vhi|] eqn:Hvhi; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|injection H as <-; split; [exact HC | reflexivity]] end.
  injection H as <-.
  apply andb_prop in Hcond as [Hcond Hlv]. apply andb_prop in Hcond as [Hcond Hlo']. apply andb_prop in Hcond as [Hcond Hside].
  apply andb_prop in Hcond as [Hcond Hapz]. apply andb_prop in Hcond as [Hcond Zh64]. apply andb_prop in Hcond as [Hcond Zlh].
  apply andb_prop in Hcond as [Hcond Zl0]. apply andb_prop in Hcond as [Hcond Hnw]. apply andb_prop in Hcond as [Hcond Hao]. apply andb_prop in Hcond as [Hc Hc64].
  apply Z.ltb_lt in Hc. apply Z.ltb_lt in Hc64. apply Z.leb_le in Hao. apply Z.ltb_lt in Hnw. apply Z.leb_le in Zl0. apply Z.leb_le in Zlh. apply Z.ltb_lt in Zh64.
  apply Z.ltb_lt in Hside. apply Z.ltb_lt in Hlo'. apply Z.leb_le in Hlv.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xlo_sound SEGS E _ (kn cs) _ alo HK Halo) as Ualo.
  pose proof (xlo_sound SEGS E _ (kn cs) _ nlo HK Hnlo) as Unlo.
  pose proof (xhi_sound SEGS E _ (kn cs) _ vhi HK Hvhi) as Uvhi. cbn [edenot] in Uvhi.
  pose proof (u64_range (ev E v)) as Rv.
  assert (Uab : bv_unsigned (edenot E (EMd M_MUL (ELit c) (EVar v))) = c * bv_unsigned (ev E v)).
  { cbn [edenot]. rewrite u_mul64, (u64_lit c) by (clear - Hc Hc64; unfold two64 in *; lia). unfold two64 in *. apply Z.mod_small. clear - Hc Hao Hnw Uvhi Rv. nia. }
  pose proof (ranges_apart_x_sound SEGS E _ (kn cs) _ ao n (ELit 0) (z_lo A) (ELit (z_hi A - z_lo A)) HK Hapz) as AZ.
  unfold estart, elenZ in AZ. cbn [a_base a_off] in AZ. rewrite !edenot_lit in AZ.
  rewrite (u64_lit 0) in AZ by (unfold two64; lia). rewrite (u64_lit (z_hi A - z_lo A)) in AZ by (unfold two64 in *; lia).
  rewrite Uab in AZ, Ualo. unfold elenZ in Unlo |- *.
  split; [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok edenot]. split; [|exact Uvhi].
  destruct AZ as [AZ|AZ]; [exfalso; clear - AZ Ualo Unlo Hside; lia|].
  clear - AZ Hc Hlo' Rv. nia.
Qed.

Lemma zroundup_ge : forall x m, 0 < m -> x <= zroundup x m /\ (m | zroundup x m).
Proof.
  intros x m Hm. unfold zroundup. split.
  - pose proof (Z.mul_div_le (- x) m Hm). pose proof (Z_div_mod_eq_full (- x) m). pose proof (Z.mod_pos_bound (- x) m Hm). nia.
  - exists (- (- x / m)). lia.
Qed.

Lemma zroundup_min : forall x m k, 0 < m -> x <= k * m -> zroundup x m <= k * m.
Proof.
  intros x m k Hm Hx. unfold zroundup.
  assert (D : - (k * m) / m <= - x / m) by (apply Z.div_le_mono; lia).
  replace (- (k * m)) with ((- k) * m) in D by lia. rewrite Z.div_mul in D by lia. nia.
Qed.

Lemma regrange_sound : forall args cs cs' E R FULL model,
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> regrange cs args = Some cs' ->
  cs_ok SEGS A LIMIT SINV argH FS0 E cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros args cs cs' E R FULL model HC H. unfold regrange in H.
  destruct args as [|[r| | | | | | |] [|? ?]]; try discriminate H.
  destruct (Z.leb 1 r && Z.ltb r 32)%bool; [|discriminate H].
  destruct (xb2 (kn cs) (reg cs (Z.to_nat r))) as [[lo hi]|] eqn:Hb; [|discriminate H].
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate H] end.
  injection H as <-.
  apply andb_prop in Hcond as [Hcond Hle]. apply andb_prop in Hcond as [Hj Hlo0].
  apply Z.leb_le in Hj. apply Z.leb_le in Hlo0. apply Z.leb_le in Hle.
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  pose proof (xb2_sound SEGS E _ (kn cs) _ lo hi HK Hb) as [Ulo Uhi].
  pose proof (ealign_sound SEGS E _ (kn cs) (reg cs (Z.to_nat r)) HK) as [Ral Dal].
  set (j := Z.min (ealign (kn cs) (reg cs (Z.to_nat r))) 40) in *.
  set (u := bv_unsigned (edenot E (reg cs (Z.to_nat r)))) in *.
  assert (Hm : 0 < 2 ^ j) by (apply Z.pow_pos_nonneg; lia).
  assert (Dj : (2 ^ j | u)).
  { destruct Dal as [q Hq]. exists (q * 2 ^ (ealign (kn cs) (reg cs (Z.to_nat r)) - j)).
    rewrite <- Z.mul_assoc, <- Z.pow_add_r by lia. replace (ealign (kn cs) (reg cs (Z.to_nat r)) - j + j) with (ealign (kn cs) (reg cs (Z.to_nat r))) by lia. exact Hq. }
  split; [|reflexivity].
  unfold add_kn. apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0); [exact HC|]. constructor; [|exact HK].
  cbn [kentry_ok]. fold u. destruct Dj as [q Hq]. split.
  - (* [comment removed for export] *)
    pose proof (zroundup_ge lo (2 ^ j) Hm) as [G1 [q' Hq']].
    pose proof (zroundup_min lo (2 ^ j) q Hm ltac:(lia)). lia.
  - pose proof (Z.mul_div_le hi (2 ^ j) Hm). pose proof (Z_div_mod_eq_full hi (2 ^ j)). pose proof (Z.mod_pos_bound hi (2 ^ j) Hm).
    destruct (Z_lt_le_dec (hi / 2 ^ j * 2 ^ j) u) as [LT|GE]; [|lia].
    exfalso. assert (hi / 2 ^ j < q)%Z by nia. nia.
Qed.

Lemma intropage_sound : forall args cs cs' E R FULL model,
  cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> intropage A nx0 cs args = Some cs' ->
  exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E') /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
Proof.
  intros args cs cs' E R FULL model HC H. unfold intropage in H.
  destruct args as [|[lo| | | | | | |] [|[hi| | | | | | |] [|[len| | | | | | |] [|? ?]]]]; try discriminate H.
  match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate H] end.
  injection H as <-.
  apply andb_prop in Hcond as [Hcond L64]. apply andb_prop in Hcond as [Hcond H64]. apply andb_prop in Hcond as [Hcond Z64].
  apply andb_prop in Hcond as [Hcond Zlh]. apply andb_prop in Hcond as [Hcond Hfit]. apply andb_prop in Hcond as [Hcond Hlen].
  apply andb_prop in Hcond as [Hcond Hlohi]. apply andb_prop in Hcond as [Hf Hlo1].
  apply Z.leb_le in Hlo1. apply Z.leb_le in Hlohi. apply Z.ltb_lt in Hlen. apply Z.leb_le in Hfit. apply Z.leb_le in Zlh.
  apply Z.ltb_lt in Z64. apply Z.ltb_lt in H64. apply Z.ltb_lt in L64.
  destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
  pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
  set (w := Z_to_bv 64 lo).
  set (E' := ext1 E (nxt cs) w).
  assert (Hag : env_agree (nxt cs) E E') by apply ext1_agree.
  assert (Uw : bv_unsigned w = lo) by (unfold w; apply u64_lit; unfold two64 in *; lia).
  exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
  pose proof (cs_ok_agree' E E' cs R FULL model Hag Hf HC) as HC2.
  match goal with |- cs_ok _ _ _ _ _ _ _ ?X _ _ _ =>
    replace X with (set_kn (bump cs 1) (KRange (EVar (nxt cs)) lo hi
                         :: KDisj (SA (escale 4096 (EVar (nxt cs))) 0) (ELit len) (SA (ELit 0) (z_lo A)) (ELit (z_hi A - z_lo A))
                         :: kn cs))
      by (unfold set_kn, bump; cbn; rewrite Nat.add_1_r; reflexivity) end.
  apply (cs_ok_set_kn SEGS A LIMIT SINV argH FS0).
  - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
      try assumption; reflexivity.
  - unfold Mr. change (hid A argH E' (bump cs 1) model) with (hid A argH E' cs model).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC2) as HK2. unfold Mr in HK2.
    assert (Ev : bv_unsigned (edenot E' (EVar (nxt cs))) = lo) by (cbn [edenot]; unfold E'; rewrite ext1_at; exact Uw).
    assert (Es : bv_unsigned (edenot E' (escale 4096 (EVar (nxt cs)))) = 4096 * lo).
    { unfold escale. rewrite mkMd_denot, u_mul64, edenot_lit. change (edenot E' (EVar (nxt cs))) with (ev E' (nxt cs)).
      unfold E'. rewrite ext1_at, Uw. rewrite (u64_lit 4096) by lia. unfold two64 in *. apply Z.mod_small. lia. }
    constructor; [|constructor; [|exact HK2]].
    + cbn [kentry_ok]. rewrite Ev. split; [lia|exact Hlohi].
    + cbn [kentry_ok]. unfold estart, elenZ. cbn [a_base a_off]. rewrite Es, !edenot_lit.
      rewrite (u64_lit 0), (u64_lit len), (u64_lit (z_hi A - z_lo A)) by (unfold two64 in *; lia). left. lia.
Qed.

Theorem XN5_ext_stmt : ext_stmt SEGS SC A nx0 LIMIT (XN5 SEGS A nx0) SINV argH FS0.
Proof.
  intros id args cs cs' E R FULL model T HC _ Hn HK.
  unfold XN5 in Hn. destruct id as [|[|[|[|[|[|]]]]]]; try discriminate Hn.
  - destruct (absword_sound args cs cs' E R FULL model HC Hn) as (E' & Hag & HC' & Hpc).
    specialize (HK E' R FULL model Hag HC' eq_refl). rewrite Hpc in HK.
    (* [comment removed for export] *)
    exact HK.
  - destruct (varlb_sound args cs cs' E R FULL model HC Hn) as [HC' Hpc].
    specialize (HK E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). rewrite Hpc in HK. exact HK.
  - destruct (regrange_sound args cs cs' E R FULL model HC Hn) as [HC' Hpc].
    specialize (HK E R FULL model (conj (env_agree_refl _ _) (env_agree_refl _ _)) HC' eq_refl). rewrite Hpc in HK. exact HK.
  - destruct (intropage_sound args cs cs' E R FULL model HC Hn) as (E' & Hag & HC' & Hpc).
    specialize (HK E' R FULL model Hag HC' eq_refl). rewrite Hpc in HK. exact HK.
Qed.
End Sound.
