(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import
  PropExec CatExec CatSim SeqExec StoreOk ShapeAlg SpinAlg AgentLib AsanAcct AsanAcctShape.
From OSSVerify.Proofs.zstd.simple_decompress.lib.AS Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound AsanPlanSoundSums AsanNodesMmLib.
(* [comment removed for export] *)
Unset Lia Cache.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.
Import ListNotations.
Import AX2. Import AX2S. Import AP. Import APS.
Open Scope Z_scope.

Section NodesWJoin.
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.

  (* [comment removed for export] *)
  Definition node_wjoin (cs : acs) (b : expr) (n : Z) : option acs :=
    let '(bb, bo) := split_lit b in
    let k := kn cs in
    if (fresh_ok nx0 cs && expr_vars_lt (nxt cs) bb && Z.leb 1 n && Z.leb n 8
        && kn_readable SEGS k k bb bo (Z.to_nat n))%bool
    then Some (set_kn (bump cs 1) (KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout k bb bo (ELit n)))
    else None.

  (* [comment removed for export] *)
  Definition node_bandhi (cs : acs) (v : nat) : option acs :=
    let k := kn cs in
    let b := escale 4096 (EVar v) in
    match find_disj k b (ELit MID_LO) with
    | Some (c1, o1, n1, c2, o2, ELit L) =>
        match xlo k n1, xlo k (EVar v), xhi k (EVar v) with
        | Some nlo, Some lov, Some hiv =>
            if (expr_eqb c1 b && Z.eqb o1 0 && expr_eqb c2 (ELit MID_LO) && Z.eqb o2 0
                && Z.ltb 0 L && Z.ltb L two64 && Z.leb 1 nlo && Z.leb 0 lov && Z.leb hiv (2 ^ 52 - 1)
                && Z.ltb MID_LO (4096 * lov + nlo))%bool
            then Some (add_kn cs [KRange (EVar v) ((MID_LO + L + 4095) / 4096) hiv])
            else None
        | _, _, _ => None
        end
    | _ => None
    end.

  (* [comment removed for export] *)
  Definition node_vis (cs : acs) (b n : expr) : option acs := vis_add A LIMIT cs b n (kimg_clip A (kn cs)).

  (* [comment removed for export] *)
  Definition node_brkvar (cs : acs) : option acs :=
    let k := kn cs in let b := a_brk cs in
    match xlo k b, xhi k b with
    | Some lo, Some hi =>
        if (fresh_ok nx0 cs && page_aligned k b && Z.leb 0 lo && Z.ltb hi two64)%bool then
          let v := nxt cs in let nb := escale 4096 (EVar v) in
          let ss := a_ss cs in
          Some (ACS (mk_ss (s_pc ss) (s_regs ss) (KRange (EVar v) ((lo + 4095) / 4096) (hi / 4096) :: KRange (esub nb b) 0 0 :: s_know ss) (S v))
                    (a_maps cs) (a_totsz cs) (a_ylo cs) (a_eager cs) (a_vis cs) (a_ghost cs) (a_abytes cs) nb (a_fd cs) (a_tidset cs))
        else None
    | _, _ => None
    end.

  (* [comment removed for export] *)
  Definition XNS (id : nat) (args : list expr) (cs : acs) : option acs :=
    match id, args with
    | 1%nat, [b; ELit n] => node_wjoin cs b n
    | 2%nat, [EVar v] => node_bandhi cs v
    | 3%nat, [b; n] => node_vis cs b n
    | 4%nat, [] => node_brkvar cs
    | _, _ => None
    end.

  Lemma wjoin_sound : forall E cs R FULL model b n cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_wjoin cs b n = Some cs' ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E')
               /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model b n cs' HC H. unfold node_wjoin in H.
    destruct (split_lit b) as [bb bo]. cbv zeta in H.
    destruct (fresh_ok nx0 cs && expr_vars_lt (nxt cs) bb && Z.leb 1 n && Z.leb n 8
              && kn_readable SEGS (kn cs) (kn cs) bb bo (Z.to_nat n))%bool eqn:Hg; [|discriminate].
    injection H as <-.
    apply andb_prop in Hg as [Hg Hrd]. apply andb_prop in Hg as [Hg Hn8]. apply andb_prop in Hg as [Hg Hn1].
    apply andb_prop in Hg as [Hf Hvb].
    apply Z.leb_le in Hn1. apply Z.leb_le in Hn8.
    destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (M := Mr A argH E cs model FULL).
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. fold M in HK.
    destruct (kn_readable_sound SEGS E M (kn cs) M (kn cs) bb bo (Z.to_nat n) HK HK ltac:(lia) ltac:(lia) Hrd)
      as [Hflat [bs [Hbs Hlen]]].
    set (V := Z_to_bv 64 (bytes_le_to_Z bs)).
    set (E' := upd E (nxt cs) V).
    assert (Hag : env_agree (nxt cs) E E') by (unfold E'; apply upd_agree).
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC) as HC2.
    change (set_kn (bump cs 1) (KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout (kn cs) bb bo (ELit n)))
      with (set_kn (bump cs 1) (KWord (SA bb bo) (Z.to_nat n) (EVar (nxt cs)) :: kn_cutout (kn cs) bb bo (ELit n))).
    apply cs_ok_set_kn.
    - destruct HC2; constructor; cbn [bump with_ss a_ss mk_ss s_regs s_log s_know kn a_maps a_totsz a_ylo a_eager a_vis a_abytes a_brk a_fd a_tidset];
        try assumption; reflexivity.
    - pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC2) as HK2.
      assert (EM : Mr A argH E' (bump cs 1) model FULL = M).
      { unfold M, Mr. change (hid A argH E' (bump cs 1) model) with (hid A argH E' cs model).
        rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow). reflexivity. }
      assert (EM2 : Mr A argH E' cs model FULL = M).
      { unfold M, Mr. rewrite (hid_agree A nx0 argH argH_agree (nxt cs) E E' cs model Hag Fle Fallow). reflexivity. }
      rewrite EM. rewrite EM2 in HK2.
      constructor.
      + (* [comment removed for export] *)
        cbn [kentry_ok]. split; [lia|].
        assert (Ea : adenot E' (SA bb bo) = adenot E (SA bb bo)).
        { symmetry. apply (adenot_agree (nxt cs)); [exact Hag | exact Hvb]. }
        split; [apply (flat_agree (nxt cs) E E' (SA bb bo) _ Hag Hvb); exact Hflat|].
        rewrite Ea, Hbs. cbn [edenot]. unfold E'. rewrite upd_at. unfold V.
        rewrite (APSX.word_to_le_bytes_of_bytes_n (Z.to_nat n) bs Hlen ltac:(lia)). reflexivity.
      + (* [comment removed for export] *)
        eapply know_ok_cutout; [exact HK2 | intros; reflexivity].
  Qed.

  Lemma bandhi_sound : forall E cs R FULL model v cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_bandhi cs v = Some cs' ->
    cs_ok SEGS A LIMIT SINV argH FS0 E cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model v cs' HC H. unfold node_bandhi in H.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    destruct (find_disj (kn cs) (escale 4096 (EVar v)) (ELit MID_LO)) as [[[[[[c1 o1] n1] c2] o2] n2]|] eqn:Hf; [|discriminate].
    destruct n2 as [L| | | | | | |]; try discriminate.
    destruct (xlo (kn cs) n1) as [nlo|] eqn:Hn; [|discriminate].
    destruct (xlo (kn cs) (EVar v)) as [lov|] eqn:Hlv; [|discriminate].
    destruct (xhi (kn cs) (EVar v)) as [hiv|] eqn:Hhv; [|discriminate].
    destruct (expr_eqb c1 (escale 4096 (EVar v)) && Z.eqb o1 0 && expr_eqb c2 (ELit MID_LO) && Z.eqb o2 0
              && Z.ltb 0 L && Z.ltb L two64 && Z.leb 1 nlo && Z.leb 0 lov && Z.leb hiv (2 ^ 52 - 1)
              && Z.ltb MID_LO (4096 * lov + nlo))%bool eqn:Hg; [|discriminate].
    injection H as <-.
    repeat match type of Hg with (_ && _)%bool = true => apply andb_prop in Hg as [Hg ?X] end.
    apply expr_eqb_eq in Hg. apply Z.eqb_eq in X7. apply expr_eqb_eq in X6. apply Z.eqb_eq in X5.
    apply Z.ltb_lt in X4. apply Z.ltb_lt in X3. apply Z.leb_le in X2. apply Z.leb_le in X1. apply Z.leb_le in X0. apply Z.ltb_lt in X.
    subst c1 o1 c2 o2.
    pose proof (find_disj_sound SEGS E _ (kn cs) _ _ _ _ _ _ _ _ HK Hf) as Hd.
    pose proof (xlo_sound SEGS E _ (kn cs) n1 nlo HK Hn) as Ln.
    pose proof (xlo_sound SEGS E _ (kn cs) (EVar v) lov HK Hlv) as Lv.
    pose proof (xhi_sound SEGS E _ (kn cs) (EVar v) hiv HK Hhv) as Hv.
    cbn [edenot] in Lv, Hv.
    assert (Ub : bv_unsigned (edenot E (escale 4096 (EVar v))) = 4096 * bv_unsigned (ev E v)).
    { unfold escale. rewrite mkMd_denot, u_mul64. cbn [edenot]. rewrite u_lit64 by lia.
      apply Z.mod_small. pose proof (u64_range (ev E v)). lia. }
    unfold estart, elenZ in Hd. cbn [a_base a_off] in Hd. rewrite Ub in Hd. cbn [edenot] in Hd. rewrite !u_lit64 in Hd by (unfold MID_LO, two64 in *; lia).
    split; [|reflexivity].
    unfold add_kn. apply cs_ok_set_kn; [exact HC|]. cbn [app]. constructor; [|exact HK].
    cbn [kentry_ok edenot]. unfold two64 in *.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
    change (MID_LO mod 2 ^ 64) with MID_LO in Hd. unfold MID_LO in *.
    split; [|exact Hv]. destruct Hd as [Hd|Hd]; [exfalso; lia|].
    rewrite (Z.mod_small L) in Hd by lia.
    lia.
    Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Qed.

  Lemma brkvar_sound : forall E cs R FULL model cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_brkvar cs = Some cs' ->
    exists E', (env_agree nx0 E E' /\ env_agree (nxt cs) E E')
               /\ cs_ok SEGS A LIMIT SINV argH FS0 E' cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model cs' HC H. unfold node_brkvar in H.
    destruct (xlo (kn cs) (a_brk cs)) as [l|] eqn:Hl; [|discriminate].
    destruct (xhi (kn cs) (a_brk cs)) as [h|] eqn:Hh; [|discriminate].
    match type of H with (if ?c then _ else _) = _ => destruct c eqn:Hc; [|discriminate] end.
    injection H as <-.
    apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [Hc H2]. apply andb_prop in Hc as [Hf Hpa].
    apply Z.leb_le in H2. apply Z.ltb_lt in H3. unfold two64 in H3.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK.
    pose proof (xlo_sound SEGS E _ (kn cs) (a_brk cs) l HK Hl) as L1.
    pose proof (xhi_sound SEGS E _ (kn cs) (a_brk cs) h HK Hh) as L2.
    assert (AL : bv_unsigned (edenot E (a_brk cs)) mod 4096 = 0).
    { assert (GEN : 12 <= ealign (kn cs) (a_brk cs) -> bv_unsigned (edenot E (a_brk cs)) mod 4096 = 0).
      { intros Hle. destruct (ealign_sound SEGS E _ (kn cs) (a_brk cs) HK) as [Hr [q Hq]]. rewrite Hq.
        replace (2 ^ ealign (kn cs) (a_brk cs)) with (2 ^ (ealign (kn cs) (a_brk cs) - 12) * 4096) by (rewrite <- (Z.pow_add_r 2 _ 12) by lia; f_equal; lia).
        rewrite Z.mul_assoc. apply Z.mod_mul. lia. }
      unfold page_aligned in Hpa. destruct (a_brk cs) as [z| | | | | | |]; try (apply GEN; apply Z.leb_le; exact Hpa).
      apply Z.eqb_eq in Hpa. cbn [edenot]. rewrite Z_to_bv_unsigned, bv_wrap64_mod.
      rewrite Z.mod_mod_divide; [exact Hpa | exists (2 ^ 52); reflexivity]. }
    destruct (fresh_ok_parts nx0 cs Hf) as (Fsr & Fkn & Fmaps & Fallow & Fbrk & Ffd & Fle).
    set (bz := bv_unsigned (edenot E (a_brk cs))) in *.
    set (v := nxt cs). set (E' := ext1 E v (Z_to_bv 64 (bz / 4096))).
    assert (Hag : env_agree v E E') by apply ext1_agree.
    pose proof (cs_ok_agree SEGS A nx0 LIMIT SINV argH argH_agree SINV_agree FS0 E E' cs R FULL model Hag Hf HC) as HC'.
    exists E'. split; [split; [eapply env_agree_le; [exact Hag | exact Fle] | exact Hag]|]. split; [|reflexivity].
    pose proof (u64_range (edenot E (a_brk cs))) as Rb. fold bz in Rb.
    assert (Hv : bv_unsigned (edenot E' (EVar v)) = bz / 4096).
    { cbn [edenot]. unfold E'. rewrite ext1_at. apply u_small.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    assert (Hold : edenot E' (a_brk cs) = edenot E (a_brk cs)).
    { symmetry. apply (edenot_agree' (nxt cs)); [exact Hag | exact Fbrk]. }
    assert (Hnb : edenot E' (escale 4096 (EVar v)) = edenot E (a_brk cs)).
    { unfold escale. rewrite mkMd_denot. cbn [edenot]. cbn [edenot] in Hv. apply bv_eq. rewrite u_mul64, Hv, u_lit64.
      change (4096 mod two64) with 4096. fold bz.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
      rewrite Z.mod_small; lia.
      Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false). }
    pose proof (co_brk _ _ _ _ _ _ _ _ _ _ _ HC) as HB0.
    set (cs' := ACS _ _ _ _ _ _ _ _ _ _ _).
    assert (HMr : Mr A argH E' cs' model FULL = Mr A argH E' cs model FULL) by reflexivity.
    assert (HA : allowA A E' cs' = allowA A E' cs) by reflexivity.
    destruct HC'; constructor; unfold cs'; rewrite ?HMr, ?HA;
      cbn [a_ss a_maps a_totsz a_ylo a_eager a_vis a_ghost a_abytes a_brk a_fd a_tidset kn mk_ss s_regs s_log s_know s_pc s_next] in *;
      try assumption; try reflexivity.
    - (* [comment removed for export] *) constructor; [|constructor; [|exact co_know0]].
      + cbn [kentry_ok]. rewrite Hv.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true). lia.
        Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
      + cbn [kentry_ok]. unfold esub. rewrite mkAlu_denot, u_sub64, Hnb, Hold. rewrite Z.sub_diag. rewrite Z.mod_0_l by lia. lia.
    - (* [comment removed for export] *) rewrite Hnb. exact HB0.
  Qed.

  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis SHADOW_ok : shadow_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_high2 : forall E M (a : word), SINV E M -> argH E a = true -> uE E e_sp0 <= bv_unsigned a.

  Lemma vis_sound : forall E cs R FULL model b n cs',
    cs_ok SEGS A LIMIT SINV argH FS0 E cs R FULL model -> node_vis cs b n = Some cs' ->
    cs_ok SEGS A LIMIT SINV argH FS0 E cs' R FULL model /\ pc cs' = pc cs.
  Proof.
    intros E cs R FULL model b n cs' HC H. unfold node_vis in H.
    destruct (AsanNodesMmLib.vis_add_inv A LIMIT cs b n _ cs' H) as (nhi & Hnhi & Ecs2).
    split; [| rewrite Ecs2; reflexivity].
    eapply (vis_add_sound SEGS A LIMIT (fun _ => None) (fun _ _ _ => None) (fun _ _ _ => None) (fun _ _ _ => None) SHADOW_ok SINV argH argH_high2 FS0 0%nat);
      [exact H | exact HC |].
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. unfold Mr in HK |- *.
    eapply (know_ok_unhide SEGS A); [apply (H_off_segments_cs SEGS A SEGS_in_hull HULL_ok argH argH_high) | apply kimg_clip_in_hull | | | ].
    - intros y Hy. rewrite Ecs2 in Hy. eapply hid_cons_sub. exact Hy.
    - intros y Hy. apply (hid_hull A HULL_ok argH argH_high). exact Hy.
    - unfold know_ok in *. apply Forall_forall. intros K HKin. apply kimg_clip_incl in HKin. exact (proj1 (Forall_forall _ _) HK K HKin).
  Qed.

  Theorem XNS_sound : ext_stmt SEGS A nx0 LIMIT XNS SINV argH FS0.
  Proof.
    intros id args cs cs' E R FULL model T HC _ Hn Hk.
    destruct id as [|[|[|[|[|id]]]]]; [discriminate| | | | |discriminate]; cbn [XNS] in Hn.
    - destruct args as [|b [|[z| | | | | | |] [|]]]; try discriminate.
      destruct (wjoin_sound E cs R FULL model b z cs' HC Hn) as (E' & Hag & HC' & Hpc).
      rewrite <- Hpc. eapply Hk; [exact Hag | exact HC' | reflexivity].
    - destruct args as [|[|v| | | | | |] [|]]; try discriminate.
      destruct (bandhi_sound E cs R FULL model v cs' HC Hn) as [HC' Hpc].
      rewrite <- Hpc. eapply Hk; [split; apply env_agree_refl | exact HC' | reflexivity].
    - destruct args as [|b [|n [|]]]; try discriminate.
      destruct (vis_sound E cs R FULL model b n cs' HC Hn) as [HC' Hpc].
      rewrite <- Hpc. eapply Hk; [split; apply env_agree_refl | exact HC' | reflexivity].
    - destruct args as [|? ?]; try discriminate.
      destruct (brkvar_sound E cs R FULL model cs' HC Hn) as (E' & Hag & HC' & Hpc).
      rewrite <- Hpc. eapply Hk; [exact Hag | exact HC' | reflexivity].
  Qed.
End NodesWJoin.
