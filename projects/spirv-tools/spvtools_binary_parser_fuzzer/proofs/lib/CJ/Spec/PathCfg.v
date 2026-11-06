(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State Specs Run.

From LinuxProcessSemantics.LinuxProcessSem.Checks.Sys Require Import Prelude.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Lib Require Import PropExec MState ITree Nodes Decode NodesMM NodesInv Gap.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.CJ.Spec Require Import Prelim Monad MSafe STree Malloc MallocCtrl Prog KInv KStep KLink
  MI_Kit MPos CtxMono LB_Logic LB_Kernel LB_Embed LB_Raw LB_Count Path.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import AllocCeil RunRandom.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Section AC_1. Context {ACEIL : AllocCeiling} {RRND : RunRandom}.

Lemma nstep_evs_nil' nd mo eff mo' evs : nstep_cfg nd mo eff mo' evs -> evs = [].
Proof. intros [[H _] _]. exact H. Qed.

Lemma mmap_refusal_iff len prot s mo kk eff mo1 z s1 :
  prot = PROT_NONE \/ prot = PROT_RW -> 0 < len < LEN_MAX ->
  ev_step (EMmap 0 len prot MAPF) s = Vis (NMmap 0 len prot MAPF) kk ->
  nstep (NMmap 0 len prot MAPF) mo eff mo1 [] -> kk eff = Ret (Ok (z, s1)) ->
  nrefusal (NMmap 0 len prot MAPF) mo eff = is_err z.
Proof.
  intros Hp Hlen Hvis Hst Hk.
  destruct (ev_step_mmap_shape len prot s Hp) as (kk' & Hvis' & Hkk). rewrite Hvis in Hvis'. injection Hvis' as <-.
  rewrite Hkk in Hk. destruct Hst as [_ Hst]. cbv zeta in Hst.
  pose proof alloc_ceiling_lt64 as HC.
  pose proof (mmap_len_facts len ltac:(lia)) as (M1 & M2 & M3 & M4).
  assert (NE : forall a : word, bv_unsigned a < 2 ^ 63 -> bv_eqb a (errno_ret ENOMEM) = false).
  { intros a Ha. apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). unfold two_pow_64, ENOMEM in E. lia. }
  destruct Hp as [-> | ->].
  - change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? PROT_RW_Z)) with false in Hst.
    change ((MAPF =? MAP_ANON_PRIV) && (PROT_NONE =? 0)) with true in Hst. cbv iota in Hst.
    change (PROT_NONE =? 0) with true in Hk. cbv iota in Hk.
    destruct Hst as [(e & He & -> & ->) | (a & Hg & -> & ->)].
    + destruct He as [<- | []]. rewrite dec_mmap_none_err in Hk. cbn in Hk. injection Hk as <- _.
      rewrite is_err_neg by (unfold ENOMEM; lia). cbn [nrefusal]. unfold efferr, eff0. cbn [eff_ret]. apply bv_eqb_refl.
    + unfold dec_mmap_none in Hk. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins] in Hk.
      change (mmap_len len) with (page_round_up_Z len) in Hk. rewrite !bv_eqb_refl in Hk.
      destruct (mmap_addr_ok len [] (bv_unsigned a)) eqn:Ha; cbn in Hk; [| discriminate Hk].
      injection Hk as <- _. apply mmap_addr_ok_true in Ha as [(A1 & A2 & A3) _].
      cbn [nrefusal eff_ret]. rewrite NE by lia. symmetry. unfold is_err, TWO64. apply Z.ltb_ge. lia.
  - change ((MAPF =? MAP_ANON_PRIV) && (PROT_RW =? PROT_RW_Z)) with true in Hst. cbv iota in Hst.
    change (PROT_RW =? 0) with false in Hk. cbv iota in Hk.
    destruct Hst as [(e & He & -> & ->) | (a & Hg & -> & ->)].
    + destruct He as [<- | []]. rewrite dec_mmap_err in Hk. cbn in Hk. injection Hk as <- _.
      rewrite is_err_neg by (unfold ENOMEM; lia). cbn [nrefusal]. unfold efferr, eff0. cbn [eff_ret]. apply bv_eqb_refl.
    + unfold dec_mmap in Hk. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins] in Hk.
      change (mmap_len len) with (page_round_up_Z len) in Hk. rewrite !bv_eqb_refl in Hk.
      destruct (mmap_addr_ok len [] (bv_unsigned a)) eqn:Ha; cbn in Hk; [| discriminate Hk].
      injection Hk as <- _. apply mmap_addr_ok_true in Ha as [(A1 & A2 & A3) _].
      cbn [nrefusal eff_ret]. rewrite NE by lia. symmetry. unfold is_err, TWO64. apply Z.ltb_ge. lia.
Qed.

Lemma mprotect_refusal_iff a len prot s mo kk eff mo1 z s1 :
  ev_step (EMprotect a len prot) s = Vis (NMprotect a len prot) kk ->
  nstep (NMprotect a len prot) mo eff mo1 [] -> kk eff = Ret (Ok (z, s1)) ->
  nrefusal (NMprotect a len prot) mo eff = negb (z =? 0).
Proof.
  intros Hvis Hst Hk.
  destruct (ev_step_mprotect_shape a len prot s) as (kk' & Hvis' & Hkk). rewrite Hvis in Hvis'. injection Hvis' as <-.
  rewrite Hkk in Hk. destruct Hst as [_ Hst]. cbv zeta in Hst.
  destruct Hst as [(e & He & -> & ->) | (_ & -> & ->)].
  - destruct He as [<- | []].
    assert (D : dec_mprotect_rw a len (efferr ENOMEM) = Some (RgErr ENOMEM)).
    { unfold dec_mprotect_rw, dec_mprotect, efferr, eff0. cbn [eff_ret eff_writes eff_zeros eff_unmaps eff_copies eff_copyins].
      rewrite errno_of_errno_ret by (unfold ENOMEM; lia). reflexivity. }
    rewrite D in Hk. cbn in Hk. injection Hk as <- _.
    cbn [nrefusal]. unfold efferr, eff0. cbn [eff_ret]. unfold ret_in_errnos, mprotect_errnos. cbn [existsb]. rewrite bv_eqb_refl.
    reflexivity.
  - change (page_round_up_Z len) with (mmap_len len) in Hk. rewrite dec_mprotect_rw_ok in Hk. cbn in Hk. injection Hk as <- _.
    cbn [nrefusal eff_ret]. unfold ret_in_errnos, mprotect_errnos. cbn [existsb]. rewrite orb_false_r.
    apply bv_eqb_neq. intros E. apply (f_equal bv_unsigned) in E.
    rewrite errno_ret_unsigned in E by (unfold ENOMEM; lia). change (bv_unsigned (Z_to_bv 64 0)) with 0 in E.
    unfold two_pow_64, ENOMEM in E. lia.
Qed.

Lemma nstep_cfg_nonref nd mo eff mo1 eff0 mo0 :
  nstep_cfg nd mo eff mo1 [] -> nstep nd mo eff0 mo0 [] -> nrefusal nd mo eff0 = false -> nrefusal nd mo eff = false.
Proof.
  intros [_ Hf] H0 Hr0. destruct (nrefusal nd mo eff) eqn:E; [| reflexivity].
  rewrite (Hf eq_refl eff0 mo0 [] H0) in Hr0. discriminate Hr0.
Qed.

Lemma membed_cfg_inv {R} e (k : Z -> stree ev Z R) s mo r mo' :
  is_sys e = true -> tpath nstep_cfg (membed (SVis e k) s) mo [] r mo' ->
  exists kk eff mo1 v, ev_step e s = Vis (node_of e) kk /\ nstep_cfg (node_of e) mo eff mo1 [] /\ kk eff = Ret v
    /\ match v with Unr => r = Unr | Ok (z, s1) => tpath nstep_cfg (membed (k z) s1) mo1 [] r mo' end.
Proof.
  intros Hs Hp. destruct (ev_step_vis e s Hs) as (kk & Hvis & Hret).
  cbn [membed] in Hp. unfold mbind in Hp. apply (proj1 (tpath_ebind _ _ _ _ _ _ _ _)) in Hp. rewrite Hvis in Hp.
  destruct Hp as [[H1 Er] | (tr1 & [z s1] & mo1 & tr2 & H1 & H2 & Etr)].
  - cbn in H1. destruct H1 as (eff & mo1 & evs & tr' & Hst & Hk & _).
    destruct (Hret eff) as [v Hv]. rewrite Hv in Hk. cbn in Hk. destruct Hk as (Ev & _ & _). subst v.
    pose proof (nstep_evs_nil' _ _ _ _ _ Hst) as Eevs. subst evs.
    exists kk, eff, mo1, Unr. auto.
  - destruct tr1; [| discriminate Etr]. destruct tr2; [| discriminate Etr].
    cbn in H1. destruct H1 as (eff & mo1' & evs & tr' & Hst & Hk & _).
    destruct (Hret eff) as [v Hv]. rewrite Hv in Hk. cbn in Hk. destruct Hk as (Ev & Emo & _). subst v mo1'.
    pose proof (nstep_evs_nil' _ _ _ _ _ Hst) as Eevs. subst evs.
    exists kk, eff, mo1, (Ok (z, s1)). split; [exact Hvis|]. split; [exact Hst|]. split; [exact Hv|]. exact H2.
Qed.

Lemma CB_nonneg L pbrk mo : KL L pbrk mo -> 0 <= CB L.
Proof.
  intros HK. unfold CB. destruct (ld_brk L); try lia. all: destruct (ld_brkreg L) as [[b l]|] eqn:E; [| lia].
  all: pose proof (kl_brkreg _ _ _ HK b l E) as (R1 & R2 & R3 & _); unfold PGSZ in *; apply Z.div_pos; lia.
Qed.
Lemma HCC_any L pbrk mo e z :
  KL L pbrk mo -> event_pre L e ->
  gc (event_post L e z) + CB (event_post L e z) <= gc L + CB L + 1.
Proof.
  intros HK Hpre. pose proof (kl_phase _ _ _ HK) as PH. pose proof (CB_nonneg L pbrk mo HK) as CB0.
  destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [event_pre] in Hpre; try (destruct Hpre; fail).
  - destruct (Z.eq_dec req 0) as [->|Hr].
    + unfold event_post. cbn [Z.eqb]. rewrite gc_set_brkph. unfold CB at 1. cbn. lia.
    + unfold event_post. rewrite (proj2 (Z.eqb_neq _ _) Hr).
      destruct Hpre as [[E _]|[(cur & Hph & E)|(b & l & Hph & Hreg & E)]]; [lia| |].
      * rewrite Hph in PH. destruct PH as (_ & _ & _ & Hreg).
        destruct (z =? req); rewrite ?Hph; rewrite gc_set_brkph; unfold CB; cbn; rewrite ?Hph, ?Hreg; lia.
      * pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & _).
        destruct (z =? req); rewrite ?Hph, ?Hreg.
        -- rewrite gc_set_brkreg. unfold CB. cbn. rewrite Hph, Hreg. unfold PGSZ in *.
           assert ((l + 4096) / 4096 = l / 4096 + 1) by (replace (l + 4096) with (1 * 4096 + l) by lia; rewrite Z.div_add_l by lia; lia). lia.
        -- rewrite gc_set_brkph. unfold CB. cbn. rewrite Hph, Hreg. lia.
  - unfold event_post. destruct (Z.land flags MAP_FIXED =? 0) eqn:Ef.
    + destruct (is_err z); [lia|]. destruct (prot =? PROT_NONE).
      * rewrite gc_add_meta, CB_set_metas. lia.
      * rewrite gc_add_group, CB_set_groups. lia.
    + destruct Hpre as [(Hq & _ & -> & _) | (cur & Hph & _)].
      * exfalso. vm_compute in Ef. discriminate Ef.
      * rewrite Hph in PH. destruct PH as (_ & _ & _ & Hreg & _).
        rewrite gc_set_brkph, gc_set_brkreg. unfold CB. cbn. rewrite Hph. unfold PGSZ. rewrite Z.div_mul by lia. lia.
  - unfold event_post. rewrite CB_set_groups. unfold gc. cbn [ld_groups ld_metas set_groups].
    pose proof (g_remove_length addr (ld_groups L)). lia.
  - unfold event_post. destruct ((z =? 0) || (z =? TWO64 - ENOSYS)); [rewrite gc_bump, CB_set_metas|]; lia.
Qed.

Section PATHCFG.
Variables (n SMAX ETOT NR RBY : Z).
Hypothesis SMAX0 : 0 <= SMAX.
Hypothesis RBY0 : 0 <= RBY.
Hypothesis HGAP : GAPOK n SMAX ETOT NR RBY.

Theorem all_succ_path : forall (t : stree ev Z (mstate * option cptr)) D L s mo,
  pos D t (fun r => snd r <> None) -> qtree LBUDGET L t TT -> nok (CE n) t -> NI ETOT NR RBY D L s mo -> LEAF SMAX t s mo ->
  forall r mo', tpath nstep_cfg (membed t s) mo [] r mo' -> exists cs' p s', r = Ok ((cs', Some p), s').
Proof.
  induction t as [r0|e k IH]; intros D L s mo HP HQ HN HNI HL r mo' Hp.
  { cbn in HP, Hp. destruct Hp as (<- & _ & _). destruct r0 as [cs' [p|]]; [| exfalso; apply HP; reflexivity]. exists cs', p, s. reflexivity. }
  destruct D as [|D]; [destruct HP|]. cbn [pos] in HP.
  cbn [qtree] in HQ. destruct HQ as (Hpre & HB & HQk).
  assert (HNk : (forall z, lall (CE n e) (k z)) /\ (forall z, nok (CE n) (k z))).
  { cbn in HN. destruct e; try exact HN; cbn in Hpre; destruct Hpre. }
  clear HN. destruct HNk as [NK1 NK2]. pose proof HNI as [HK HLI Hlim HR HC].
  assert (Hsys : is_sys e = true) by (destruct e; try reflexivity; cbn in Hpre; destruct Hpre).
  destruct (membed_cfg_inv e k s mo r mo' Hsys Hp) as (kk & eff & mo1 & v & Hvis & Hcfg & Hkv & Hrest).
  pose proof (nstep_cfg_sub _ _ _ _ _ Hcfg) as Hst.
  destruct (child_inv LBUDGET L e s mo kk eff mo1 v Hpre HK HLI HB Hvis Hst Hkv) as (z & s1 & Ev & Ha & HK1 & HLI1 & Hm).
  subst v. cbv iota beta in Hrest.

  assert (Hpz : posz e z).
  { destruct e as [req|addr len prot flags|addr len|addr len prot|? ? ?|?]; cbn [posz]; try exact I; cbn [event_pre] in Hpre; try (destruct Hpre; fail).
    - destruct Hpre as [(Hq & -> & -> & Hp' & Hlen)|(cur & Hph & -> & -> & -> & ->)].
      + right.
        destruct (nonfixed_len_bound n SMAX ETOT NR RBY SMAX0 L D s mo len prot k HNI Hq Hp' Hlen HB
                    ltac:(intros z' Hz'; exact (qtree_ctree_ok _ _ _ _ (HQk z' Hz'))) NK1 HL) as [HLM HGB].
        destruct (node_mmap_grant n SMAX ETOT NR RBY RBY0 HGAP L D s mo len prot HNI Hq Hp' Hlen HB HLM HGB)
          as (kk0 & eff0 & mo0 & a & Hvis0 & Hst0 & Hk0 & Herr0 & _).
        rewrite Hvis in Hvis0. injection Hvis0 as Ekk. subst kk0.
        pose proof (mmap_refusal_iff len prot s mo kk eff0 mo0 a s Hp' Hlen Hvis Hst0 Hk0) as R0. rewrite Herr0 in R0.
        pose proof (nstep_cfg_nonref _ _ _ _ _ _ Hcfg Hst0 R0) as R1.
        rewrite (mmap_refusal_iff len prot s mo kk eff mo1 z s1 Hp' Hlen Hvis Hst Hkv) in R1. exact R1.
      + left. reflexivity.
    - destruct (node_munmap ETOT NR RBY L D s mo addr len HNI) as (kk0 & eff0 & mo0 & Hvis0 & Hst0 & Hk0 & _).
      rewrite Hvis in Hvis0. injection Hvis0 as Ekk. subst kk0.
      destruct Hst as [_ [Ee _]]. destruct Hst0 as [_ [Ee0 _]]. subst eff eff0.
      rewrite Hk0 in Hkv. injection Hkv as Ez _. symmetry. exact Ez.
    - destruct (node_mprotect ETOT NR RBY L D s mo addr len prot HNI Hpre HB) as (kk0 & eff0 & mo0 & Hvis0 & Hst0 & Hk0 & _).
      rewrite Hvis in Hvis0. injection Hvis0 as Ekk. subst kk0.
      pose proof (mprotect_refusal_iff addr len prot s mo kk eff0 mo0 0 s Hvis Hst0 Hk0) as R0. cbn in R0.
      pose proof (nstep_cfg_nonref _ _ _ _ _ _ Hcfg Hst0 R0) as R1.
      rewrite (mprotect_refusal_iff addr len prot s mo kk eff mo1 z s1 Hvis Hst Hkv) in R1.
      destruct (z =? 0) eqn:E; [apply Z.eqb_eq in E; exact E | discriminate R1]. }
  destruct (nstep_vm_const _ _ _ _ _ Hst) as [E1 E2].
  exact (IH z D (event_post L e z) s1 mo1 (HP z Hpz) (HQk z Ha) (NK2 z)
           (NI_child ETOT NR RBY D L _ s s1 mo mo1 HNI HK1 HLI1 E1 E2 (HCC_any L (ps_brk s) mo e z HK Hpre))
           (LEAF_child SMAX e k s mo kk eff mo1 z s1 Hvis Hst Hkv HL) r mo' Hrest).
Qed.
End PATHCFG.

End AC_1.
