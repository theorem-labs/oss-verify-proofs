(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OssFuzzTheorems.openssl.hashtable.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import PropExec CatExec ShapeAlg AgentLib AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanInit.
From OssFuzzTheorems.Proofs.openssl.hashtable.lib Require Import CxRel CxPlan CxPlanSound CxOfAps CxReblob HBPlanImage HBAtable HBCheck0 HBCheck1 HBArg HBChain HBUsageDefs
  BC2A0Lit BC2A2Lit BC2A3Lit BS6EndA0 BS6EndA2 BS6EndA3 BC3A0Lit BC3A2Lit BC3A3Lit BFEEndA0 BFEEndA2 BFEEndA3  BC2A1Lit BS6EndA1 BC3A1Lit BFEEndA1  BC2B0Lit BC2B2Lit BC2B3Lit BS6EndB0 BS6EndB2 BS6EndB3 BC3B0Lit BC3B2Lit BC3B3Lit BFEEndB0 BFEEndB2 BFEEndB3  BC2B1Lit BS6EndB1 BC3B1Lit BFEEndB1 BC1Thm HBUsage.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import CAP. Import CXS.
Open Scope Z_scope.

Definition usage_bytes (argv0 : list byte) : list byte :=
  map (Z_to_bv 8) [117; 115; 97; 103; 101; 58; 32] ++ argv0 ++ map (Z_to_bv 8) [32; 73; 78; 80; 85; 84; 10].
Definition T_usage (argv0 : list byte) (fs : Fs.Fs) : TSet :=
  t_emit (map (WriteEv (Z_to_bv 64 2)) (usage_bytes argv0)) (t_exit (Z_to_bv 64 2) fs).

(* [comment removed for export] *)
Fixpoint knows_argc2 (k : list kentry) : bool :=
  match k with
  | [] => false
  | KRange (EVar v) lo hi :: r => if (Nat.eqb v 1 && Z.eqb lo 2 && Z.eqb hi 2)%bool then true else knows_argc2 r
  | _ :: r => knows_argc2 r
  end.
Lemma knows_argc2_sound : forall segs E M k, knows_argc2 k = true -> know_ok segs E M k -> bv_unsigned (edenot E (EVar 1)) = 2.
Proof.
  intros segs E M k. induction k as [|K r IH]; intros H HK; [discriminate H|].
  inversion HK as [|? ? HK1 HKr]; subst.
  destruct K as [ | | | | |e lo hi| | | | ]; cbn [knows_argc2] in H; try (exact (IH H HKr)).
  destruct e as [ |v| | | | | | ]; try (exact (IH H HKr)).
  destruct (Nat.eqb v 1 && Z.eqb lo 2 && Z.eqb hi 2)%bool eqn:Hc; [|exact (IH H HKr)].
  apply andb_prop in Hc as [Hc H3]. apply andb_prop in Hc as [H1 H2].
  apply Nat.eqb_eq in H1. apply Z.eqb_eq in H2. apply Z.eqb_eq in H3. subst. cbn [kentry_ok] in HK1. lia.
Qed.

Section Leaf.
  Variable sp : word.
  Variable rdraw : EntryDraw.
  Variables brk0 mbase : word.
  Variable lim : Z.   (* [comment removed for export] *)
  Variables argv envp : list (list byte).
  Variable fs : Fs.Fs.
  Variable stdin : InStreams.
  Variables uid gid hw : word.
  Variable groups : list word.
  Variable net : NetQueue.
  Variables nofile sigmask : word.
  Hypothesis Hsp : valid_sp sp.
  Hypothesis Hbrk : valid_brk HASEGS brk0.
  Hypothesis Hlim : (AsanInit.LIMIT <= lim)%Z.
  Hypothesis Hva : valid_argv argv.
  Hypothesis Hve : valid_envp envp.
  Hypothesis Hfit : entry_stack_fits sp argv envp.
  Hypothesis Huid : valid_id uid.
  Hypothesis Hargc : length argv <> 2%nat.
  Let c := content_of argv fs.
  #[local] Notation SV := (SINVm HAPH sp rdraw brk0 argv envp uid hw c).
  #[local] Notation argH := (argH0 HAPH sp rdraw argv envp uid hw).
  #[local] Notation ISP := (bv_unsigned sp).
  #[local] Notation PIECE := (piece SV argH ISP fs).
  #[local] Notation FXHOLE := (fx_hole SV argH ISP fs).
  Let argv0 := nth 0 argv [].

  Lemma vals_of_SV : forall E M, SV E M ->
    edenot E (EVar 1) = Z_to_bv 64 (Z.of_nat (length argv)) /\ edenot E (EVar 3) = Z_to_bv 64 (Z.of_nat (length argv0)) /\ eb E 1%nat = argv0.
  Proof.
    intros E M H. pose proof (HBArg.vals_of_SINV1 sp brk0 argv envp rdraw hw Hsp Hva Hve uid Hfit E M (SVm_to1 sp rdraw brk0 argv envp uid hw c E M H)) as (_ & _ & H3 & H1 & _ & B1 & _).
    exact (conj H1 (conj H3 B1)).
  Qed.
  Lemma argc_range : 1 <= Z.of_nat (length argv) <= 1024. Proof. destruct Hva as [H _]. lia. Qed.
  Lemma L0_range : 0 <= Z.of_nat (length argv0) <= 131071.
  Proof. split; [lia|]. unfold argv0. apply (valid_argv_str_len argv 0 Hva). destruct Hva as [H _]. lia. Qed.

  (* [comment removed for export] *)
  Lemma no98 : forall cs T, knows_argc2 (kn cs) = true -> PIECE cs T.
  Proof.
    intros cs T Hk E R FULL m HC. exfalso.
    pose proof (knows_argc2_sound _ _ _ _ Hk (co_know _ _ _ _ _ _ _ _ _ _ _ _ HC)) as H2.
    destruct (vals_of_SV E FULL (co_sinv _ _ _ _ _ _ _ _ _ _ _ _ HC)) as (H1 & _ & _).
    rewrite H1 in H2. pose proof argc_range. rewrite Z_to_bv_unsigned in H2. unfold bv_wrap, bv_modulus in H2. rewrite Z.mod_small in H2 by lia. lia.
  Qed.

  Definition T98 : env -> Fs.Fs -> TSet := fun _ _ => t_nil.
  Lemma T98_agree : t_agree T98. Proof. intros E E' fs0 _. reflexivity. Qed.
  Lemma T98_nil : forall E fs0, T98 E fs0 []. Proof. reflexivity. Qed.

  (* [comment removed for export] *)
  Lemma T_main_usage : forall E M, SV E M -> t_eq (T_main T98 E fs) (T_usage argv0 fs).
  Proof.
    intros E M HS. destruct (vals_of_SV E M HS) as (H1 & H3 & B1). pose proof argc_range as AR. pose proof L0_range as LR.
    assert (U1 : bv_unsigned (edenot E (EVar 1)) = Z.of_nat (length argv)).
    { rewrite H1, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. lia. }
    assert (U3 : bv_unsigned (edenot E (EVar 3)) = Z.of_nat (length argv0)).
    { rewrite H3, Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. apply Z.mod_small. lia. }
    assert (X : forall T : TSet, T = t_exit (Z_to_bv 64 2) fs -> T []) by (intros T ->; apply CXS.t_exit_has_nil).
    assert (LEAF2 : t_eq (t_emit (Wp E 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]]) (t_exit (Z_to_bv 64 2) fs)) (T_usage argv0 fs)).
    { unfold Wp, T_usage, usage_bytes. cbn [flat_map piece_den]. rewrite B1, app_nil_r. apply t_eq_refl. }
    assert (LEAF1 : length argv0 = 0%nat -> t_eq (t_emit (Wp E 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]]) (t_exit (Z_to_bv 64 2) fs)) (T_usage argv0 fs)).
    { intros H0. unfold Wp, T_usage, usage_bytes. cbn [flat_map piece_den]. destruct argv0; [|discriminate H0]. rewrite app_nil_r. apply t_eq_refl. }
    assert (LEAF3 : t_eq (t_emit (Wp E 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]]) (t_emit (Wp E 2 []) (t_exit (Z_to_bv 64 2) fs))) (T_usage argv0 fs)).
    { eapply t_eq_trans; [apply t_emit_congr; apply t_emit_nil_eq; apply CXS.t_exit_has_nil | exact LEAF2]. }
    assert (LEAF4 : t_eq (t_emit (Wp E 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1]) (t_emit (Wp E 2 [SPLit [32; 73; 78; 80; 85; 84; 10]]) (t_exit (Z_to_bv 64 2) fs))) (T_usage argv0 fs)).
    { eapply t_eq_trans; [apply t_eq_sym; apply t_emit_app|]. unfold Wp, T_usage, usage_bytes. cbn [flat_map piece_den]. rewrite B1, !app_nil_r, <- map_app, <- app_assoc. apply t_eq_refl. }
    assert (USAGE : t_eq (sd (HOLES3 T98) t_nil E fs
              (SCase (EVar 3) 63
                 (SCase (EVar 3) 0 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32; 32; 73; 78; 80; 85; 84; 10]] (SHole 20))
                    (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))
                 (SCase (EVar 3) 64 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))
                    (SCase (EVar 3) 73
                       (SCase (EVar 3) 66 (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20))
                          (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1; SPLit [32; 73; 78; 80; 85; 84; 10]] (SEmitP 2 [] (SHole 20))))
                       (SEmitP 2 [SPLit [117; 115; 97; 103; 101; 58; 32]; SPBlob 1] (SEmitP 2 [SPLit [32; 73; 78; 80; 85; 84; 10]] (SHole 20)))))))
            (T_usage argv0 fs)).
    { cbn [sd]. rewrite U3. change (HOLES3 T98 20 E fs) with (t_exit (Z_to_bv 64 2) fs).
      repeat match goal with |- context [(?a <=? ?b)%Z] => destruct (Z.leb_spec a b) end;
        first [exact LEAF2 | exact LEAF3 | exact LEAF4 | apply LEAF1; lia]. }
    unfold T_main, usage_shape. cbn [sd]. rewrite U1.
    destruct (Z.leb_spec (Z.of_nat (length argv)) 1); [exact USAGE|].
    destruct (Z.leb_spec (Z.of_nat (length argv)) 2); [lia | exact USAGE].
  Qed.

  (* [comment removed for export] *)
  Hypothesis H_S6_A0 : FXHOLE c2a0_hs10 s6enda0.   Hypothesis H_FE_A0 : FXHOLE c3a0_hs20 feenda0.
  Hypothesis H_S6_A2 : FXHOLE c2a2_hs10 s6enda2.   Hypothesis H_FE_A2 : FXHOLE c3a2_hs20 feenda2.
  Hypothesis H_S6_A3 : FXHOLE c2a3_hs10 s6enda3.   Hypothesis H_FE_A3 : FXHOLE c3a3_hs20 feenda3.
  Hypothesis H_S6_A1 : FXHOLE c2a1_hs10 s6enda1.   Hypothesis H_FE_A1 : FXHOLE c3a1_hs20 feenda1.
  Hypothesis H_S6_B0 : FXHOLE c2b0_hs10 s6endb0.   Hypothesis H_FE_B0 : FXHOLE c3b0_hs20 feendb0.
  Hypothesis H_S6_B2 : FXHOLE c2b2_hs10 s6endb2.   Hypothesis H_FE_B2 : FXHOLE c3b2_hs20 feendb2.
  Hypothesis H_S6_B3 : FXHOLE c2b3_hs10 s6endb3.   Hypothesis H_FE_B3 : FXHOLE c3b3_hs20 feendb3.
  Hypothesis H_S6_B1 : FXHOLE c2b1_hs10 s6endb1.   Hypothesis H_FE_B1 : FXHOLE c3b1_hs20 feendb1.

  Theorem usage_leaf :
    crz HASEGS (init_config HASEGS AsanUbsan.M.init_pc HAPH sp brk0 mbase rdraw lim
                  (inp argv envp fs stdin uid gid hw groups net nofile sigmask))
        (T_usage argv0 fs).
  Proof.
    pose proof (usage_chain sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask Hsp Hbrk Hlim Hva Hve Hfit Huid T98 T98_agree T98_nil
                  H_S6_A0 H_FE_A0 (no98 c3a0_hs98 T98 eq_refl)
                  H_S6_A2 H_FE_A2 (no98 c3a2_hs98 T98 eq_refl)
                  H_S6_A3 H_FE_A3 (no98 c3a3_hs98 T98 eq_refl) H_S6_A1 H_FE_A1 (no98 c3a1_hs98 T98 eq_refl)
                  H_S6_B0 H_FE_B0 (no98 c3b0_hs98 T98 eq_refl)
                  H_S6_B2 H_FE_B2 (no98 c3b2_hs98 T98 eq_refl)
                  H_S6_B3 H_FE_B3 (no98 c3b3_hs98 T98 eq_refl) H_S6_B1 H_FE_B1 (no98 c3b1_hs98 T98 eq_refl)) as RZ.
    eapply crz_conseq; [exact RZ|].
    apply (T_main_usage _ (FULL0 HAPH sp rdraw argv envp uid hw)).
    apply SINVm_reblob.
    exact (AsanPlanSound.APS.co_sinv _ _ _ _ _ _ _ _ _ _ _ _ (init_cs_ok HASEGS HAT HAPH sp rdraw brk0 mbase lim argv envp fs stdin uid gid hw groups net nofile sigmask
                  ha_img_facts Hsp Hbrk Hlim Hva Hve Hfit Huid)).
  Qed.
End Leaf.
