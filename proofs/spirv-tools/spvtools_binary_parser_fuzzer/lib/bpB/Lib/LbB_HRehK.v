(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil PropExec LibIface SymExec3 SymExec3Sound.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HLib HRepFacts HStmts HRehashModel.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsIface BXXRep.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.bpB.Lib Require Import LbB_MILB.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Import SymExec3.SX2. Import SymExec3Sound.SX2S.

Section RehK.
  Context {HCEIL : HeapCeil}.
  Variables (n obj bl bc : Z) (ents : list (Z * (Z * Z))).

  #[local] Notation ent := (Z * (Z * Z))%type.
  Definition d0 : ent := (0, (0, 0)).
  #[local] Notation addr := (HRehashModel.addr Z).
  #[local] Notation hkey := (HRehashModel.hkey Z).
  #[local] Notation hh := (HRehashModel.hh Z n).
  #[local] Notation sent := (obj + 16).

  Lemma ent_facts : forall A1 M1 e, umapx MI_A 24 (nval24 ASEGS) A1 M1 obj bl bc ents -> In e ents ->
    0 < addr e /\ addr e + 24 <= 2 ^ 47 /\ addr e mod 16 = 0 /\ 0 <= hkey e < 2 ^ 32.
  Proof.
    intros A1 M1 [q [k v]] U Hin. destruct (u_node U q k v Hin) as (_ & Hq0 & Hq1 & Hal & _ & _ & Hkr & _). cbn. lia.
  Qed.

  Lemma last_any : forall {X : Type} (l : list X) a b, l <> [] -> last l a = last l b.
  Proof.
    intros X l a b Hne. induction l as [|q l IH]; [exfalso; exact (Hne eq_refl)|].
    destruct l as [|r l']; [reflexivity|]. cbn. cbn in IH. apply IH. discriminate.
  Qed.

  Definition hda (L : list ent) (t : Z) : Z := match L with [] => t | b :: _ => addr b end.
  Fixpoint lnk (M : mem) (Ls : list ent) (t : Z) : Prop :=
    match Ls with
    | [] => True
    | a :: Ls' => cell8 ASEGS M (addr a) (hda Ls' t) /\ lnk M Ls' t
    end.

  Lemma lnk_chain : forall M Ls, chain ASEGS M Ls <-> lnk M Ls 0.
  Proof.
    intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
    destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
  Qed.

  Lemma hd_app : forall (A B : list ent) t, hda (A ++ B) t = hda A (hda B t).
  Proof. intros [|a A] B t; reflexivity. Qed.

  Lemma hdaddr_hda : forall (A : list ent), hdaddr A = hda A 0.
  Proof. intros [|[a v] A]; reflexivity. Qed.

  Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
  Proof.
    intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
    rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
  Qed.

  Lemma last_app_ne : forall {X : Type} (A B : list X) d, B <> [] -> last (A ++ B) d = last B d.
  Proof.
    intros X A B d HB. induction A as [|a A IH]; [reflexivity|]. cbn. rewrite IH.
    destruct (A ++ B) as [|c C] eqn:HE; [| reflexivity]. apply app_eq_nil in HE. destruct HE as [_ HE]. exfalso. exact (HB HE).
  Qed.

  Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (addr a) 8) ->
    (forall a, In a Ls -> 0 <= addr a /\ addr a + 8 <= 2 ^ 64) -> lnk M' Ls t.
  Proof.
    intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
    destruct HL as [Hc HL]. split.
    - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
    - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
  Qed.

  Lemma perm_nodup : forall A1 M1 Ls, umapx MI_A 24 (nval24 ASEGS) A1 M1 obj bl bc ents -> Permutation Ls ents -> List.NoDup (map addr Ls).
  Proof.
    intros A1 M1 Ls U HP. eapply Permutation_NoDup; [apply Permutation_map; apply Permutation_sym; exact HP|].
    apply base.NoDup_ListNoDup. exact (u_nodup U).
  Qed.

  Lemma nodup_app_ne : forall (l1 l2 : list ent) b b',
    List.NoDup (map addr (l1 ++ l2)) -> In b l1 -> In b' l2 -> addr b <> addr b'.
  Proof.
    intros l1 l2 b b' Hnd H1 H2 Heq.
    revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
    cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
    destruct H1 as [<-|H1].
    - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
    - exact (IH Hnd' H1).
  Qed.

  Lemma last_in : forall (P : list ent) d, P <> [] -> In (last P d) P.
  Proof.
    intros P d HP. destruct P as [|q P']; [exfalso; exact (HP eq_refl)|].
    assert (Hc : q :: P' <> []) by discriminate. rewrite (app_removelast_last d Hc) at 2. apply in_app_iff. right. left. reflexivity.
  Qed.

  Lemma splice_facts : forall A1 M1 P S' B x M,
    umapx MI_A 24 (nval24 ASEGS) A1 M1 obj bl bc ents ->
    Permutation (P ++ x :: S') ents -> binv Z n sent P B -> P <> [] ->
    cell8 ASEGS M sent (hdaddr (P ++ x :: S')) -> chain ASEGS M (P ++ x :: S') ->
    0 <= hh x < n -> B (hh x) <> 0 ->
    exists nt P',
      cell8 ASEGS M (B (hh x)) nt /\ 0 <= nt < 2 ^ 64 /\
      (B (hh x) = sent \/ exists y, In y P /\ B (hh x) = addr y /\ addr y <> addr (last P d0) /\ addr y <> addr x) /\
      last P' d0 = last P d0 /\ P' <> [] /\ Permutation (P' ++ S') (P ++ x :: S') /\ binv Z n sent P' B /\
      (forall M3, cell8 ASEGS M3 (B (hh x)) (addr x) -> cell8 ASEGS M3 (addr x) nt -> cell8 ASEGS M3 (addr (last P d0)) (hdaddr S') ->
         (forall a, In a (P ++ S') -> addr a <> addr (last P d0) -> addr a <> addr x -> addr a <> B (hh x) -> agree_on M M3 (addr a) 8) ->
         (B (hh x) <> sent -> agree_on M M3 sent 8) ->
         cell8 ASEGS M3 sent (hdaddr (P' ++ S')) /\ chain ASEGS M3 (P' ++ S')).
  Proof.
    intros A1 M1 P S' B x M U1 PERM BI HP Cp1 CH Hh Hfull.
    pose proof (perm_nodup _ _ _ U1 PERM) as NDL.
    pose proof (u_obj_lo U1) as Hobj0.
    assert (Hnoty : forall e, In e (P ++ x :: S') -> addr e <> sent).
    { intros e He. assert (Hin : In e ents) by (eapply Permutation_in; [exact PERM | exact He]).
      destruct e as [q [k v]]. destruct (u_node U1 q k v Hin) as (_ & Hq0 & _ & _ & _ & _ & _ & _ & Hap & _). unfold apart in Hap. cbn. lia. }
    assert (Hrng : forall e, In e (P ++ x :: S') -> 0 <= addr e /\ addr e + 8 <= 2 ^ 64).
    { intros e He. destruct (ent_facts _ _ e U1 ltac:(eapply Permutation_in; [exact PERM | exact He])) as (H0 & H1 & _). lia. }
    apply lnk_chain in CH.
    set (w := last P d0).
    assert (HwP : In w P) by (unfold w; apply last_in; exact HP).

    pose proof NDL as NDxS. rewrite map_app in NDxS. apply NoDup_app_remove_l in NDxS. cbn in NDxS. apply NoDup_cons_iff in NDxS. destruct NDxS as [HxS NDS].
    assert (HSx : forall a, In a S' -> addr a <> addr x) by (intros a Ha He; apply HxS; rewrite <- He; apply in_map; exact Ha).
    assert (HPx : forall a, In a P -> addr a <> addr x) by (intros a Ha; exact (nodup_app_ne P (x :: S') a x NDL Ha (or_introl eq_refl))).
    assert (HPS : forall a b, In a P -> In b S' -> addr a <> addr b) by (intros a b Ha Hb; exact (nodup_app_ne P (x :: S') a b NDL Ha (or_intror Hb))).
    destruct (bi_just _ _ _ _ _ BI (hh x) Hh Hfull) as [[Ht (x0 & P0 & HP0 & Hx0)] | (P1 & y & z & P2 & HPd & Ht & Hz)].
    -
      exists (addr x0), (x :: P).
      assert (Hhd : hdaddr (P ++ x :: S') = addr x0) by (rewrite HP0; destruct x0 as [q v]; reflexivity).
      assert (HPR : P = removelast P ++ [w]) by (unfold w; apply app_removelast_last; exact HP).
      pose proof NDL as NDP. rewrite map_app in NDP. apply NoDup_app_remove_r in NDP.
      split; [rewrite Ht, <- Hhd; exact Cp1|].
      split; [pose proof (Hrng x0 ltac:(rewrite HP0; left; reflexivity)); lia|].
      split; [left; exact Ht|].
      split; [unfold w; rewrite HP0; reflexivity|].
      split; [discriminate|].
      split; [cbn [app]; apply Permutation_middle|].
      split.
      { apply (step_front Z n sent P x B BI Hh Ht ltac:(lia)).
        intros Q1 y z Q2 HQ. apply Hnoty. apply in_app_iff. left. rewrite HQ. apply in_app_iff. right. left. reflexivity. }
      intros M3 C3t C3x C3w AG AGs.
      split; [replace (hdaddr ((x :: P) ++ S')) with (addr x) by (destruct x as [q v]; reflexivity); rewrite <- Ht; exact C3t|].
      apply lnk_chain. cbn [app lnk]. split; [rewrite hd_app; rewrite HP0; cbn; exact C3x|].
      rewrite HPR in CH |- *. rewrite <- app_assoc in CH |- *. cbn [app] in CH |- *.
      apply lnk_app in CH. destruct CH as [CHR [CHw [CHx CHS]]]. cbn [hda] in CHR.
      apply lnk_app. cbn [lnk hda]. split; [|split; [rewrite <- hdaddr_hda; exact C3w | ]].
      + eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; rewrite HPR; apply in_app_iff; left; exact Ha].
        intros a Ha. assert (HaP : In a P) by (rewrite HPR; apply in_app_iff; left; exact Ha).
        apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HaP].
        rewrite HPR in NDP. exact (nodup_app_ne _ _ a w NDP Ha (or_introl eq_refl)).
      + eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
        intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; apply Hnoty; apply in_app_iff; right; right; exact Ha].
    -
      remember (z :: P2) as Q2 eqn:HQ2.
      assert (HQne : Q2 <> []) by (rewrite HQ2; discriminate).
      assert (HhQ : forall u, hda Q2 u = addr z) by (intros u; rewrite HQ2; reflexivity).
      assert (HwQ : last Q2 d0 = w) by (unfold w; rewrite HPd; symmetry; rewrite last_app_ne by discriminate; cbn; rewrite HQ2; reflexivity).
      assert (HQR : Q2 = removelast Q2 ++ [w]) by (rewrite <- HwQ; apply app_removelast_last; exact HQne).
      assert (HwQ2 : In w Q2) by (rewrite HQR; apply in_app_iff; right; left; reflexivity).
      assert (HF1 : P ++ x :: S' = P1 ++ (y :: Q2 ++ x :: S')) by (rewrite HPd, <- app_assoc; reflexivity).
      assert (HF2 : P ++ x :: S' = (P1 ++ [y]) ++ (Q2 ++ x :: S')) by (rewrite HPd, <- !app_assoc; reflexivity).
      assert (HyP : In y P) by (rewrite HPd; apply in_app_iff; right; left; reflexivity).
      assert (HQP : forall a, In a Q2 -> In a P) by (intros a Ha; rewrite HPd; apply in_app_iff; right; right; exact Ha).
      pose proof NDL as ND2. rewrite HF2 in ND2.
      assert (HyQS : forall a, In a (Q2 ++ x :: S') -> addr y <> addr a) by (intros a Ha; exact (nodup_app_ne _ _ y a ND2 ltac:(apply in_app_iff; right; left; reflexivity) Ha)).
      rewrite map_app in ND2. apply NoDup_app_remove_l in ND2.
      pose proof ND2 as NDQ. rewrite map_app in NDQ. apply NoDup_app_remove_r in NDQ. rewrite HQR in NDQ.
      pose proof NDL as ND1. rewrite HF1 in ND1.
      assert (Hyw : addr y <> addr w) by (apply HyQS; apply in_app_iff; left; exact HwQ2).
      exists (addr z), (P1 ++ y :: x :: Q2).
      rewrite HF1 in CH. apply lnk_app in CH. destruct CH as [CH1 CH2]. cbn [lnk hda] in CH1, CH2. destruct CH2 as [Cy CH3].
      rewrite hd_app, HhQ in Cy.
      apply lnk_app in CH3. destruct CH3 as [CHQ [CHx CHS]]. cbn [hda] in CHQ.
      rewrite HQR in CHQ. apply lnk_app in CHQ. destruct CHQ as [CHR [CHw _]]. cbn [hda] in CHR, CHw.
      split; [rewrite Ht; exact Cy|].
      split; [pose proof (Hrng z ltac:(rewrite HF1; apply in_app_iff; right; right; apply in_app_iff; left; rewrite HQ2; left; reflexivity)); lia|].
      split; [right; exists y; split; [exact HyP | split; [exact Ht | split; [exact Hyw | apply HyQS; apply in_app_iff; right; left; reflexivity]]]|].
      split; [rewrite last_app_ne by discriminate; cbn; rewrite <- HwQ; destruct Q2; [exfalso; exact (HQne eq_refl) | reflexivity]|].
      split; [destruct P1; discriminate|].
      split; [rewrite HF1, <- app_assoc; cbn [app]; apply Permutation_app_head; apply perm_skip; apply Permutation_middle|].
      split.
      { rewrite HQ2. apply step_splice; [rewrite <- HQ2, <- HPd; exact BI | exact Ht | rewrite Hz; reflexivity | apply Hnoty; apply in_app_iff; left; exact HyP
        | pose proof (Hnoty y ltac:(apply in_app_iff; left; exact HyP)); destruct (ent_facts _ _ y U1 ltac:(eapply Permutation_in; [exact PERM | apply in_app_iff; left; exact HyP])) as (Hy0 & _); lia
        | pose proof NDL as NDP; rewrite map_app in NDP; apply NoDup_app_remove_r in NDP; rewrite HPd, HQ2 in NDP; exact NDP]. }
      intros M3 C3t C3x C3w AG AGs.
      assert (Hts : B (hh x) <> sent) by (rewrite Ht; apply Hnoty; apply in_app_iff; left; exact HyP).
      split.
      { rewrite hdaddr_hda, <- app_assoc, hd_app. cbn [hda]. rewrite hdaddr_hda, HF1, hd_app in Cp1. cbn [hda] in Cp1.
        pose proof (u_obj_hi U1). eapply cellw_agree; [exact Cp1 | exact (AGs Hts) | lia | cbn; lia]. }
      apply lnk_chain. rewrite <- app_assoc. cbn [app]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Ht; exact C3t | split; [rewrite hd_app, HhQ; exact C3x |]]].
      + eapply lnk_agree; [exact CH1 | | intros a Ha; apply Hrng; rewrite HF1; apply in_app_iff; left; exact Ha].
        intros a Ha. assert (HaP : In a P) by (rewrite HPd; apply in_app_iff; left; exact Ha).
        apply AG; [apply in_app_iff; left; exact HaP | | exact (HPx a HaP) | rewrite Ht].
        * exact (nodup_app_ne _ _ a w ND1 Ha ltac:(right; apply in_app_iff; left; exact HwQ2)).
        * exact (nodup_app_ne _ _ a y ND1 Ha (or_introl eq_refl)).
      + apply lnk_app. split.
        * rewrite HQR. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact C3w | exact I]].
          eapply lnk_agree; [exact CHR | | intros a Ha; apply Hrng; apply in_app_iff; left; apply HQP; rewrite HQR; apply in_app_iff; left; exact Ha].
          intros a Ha. assert (HaQ : In a Q2) by (rewrite HQR; apply in_app_iff; left; exact Ha).
          apply AG; [apply in_app_iff; left; exact (HQP a HaQ) | exact (nodup_app_ne _ _ a w NDQ Ha (or_introl eq_refl)) | exact (HPx a (HQP a HaQ)) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; left; exact HaQ)))].
        * eapply lnk_agree; [exact CHS | | intros a Ha; apply Hrng; apply in_app_iff; right; right; exact Ha].
          intros a Ha. apply AG; [apply in_app_iff; right; exact Ha | exact (not_eq_sym (HPS w a HwP Ha)) | exact (HSx a Ha) | rewrite Ht; exact (not_eq_sym (HyQS a ltac:(apply in_app_iff; right; right; exact Ha)))].
  Qed.

  Lemma nodes_apart : forall A1 M1 a b, umapx MI_A 24 (nval24 ASEGS) A1 M1 obj bl bc ents -> In a ents -> In b ents -> addr a <> addr b ->
    apart (addr a) 24 (addr b) 24.
  Proof.
    intros A1 M1 a b U Ha Hb Hne. apply (u_napart U); [apply in_map; exact Ha | apply in_map; exact Hb | exact Hne].
  Qed.

  Lemma chain_head_next : forall M P x S', chain ASEGS M (P ++ x :: S') -> cell8 ASEGS M (addr x) (hdaddr S').
  Proof.
    intros M P x S' CH. apply lnk_chain in CH. apply lnk_app in CH. destruct CH as [_ CH]. cbn [lnk] in CH.
    rewrite hdaddr_hda. exact (proj1 CH).
  Qed.

  Lemma chain_last_next : forall M P x S', chain ASEGS M (P ++ x :: S') -> P <> [] ->
    cell8 ASEGS M (addr (last P d0)) (addr x).
  Proof.
    intros M P x S' CH HP. apply lnk_chain in CH.
    rewrite (app_removelast_last d0 HP) in CH. rewrite <- app_assoc in CH. cbn [app] in CH.
    apply lnk_app in CH. destruct CH as [_ CH]. cbn [lnk hda] in CH. exact (proj1 CH).
  Qed.

  Lemma ents_nil_of_bc0 : forall A1 M1, umapx MI_A 24 (nval24 ASEGS) A1 M1 obj bl bc ents -> bc = 0 -> ents = [].
  Proof.
    intros A1 M1 U Hbc. destruct ents as [|[q [k v]] es] eqn:HE; [reflexivity|]. exfalso.
    rewrite <- HE in U. destruct (u_node U q k v ltac:(rewrite HE; left; reflexivity)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & Hb).
    pose proof (u_load U) as HL. rewrite HE in HL. unfold Zlength in HL. cbn [length] in HL. lia.
  Qed.
End RehK.
