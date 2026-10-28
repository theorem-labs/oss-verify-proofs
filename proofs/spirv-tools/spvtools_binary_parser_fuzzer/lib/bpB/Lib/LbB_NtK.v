(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import LibIface.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.LibHash Require Import HRep HRepFacts.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section Link.
  Context {AC : AllocCeiling}.
  Variable SEGS : list Segment.
  Variable L : Layout.
  Variable MI : MallocIface SEGS L.
  Variables (obj key : Z).

    #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

    Definition hda (l : list ent) (t : Z) : Z := match l with [] => t | b :: _ => fst b end.
    Fixpoint lnk (M : mem) (Ls : list ent) (t : Z) : Prop :=
      match Ls with
      | [] => True
      | a :: Ls' => cell8 SEGS M (fst a) (hda Ls' t) /\ lnk M Ls' t
      end.
    Lemma lnk_chain : forall M Ls, chain SEGS M Ls <-> lnk M Ls 0.
    Proof.
      intros M Ls. induction Ls as [|[a v] Ls IH]; cbn; [tauto|].
      destruct Ls as [|[b v'] Ls']; cbn in *; tauto.
    Qed.
    Lemma hd_app : forall (A B : list ent) t, hda (A ++ B) t = hda A (hda B t).
    Proof using. intros [|a A] B t; reflexivity. Qed.
    Lemma hdaddr_hda : forall (A : list ent), hdaddr A = hda A 0.
    Proof using. intros [|[a v] A]; reflexivity. Qed.
    Lemma lnk_app : forall M A B t, lnk M (A ++ B) t <-> lnk M A (hda B t) /\ lnk M B t.
    Proof.
      intros M A B t. induction A as [|a A IH]; cbn; [tauto|].
      rewrite hd_app. rewrite IH. destruct A as [|a' A']; (first [solve [clear; cbn; tauto] | cbn; tauto]).
    Qed.
    Lemma lnk_agree : forall M M' Ls t, lnk M Ls t -> (forall a, In a Ls -> agree_on M M' (fst a) 8) ->
      (forall a, In a Ls -> 0 <= fst a /\ fst a + 8 <= 2 ^ 64) -> lnk M' Ls t.
    Proof.
      intros M M' Ls t. induction Ls as [|a Ls IH]; intros HL HA HR; cbn in *; [exact I|].
      destruct HL as [Hc HL]. split.
      - pose proof (HR a (or_introl eq_refl)). eapply cellw_agree; [exact Hc | apply HA; left; reflexivity | lia | cbn; lia].
      - apply IH; [exact HL | intros b Hb; apply HA; right; exact Hb | intros b Hb; apply HR; right; exact Hb].
    Qed.

    Definition lasta (t : Z) (l1 : list ent) : Z := match l1 with [] => t | _ => fst (last l1 (0, (0, (0, 0, 0)))) end.

    Lemma nodup_app_ne : forall (l1 l2 : list ent) b b',
      List.NoDup (map fst (l1 ++ l2)) -> In b l1 -> In b' l2 -> fst b <> fst b'.
    Proof using.
      intros l1 l2 b b' Hnd H1 H2 Heq.
      revert Hnd H1. induction l1 as [|x l1 IH]; intros Hnd H1; [destruct H1|].
      cbn in Hnd. inversion Hnd as [|y l Hni Hnd']. subst.
      destruct H1 as [<-|H1].
      - apply Hni. rewrite Heq, map_app. apply in_app_iff. right. apply in_map. exact H2.
      - exact (IH Hnd' H1).
    Qed.

    Lemma umapx_link : forall A M M' (p bl2 bc2 : Z) (vv : Z * Z * Z) (l1 l2 : list ent),
      umapx MI 32 (nval32 SEGS) A M obj bl2 bc2 (l1 ++ l2) -> bc2 <> 0 -> Zlength (l1 ++ l2) + 1 <= bc2 ->
      0 <= key < 2 ^ 32 ->
      In (p, 32) (live MI A) -> 0 < p -> p + 32 <= 2 ^ 47 -> p mod 16 = 0 -> apart p 32 obj 40 ->
      (forall q m, In (q, m) (umap_blocks 32 bl2 bc2 (l1 ++ l2)) -> apart p 32 q m) ->
      cell8 SEGS M' p (hdaddr l2) -> cell8 SEGS M' (p + 8) key -> cell4 SEGS M' (p + 16) key -> nval32 SEGS M' p vv ->
      cell8 SEGS M' (lasta (obj + 16) l1) p -> cell8 SEGS M' (obj + 24) (Zlength (l1 ++ l2) + 1) ->
      (forall x : word, M x <> None -> M' x <> None) ->
      (forall a, umap_foot 32 obj bl2 bc2 (l1 ++ l2) a -> ~ (lasta (obj + 16) l1 <= a < lasta (obj + 16) l1 + 8) -> ~ (obj + 24 <= a < obj + 32) ->
                 ~ (bl2 <= a < bl2 + 8 * bc2) -> M' (Z_to_bv 64 a) = M (Z_to_bv 64 a)) ->
      (forall i, 0 <= i < bc2 -> exists b', cell8 SEGS M' (bl2 + 8 * i) b' /\ bucket_ok obj bc2 (l1 ++ (p, (key, vv)) :: l2) i b') ->
      umapx MI 32 (nval32 SEGS) A M' obj bl2 bc2 (l1 ++ (p, (key, vv)) :: l2).
    Proof.
      intros A M M' p bl2 bc2 vv l1 l2 U Hbc Hload Hkr Hpl Hp0 Hpc Hpal Hpo Hpa Cn Ch Ck Cv Cpred Csz HG HM HB.
      destruct U as [HD Hoal Holo Hohi Hbseq Hload0 Hblive Hblal Hbllo Hblhi Hblobj Hbkt Hndup Hch Hnode Hapart].
      destruct HD as [Cbl Cbc Cp1 Csz0 Cmlf Cdef].
      pose proof (Hbllo Hbc) as Hbl0. pose proof (Hblobj Hbc) as Hblo.

      assert (NF : forall q k v', In (q, (k, v')) (l1 ++ l2) -> 0 < q /\ q + 32 <= 2 ^ 47 /\ apart q 32 obj 40 /\ apart q 32 bl2 (8 * bc2) /\ apart p 32 q 32).
      { intros q k v' Hin. destruct (Hnode q k v' Hin) as (_ & Hq0 & Hq1 & _ & _ & _ & _ & _ & Hqo & Hqb).
        split; [exact Hq0|]. split; [exact Hq1|]. split; [exact Hqo|]. split; [exact (Hqb Hbc)|].
        apply Hpa. unfold umap_blocks. apply in_app_iff. right. apply in_map_iff. exists (q, (k, v')). split; [reflexivity | exact Hin]. }

      assert (Hpred : (l1 = [] /\ lasta (obj + 16) l1 = obj + 16)
                      \/ (exists r y, l1 = r ++ [y] /\ lasta (obj + 16) l1 = fst y /\ In y (l1 ++ l2))).
      { destruct l1 as [|e l1'] eqn:HL; [left; split; reflexivity | right].
        exists (removelast l1), (last l1 (0, (0, (0, 0, 0)))). rewrite <- HL.
        assert (Hne : l1 <> []) by (rewrite HL; discriminate).
        split; [exact (app_removelast_last _ Hne)|]. split; [rewrite HL; reflexivity|].
        apply in_app_iff. left. rewrite (app_removelast_last (0, (0, (0, 0, 0))) Hne) at 2. apply in_app_iff. right. left. reflexivity. }

      assert (AGt : forall q k v', In (q, (k, v')) (l1 ++ l2) -> agree_on M M' (q + 8) 24).
      { intros q k v' Hin. destruct (NF q k v' Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
        - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin] | lia].
        - destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [unfold apart in Hqo; lia|].
          destruct y as [yq [yk yv]]. cbn. destruct (Z.eq_dec yq q) as [->|Hne]; [lia|].
          pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin]) Hne) as Hap.
          unfold apart in Hap. lia.
        - unfold apart in Hqo. lia.
        - unfold apart in Hqb. lia. }
      assert (AGn : forall q k v', In (q, (k, v')) (l1 ++ l2) -> q <> lasta (obj + 16) l1 -> agree_on M M' q 8).
      { intros q k v' Hin Hne. destruct (NF q k v' Hin) as (Hq0 & Hq1 & Hqo & Hqb & Hqp). intros i Hi. apply HM.
        - right. right. exists q. split; [apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin] | lia].
        - destruct Hpred as [[_ HL] | (r & y & HL & Hly & Hy)]; [rewrite HL in *; unfold apart in Hqo; lia|].
          rewrite Hly in *. destruct y as [yq [yk yv]]. cbn in *.
          pose proof (Hapart yq q ltac:(apply in_map_iff; exists (yq, (yk, yv)); split; [reflexivity | exact Hy]) ltac:(apply in_map_iff; exists (q, (k, v')); split; [reflexivity | exact Hin]) (not_eq_sym Hne)) as Hap.
          unfold apart in Hap. lia.
        - unfold apart in Hqo. lia.
        - unfold apart in Hqb. lia. }
      assert (Hlen : Zlength (l1 ++ (p, (key, vv)) :: l2) = Zlength (l1 ++ l2) + 1).
      { unfold Zlength. rewrite !length_app. cbn [length]. lia. }
      assert (HpN : ~ In p (map fst (l1 ++ l2))).
      { intros Hin. apply in_map_iff in Hin. destruct Hin as ([q [k v']] & Hq & Hin). cbn in Hq. subst q.
        destruct (NF p k v' Hin) as (_ & _ & _ & _ & Hap). unfold apart in Hap. lia. }
      pose proof Hndup as NDL. apply base.NoDup_ListNoDup in NDL.
      constructor.
      - constructor.
        + eapply cellw_agree; [exact Cbl | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + eapply cellw_agree; [exact Cbc | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)].
          * rewrite HL in *. cbn [app hdaddr]. rewrite Hla in Cpred. exact Cpred.
          * replace (hdaddr (l1 ++ (p, (key, vv)) :: l2)) with (hdaddr (l1 ++ l2)) by (rewrite HL, <- !app_assoc; destruct r as [|[? ?] ?]; reflexivity).
            eapply cellw_agree; [exact Cp1 | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
            rewrite Hla. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + rewrite Hlen. exact Csz.
        + eapply cellw_agree; [exact Cmlf | | lia | cbn; lia]. intros i Hi. apply HM; [left; lia | | lia | unfold apart in Hblo; lia].
          destruct Hpred as [[_ ->] | (r & y & HL & -> & Hy)]; [lia|]. destruct y as [yq [yk yv]]. destruct (NF yq yk yv Hy) as (_ & _ & Hyo & _). unfold apart in Hyo. cbn. lia.
        + intros i Hi. apply HG. apply Cdef. exact Hi.
      - exact Hoal. - exact Holo. - exact Hohi. - exact Hbseq.
      - rewrite Hlen. exact Hload.
      - exact Hblive. - exact Hblal. - exact Hbllo. - exact Hblhi. - exact Hblobj.
      - exact HB.
      - rewrite map_app. cbn [map fst]. apply (proj2 (base.NoDup_ListNoDup _)). apply (proj2 (NoDup_Add (Add_app p _ _))).
        rewrite <- map_app. split; [exact NDL | exact HpN].
      -
        apply lnk_chain. apply lnk_chain in Hch. apply lnk_app in Hch. destruct Hch as [L1 L2].
        apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- hdaddr_hda; exact Cn |]].
        + destruct Hpred as [[HL _] | (r & y & HL & Hla & Hy)]; [rewrite HL; exact I|].
          rewrite HL in L1 |- *. apply lnk_app in L1. destruct L1 as [L1 _]. apply lnk_app. cbn [lnk hda]. split; [| split; [rewrite <- Hla; exact Cpred | exact I]].
          assert (NDl1 : List.NoDup (map fst l1)) by (rewrite map_app in NDL; exact (NoDup_app_remove_r _ _ NDL)). rewrite HL in NDl1.
          eapply lnk_agree; [exact L1 | |].
          * intros a Ha. destruct a as [q [k v]]. apply (AGn q k v); [apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha|].
            rewrite Hla. exact (nodup_app_ne r [y] (q, (k, v)) y NDl1 Ha (or_introl eq_refl)).
          * intros a Ha. destruct a as [q [k v]]. destruct (NF q k v ltac:(apply in_app_iff; left; rewrite HL; apply in_app_iff; left; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
        + eapply lnk_agree; [exact L2 | |].
          * intros a Ha. destruct a as [q [k v]]. apply (AGn q k v); [apply in_app_iff; right; exact Ha|].
            destruct Hpred as [[HL Hla] | (r & y & HL & Hla & Hy)]; rewrite Hla.
            -- destruct (NF q k v ltac:(apply in_app_iff; right; exact Ha)) as (_ & _ & Hqo & _). unfold apart in Hqo. lia.
            -- apply not_eq_sym. apply (nodup_app_ne l1 l2 y (q, (k, v)) NDL); [rewrite HL; apply in_app_iff; right; left; reflexivity | exact Ha].
          * intros a Ha. destruct a as [q [k v]]. destruct (NF q k v ltac:(apply in_app_iff; right; exact Ha)) as (Hq0 & Hq1 & _). cbn. lia.
      -
        intros q k v' Hin. apply in_app_iff in Hin. destruct Hin as [Hin | [Hin | Hin]].
        2: { injection Hin as <- <- <-.
             split; [exact Hpl|]. split; [exact Hp0|]. split; [lia|]. split; [exact Hpal|]. split; [exact Ch|]. split; [exact Ck|]. split; [lia|].
             split; [exact Cv|]. split; [exact Hpo|]. intros _. apply Hpa. unfold umap_blocks. destruct (Z.eqb_spec bc2 0); [lia|]. apply in_app_iff. left. left. reflexivity. }
        all: assert (Hin' : In (q, (k, v')) (l1 ++ l2)) by (apply in_app_iff; tauto).
        all: destruct (Hnode q k v' Hin') as (Hlv & Hq0 & Hq1 & Hqal & Hh & Hk & Hkr' & Hv & Hqo & Hqb); pose proof (AGt q k v' Hin') as AG.
        all: split; [exact Hlv|]; split; [exact Hq0|]; split; [exact Hq1|]; split; [exact Hqal|].
        all: split; [eapply cellw_agree; [exact Hh | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
        all: split; [eapply cellw_agree; [exact Hk | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | cbn; lia]|].
        all: split; [exact Hkr'|].
        all: split; [eapply nval32_agree; [exact Hv | eapply agree_on_sub; [exact AG | lia | cbn; lia] | lia | lia]|].
        all: split; [exact Hqo | exact Hqb].
      -
        intros q q' Hq Hq' Hne. rewrite map_app in Hq, Hq'. cbn [map fst] in Hq, Hq'.
        assert (Hcase : forall z, In z (map fst l1 ++ p :: map fst l2) -> z = p \/ In z (map fst (l1 ++ l2))).
        { intros z Hz. rewrite map_app. apply in_app_iff in Hz. destruct Hz as [Hz|[<-|Hz]]; [right; apply in_app_iff; left; exact Hz | left; reflexivity | right; apply in_app_iff; right; exact Hz]. }
        destruct (Hcase q Hq) as [-> | Hq2]; destruct (Hcase q' Hq') as [-> | Hq2'].
        + exfalso. exact (Hne eq_refl).
        + apply in_map_iff in Hq2'. destruct Hq2' as ([z [k v']] & Hz & Hin). cbn in Hz. subst z. exact (proj2 (proj2 (proj2 (proj2 (NF q' k v' Hin))))).
        + apply in_map_iff in Hq2. destruct Hq2 as ([z [k v']] & Hz & Hin). cbn in Hz. subst z.
          pose proof (proj2 (proj2 (proj2 (proj2 (NF q k v' Hin))))) as Hap. unfold apart in *. lia.
        + exact (Hapart q q' Hq2 Hq2' Hne).
    Qed.
End Link.

From OssFuzzTheorems.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BeapCeil PropExec CatSim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BTac BArr BSysStep BExec BellsX BacX BMem BMState BLFrame BPrelim.
From OssFuzzTheorems.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import BSegs BsShadow BsConst BsIface BsCXXHeap BXXRep LbB_Kit LbB_MILB LbB_Conv LbB_HKit.

Lemma agree_of_munchV : forall W m m' a k, munch W m m' -> (forall x, a <= x < a + k -> outside W x) ->
  0 <= a -> a + k <= 2 ^ 64 -> HRepFacts.agree_on m m' a k.
Proof. intros W m m' a k MU HO Ha Hak i Hi. apply MU. rewrite HLib.u64_of_Z by lia. apply HO. lia. Qed.

Section SetVal.
  Context {HCEIL : HeapCeil}.
  #[local] Notation ent := (Z * (Z * (Z * Z * Z)))%type.

  Lemma umapx_set_val32A : forall L m m' obj bl bc (l1 l2 : list ent) (p k : Z) (v : Z * Z * Z) (t w e : Z),
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L m obj bl bc (l1 ++ (p, (k, v)) :: l2) ->
    0 <= t < 2 ^ 32 -> 0 <= w < 2 ^ 32 -> 0 <= e < 2 ^ 32 ->
    munch [(p + 20, p + 32)] m m' -> (forall x, m x <> None -> m' x <> None) ->
    rw_cells asegs m' (p + 20) [C4 (Z_to_bv 64 t)] -> rw_cells asegs m' (p + 24) [C4 (Z_to_bv 64 w)] ->
    rw_cells asegs m' (p + 28) [C4 (Z_to_bv 64 e)] ->
    @umapx AC_A ASEGS LY_A MI_A 32 (Z * Z * Z) (nval32 ASEGS) L m' obj bl bc (l1 ++ (p, (k, (t, w, e))) :: l2).
  Proof.
    intros L m m' obj bl bc l1 l2 p k v t w e U Ht Hw He MU DM RWt RWw RWe.
    destruct U as [UH Ual Ulo Uhi Ubseq Uload Ublive Ublal Ubllo Ublhi Ublobj Ubkt Unodup Uchain Unode Unapart].
    assert (Hinp : In (p, (k, v)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; left; reflexivity).
    destruct (Unode p k v Hinp) as (Hlive & Hp0 & Hp47 & Hpal & Ck8 & Ck16 & Rk & Nv & Apo & Apb).
    assert (Efst : map fst (l1 ++ (p, (k, (t, w, e))) :: l2) = map fst (l1 ++ (p, (k, v)) :: l2)) by (rewrite !map_app; reflexivity).
    assert (Elen : HRep.Zlength (l1 ++ (p, (k, (t, w, e))) :: l2) = HRep.Zlength (l1 ++ (p, (k, v)) :: l2)) by (unfold HRep.Zlength; rewrite !length_app; reflexivity).
    assert (Ehd : forall l, hdaddr ((p, (k, (t, w, e))) :: l) = hdaddr ((p, (k, v)) :: l)) by (intros; reflexivity).
    assert (Ehd2 : hdaddr (l1 ++ (p, (k, (t, w, e))) :: l2) = hdaddr (l1 ++ (p, (k, v)) :: l2)) by (destruct l1; reflexivity).

    assert (AG : forall a n, 0 <= a < 2 ^ 64 -> a + n <= 2 ^ 64 -> apart (p + 20) 12 a n -> HRepFacts.agree_on m m' a n).
    { intros a n Ha Han Hap. apply (agree_of_munchV [(p + 20, p + 32)] m m' a n MU); [| lia | lia].
      intros x Hx. cbn. unfold apart in Hap. lia. }
    assert (KEEP : forall a (wd : N) x, cellw ASEGS m a wd x -> 0 <= a -> a + Z.of_N wd <= 2 ^ 47 -> apart (p + 20) 12 a (Z.of_N wd) -> cellw ASEGS m' a wd x).
    { intros a wd x C Ha Hwd Hap. eapply cellw_agree; [exact C | apply AG; [lia | lia | exact Hap] | lia | lia]. }

    assert (OTHER : forall q kq vq, In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2) -> q <> p -> apart q 32 p 32).
    { intros q kq vq Hq Hne. apply Unapart; [| | exact Hne]; apply in_map_iff; [exists (q, (kq, vq)) | exists (p, (k, v))]; auto. }
    constructor; rewrite ?Efst, ?Elen; try assumption.
    -   destruct UH as [H1 H2 H3 H4 H5 H6]. constructor; rewrite ?Ehd2, ?Elen; unfold cell8, cell4 in *;
        try (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      intros i Hi. apply DM. exact (H6 i Hi).
    -   intros i Hi. destruct (Ubkt i Hi) as (b & Cb & Hb). exists b. split.
      + unfold cell8 in *. apply KEEP; [exact Cb | lia | cbn; lia |].
        assert (Hbc : bc <> 0) by lia. pose proof (Apb Hbc) as Ap. unfold apart in *. cbn. lia.
      + unfold bucket_ok in *. rewrite Efst. destruct Hb as [Hb|[Hb|(Hb1 & Hb2 & Hb3)]]; [left; exact Hb | right; left; exact Hb | right; right].
        split; [exact Hb1|]. split; [destruct l1; discriminate|]. rewrite Hb3. destruct l1; reflexivity.
    -
      assert (CH : forall (es : list ent), chain ASEGS m es ->
                     (forall q kq vq, In (q, (kq, vq)) es -> q = p \/ apart q 32 p 32) ->
                     (forall q kq vq, In (q, (kq, vq)) es -> 0 < q /\ q + 32 <= 2 ^ 47) ->
                     chain ASEGS m' es).
      { intros es. induction es as [|[q [kq vq]] es IH]; intros C Hq Hr; [exact Logic.I|]. cbn [chain] in C |- *. destruct C as [C1 C2].
        split; [| apply IH; [exact C2 | intros q' k' u' H'; apply (Hq q' k' u'); right; exact H' | intros q' k' u' H'; apply (Hr q' k' u'); right; exact H']].
        unfold cell8 in *. destruct (Hr q kq vq (or_introl eq_refl)) as [Hq0 Hq47].
        apply KEEP; [exact C1 | lia | cbn; lia |]. destruct (Hq q kq vq (or_introl eq_refl)) as [-> | Hap]; unfold apart in *; cbn; lia. }
      assert (CH2 : chain ASEGS m' (l1 ++ (p, (k, v)) :: l2)).
      { apply CH; [exact Uchain | |].
        - intros q kq vq Hq. destruct (Z.eq_dec q p) as [-> | Hne]; [left; reflexivity | right; exact (OTHER q kq vq Hq Hne)].
        - intros q kq vq Hq. destruct (Unode q kq vq Hq) as (_ & H0 & H47 & _). lia. }
      clear - CH2 Ehd. revert CH2. generalize l2. induction l1 as [|[q [kq vq]] l1 IH]; intros l2' C; cbn [chain app] in C |- *.
      + exact C.
      + destruct C as [C1 C2]. split; [| apply IH; exact C2]. destruct l1; [cbn in C1 |- *; exact C1 | exact C1].
    -   intros q kq vq Hq.
      assert (NP : ~ In p (map fst l1) /\ ~ In p (map fst l2)).
      { rewrite map_app in Unodup. cbn [map fst] in Unodup. apply (proj1 (list_relations.list.NoDup_app _ _)) in Unodup. destruct Unodup as (N1 & NX & N2).
        split.
        - intros H1. refine (NX p _ _); [apply list_elem_of_In; exact H1 | apply list_elem_of_In; left; reflexivity].
        - intros H2. apply (proj1 (list_relations.list.NoDup_cons _ _)) in N2. destruct N2 as [N2 _]. apply N2. apply list_elem_of_In. exact H2. }
      destruct NP as [NP1 NP2].
      apply in_app_iff in Hq. destruct Hq as [Hq|[Hq|Hq]].
      + assert (Hne : q <> p) by (intros ->; apply NP1; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; left; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8' & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        destruct vq as [[vt vw] ve]. unfold cell8, cell4, nval32 in *. destruct NV as (NVt & NVw & NVe).
        repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
      + injection Hq as E1 E2 E3. subst q kq vq.
        unfold cell8, cell4, nval32 in *.
        repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          try (apply KEEP; [assumption | lia | cbn; lia | unfold apart; cbn; lia]).
        * eapply cellw4_of_rw_cells; [exact RWt | lia | lia].
        * eapply cellw4_of_rw_cells; [exact RWw | lia | lia].
        * eapply cellw4_of_rw_cells; [exact RWe | lia | lia].
      + assert (Hne : q <> p) by (intros ->; apply NP2; apply in_map_iff; exists (p, (kq, vq)); auto).
        assert (Hq' : In (q, (kq, vq)) (l1 ++ (p, (k, v)) :: l2)) by (apply in_app_iff; right; right; exact Hq).
        destruct (Unode q kq vq Hq') as (L1 & L2 & L3 & L4 & C8' & C16 & RK & NV & AP1 & AP2). pose proof (OTHER q kq vq Hq' Hne) as AP.
        destruct vq as [[vt vw] ve]. unfold cell8, cell4, nval32 in *. destruct NV as (NVt & NVw & NVe).
        repeat match goal with |- _ /\ _ => split end; try assumption; try lia;
          (apply KEEP; [assumption | lia | cbn; lia | unfold apart in *; cbn; lia]).
  Qed.
End SetVal.
