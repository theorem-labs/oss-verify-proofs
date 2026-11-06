(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Bool Lia.
From stdpp Require Import gmap.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Spec Require Import STree Malloc MallocCtrl KInv MI_Tree MI_Inv MI_Kit MI_Geom MI_List MI_Ext
  MI_Pres2 MI_WFree2 MI_WNtf2 MI_TF2 MI_WSlot MI_WMalloc MI_Sim.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums01Z37Corelib4Init9Datatypeshc3nilhc4listhc4prod37Corelib4Init5Logick83and79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec4KInv~~~~~~m28led_init79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6MI_Inv~~~~~~q94INVLq93blkq92x079OSSVerify6Proofsaboost_jsonafuzz_parse3lib4Spec6Malloc~~~~~~v94aptrv95lheadv95minit46Stdlib6ZArith6BinInt1Zhke2lehke2lthke3powm24mledm28set_liveq96extrasv94cptrv96mstate37Corelib5Lists7ListDefhq43mapq95bslotk82eqm29ap_removeq99bl_removehc4pairk82ex36Stdlib5Lists4Listhv32In79OSSVerify6Proofsaboost_jsonafuzz_parse3lib4SpeccMI_Contracts~~~~~~igc5pans0hc4unitm27ld_livev95stripm26creachigc6SIMRELhc6optionhc3sndk84Truek83notm28ctree_okv97cmallochc4Somev95cfree" s.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma INVL_init : ltac2:(zQ "f0!h9!j4!ja!k1!lc!pe!u7!ue!v4!hj7!hje!hk6!hm6!hmc!hn2>6secret$0>4resv@1$2@2$3$0$0>0@2$4@2$cZ^2@2$d^2@2$e+2+k0@5$6$8@2$b^3^2@1$5^2@1$1$7\0$a@1$1$9").
Proof. intros secret resv.
  intros Hs.
  assert (NOH : forall b m, ~ hosts (minit secret resv) b m) by (intros b m [ai H]; cbn in H; rewrite lookup_empty in H; discriminate).
  assert (MR0 : forall m, MR (minit secret resv) m = meta0) by (intros m; unfold MR, get_meta_rec; cbn; rewrite lookup_empty; reflexivity).
  split; [| split; [| split; [| split; [| split; [| split]]]]].
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + reflexivity.
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + rewrite map_to_list_empty. cbn. apply Permutation_refl.
    + split; [lia| left; reflexivity].
    + intros b l. split; [discriminate|]. intros (rid & r & H & _). rewrite lookup_empty in H. discriminate.
    + split; [reflexivity|]. intros rid r H. rewrite lookup_empty in H. discriminate.
    + split; [lia|]. split; [lia|]. intros rid off H. discriminate.
    + split; [intros rid r H; rewrite lookup_empty in H; discriminate|]. split; [intros rid1 rid2 r1 r2 H; rewrite lookup_empty in H; discriminate|]. intros j Hj. exfalso. lia.
  - constructor; cbn; try (intros; rewrite lookup_empty in *; discriminate).
    + split; [lia|]. split; [lia|]. split; intros i v H; rewrite lookup_empty in H; discriminate.
    + split; [exact Hs|]. left. repeat split; reflexivity.
    + intros _. split; reflexivity.
    + split; [unfold NSLOTS; lia|]. intros H. lia.
    + intros sc Hsc. unfold usage, gcnt. cbn. rewrite lookup_empty, map_to_list_empty. reflexivity.
  - constructor; cbn.
    + intros m _. rewrite MR0. reflexivity.
    + intros m b H. rewrite MR0 in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
    + intros m [].
    + intros z [].
    + intros m Hm. exfalso. apply Hm. apply lookup_empty.
  - constructor; cbn.
    + intros h. destruct h; cbn; [unfold active; cbn; rewrite lookup_empty|]; reflexivity.
    + intros h. exact I.
    + intros h. constructor.
    + intros h1 h2 m [].
    + intros m. rewrite MR0. cbn. split; [| reflexivity]. split; [intros [h []]| congruence].
    + intros m [].
    + intros sc m [].
    + intros h H. exfalso. apply H. reflexivity.
  - constructor; cbn.
    + intros m b ai H. rewrite lookup_empty in H. discriminate.
    + intros b ai H. rewrite lookup_empty in H. discriminate.
    + intros m1 m2 b1 b2 ai1 ai2 H. rewrite lookup_empty in H. discriminate.
    + intros rid r H. rewrite lookup_empty in H. discriminate.
    + intros b h H. rewrite lookup_empty in H. discriminate.
    + intros m1 m2 b1 b2 ai1 ai2 H. rewrite lookup_empty in H. discriminate.
  - constructor; cbn.
    + intros s m i H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m ai i H. rewrite lookup_empty in H. discriminate.
    + intros s H. discriminate.
    + constructor.
    + intros k [].
    + intros k m i [].
  - constructor; cbn.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros rid sh H. rewrite lookup_empty in H. discriminate.
    + intros b m i H. exfalso. exact (NOH _ _ H).
    + intros b m o H. exfalso. exact (NOH _ _ H).
    + intros b m p i H. exfalso. exact (NOH _ _ H).
    + intros k m i [].
Qed.

Lemma INVL_set_live : ltac2:(zQ "a0!ja!u7!hn9!ho0!ue!hob!hj7!hp4!hje!hpb>1X$5>2st$9>1L$2>2BL@1$0$4>2LS>0$8@1$0$6>1v@1$0$7>0@5$1^6^5^4^3^2@5$1^7^6@2$3^2^5^4^3").
Proof. intros X st L BL LS v.
  intros (IR & IA & IM & IL & IG & IS & ISH). split; [| split; [exact IA| split; [exact IM| split; [exact IL| split; [exact IG| split; [exact IS| exact ISH]]]]]].
  destruct IR; constructor; cbn; auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cpath_follow {R} L (t : M R) L' r : cpath L t L' r -> exists ans, follow t ans = Some r /\ lafter L t ans = L'.
Proof.
  induction 1 as [L0 r0|L0 e k z L1 r0 Hz Hp IH].
  - exists []. split; reflexivity.
  - destruct IH as (ans & Hf & Hl). exists (z :: ans).
    destruct e; cbn [follow lafter]; try (split; [exact Hf| exact Hl]). cbn in Hz. discriminate.
Qed.

(* [comment removed for export] *)
Lemma ctree_ok_paths {R} : forall (t : M R) L (P1 P2 : mled -> R -> Prop),
  ctree_ok L t P1 -> (forall L' r, cpath L t L' r -> P2 L' r) -> ctree_ok L t P2.
Proof.
  induction t as [r|e k IH]; intros L P1 P2 H HP; cbn [ctree_ok] in *.
  - apply HP. constructor.
  - destruct H as [He Hk]. split; [exact He|]. intros z Hz. apply (IH z _ P1); [apply Hk; exact Hz|].
    intros L' r Hp. apply HP. econstructor; eauto.
Qed.

Lemma bl_remove_map : ltac2:(zQ "80!hp4!ue!ja!hrb!hs2!hsa!hsf!htb>1c$0>2BL@1$2$1@3$5@1$2$0@4$3$1$0$4@2$7^2^1@2$6^2@4$3$1$0$4^1").
Proof. intros c BL.
  induction BL as [|k BL IH]; cbn; [reflexivity|]. destruct (aptr_eqb_spec (bslot k) c) as [E|NE]; [reflexivity|]. cbn. rewrite IH. reflexivity.
Qed.

Lemma In_bslot : ltac2:(zQ "a0!h9!hp4!k1!hu7!hue!ue!ig6!ja!hrb!hs2>1c$1>2BL@1$7$5>0@3$6$1^2@4$8$5$1$9^1@2$4$0\3off$0@2$4$0\1n$0@3$6@2$2@2$2$1$0$0@4$3@2$2$1$0$0@4$3$1$0^5^2^1^4").
Proof. intros c BL.
  intros H. apply in_map_iff in H as ([[c' off] n] & E & Hin). cbn in E. subst c'. exists off, n. exact Hin.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pans0 (_ : unit) (_ : aptr) (_ _ : Z) : Z := 0.
Definition pupd0 (o : unit) (_ : ev) (_ : Z) : unit := o.
Lemma pans0_range : ltac2:(zQ "70!h9!il0!il9!lc!hj7!hm6!hmc>1o$2>1p$4>1c$0>1h$0@2$3@2$5Z@4$1^4^3^2^1@2$6@4$1^4^3^2^1+hg0").
Proof. intros. unfold pans0. lia. Qed.

Definition SIMREL : ltac2:(zQ "20!hn9!hpb>2cs$1>1L$0P") := ltac2:(zQ "h00!ja!hpb!hue!ue!lc!hsa!hj7!hp4!hje!hrb!im0!hn9!u7!hs2!v4!ima\2cs$1\1L$b@2$2$1\2st$1@2$2@1$0$3\2BL@1$0$3@2$2>0$8@1$0$6\2LS>0$8@1$0$6@2$4@3$5$1@1$f^3^5@2$4@5$c$e^3^4^2^1@3$5@1$0$7@1$a^4@4$9$3$7$d^2").

Theorem creach_sim : ltac2:(zQ "40!in2!hn9!inb!hpb>2cs$3>1L$1>0@2$0^2^1@2$2^3^2").
Proof. intros cs L.
  induction 1 as [secret resv Hs|cs L n L' cs' r CR IH Hn CP|cs L c L' cs' CR IH Hc CP].
  - exists (minit secret resv), [], (fun _ => []). split; [reflexivity|]. split; [apply INVL_init; exact Hs| reflexivity].
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. rewrite HL in RES, LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try (exfalso; exact RES).
    + destruct RES as (off & LS' & Epf & Hoff & INV' & NI).
      exists st', (((c, off), n) :: BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. reflexivity.
    + destruct RES as (LS' & INV'). exists st', BL, LS'. split; [reflexivity|]. split; [exact INV'|]. rewrite LIVE'. exact LIVE.
  - destruct IH as (st & BL & LS & <- & INV & LIVE).
    rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
    destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk)) ans) as SF.
    rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (free st (Some (aadd c (UNIT * off))))) ans) as [[o' st']|] eqn:FF; [| destruct SF].
    destruct (free_sim pans0 pupd0 pans0_range st L BL LS c off n tt ans o' st' INV Hk FF) as (Hf2 & _ & LIVE' & LS' & INV').
    rewrite Hf in Hf2. inversion Hf2. subst cs'. rewrite HL in INV', LIVE'.
    exists st', (bl_remove c BL), LS'. split; [reflexivity|]. split; [apply INVL_set_live; exact INV'|]. cbn. rewrite LIVE', LIVE. symmetry. apply bl_remove_map.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem cmalloc_contract_proof : ltac2:(zQ "f0!hp4!io5!hpb!k1!hn9!ioe!ip4!ipb!h9!in2!iq1!im0!iqc!ig6!hm6>2cs$2>1L$4>1n$8>0@2$9^3^2>0@2$eZ^2@4$a@2$3$2@1$1$0^4@2$c^5^3\2L'$4\1r@2$3$2@1$1$0M1\1x@1$1$0P@3$5$2@1$1$0^1\1c$0@1$7@3$d$0^1@1$b^3$6").
Proof.
  intros cs L n CR Hn. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  apply (ctree_ok_paths _ L (fun _ _ => True)).
  - apply ptree_ctree_ok. eapply (ptree_strel (malloc_control pans0 pupd0 pans0_range st n tt)); [intros; exact I|].
    eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range (malloc st n) L _ tt (malloc_INVL st L BL LS n INV Hn)).
  - intros L' [cs' r] CP. destruct (cpath_follow _ _ _ _ CP) as (ans & Hf & HL).
    pose proof (strel_follow (malloc_control pans0 pupd0 pans0_range st n tt) ans) as SF. rewrite Hf in SF.
    destruct (follow (prun pans0 pupd0 tt (malloc st n)) ans) as [[o' [st' rf]]|] eqn:FF; [| destruct SF].
    destruct (malloc_sim pans0 pupd0 pans0_range st L BL LS n tt ans o' st' rf INV Hn FF) as (rc & Hf2 & _ & LIVE' & _ & _ & RES).
    rewrite Hf in Hf2. inversion Hf2. subst cs' r. cbn [snd]. rewrite HL in LIVE'.
    destruct rf as [pf|]; destruct rc as [c|]; try exact I; try (exfalso; exact RES).
    destruct RES as (off & LS' & _ & _ & _ & NI). rewrite LIVE', LIVE. exact NI.
Qed.

Theorem cfree_contract_proof : ltac2:(zQ "a0!hp4!hpb!hn9!ir6!ip4!in2!iq1!im0!ird!ig6>2cs$1>1L$2>1c$0>0@2$5^3^2>0@3$9$0^2@1$7^3@4$6$1^4@2$8^5@2$3$0^3\0$2\0$1$4").
Proof.
  intros cs L c CR Hc. destruct (creach_sim cs L CR) as (st & BL & LS & <- & INV & LIVE).
  rewrite LIVE in Hc. destruct (In_bslot _ _ Hc) as (off & n & Hk).
  apply ptree_ctree_ok.
  eapply (ptree_strel (free_control pans0 pupd0 st (aadd c (UNIT * off)) c tt (INVL_hdr_ok pans0 pupd0 st L BL LS c off n INV Hk))); [intros; exact I|].
  eapply ptree_mono; [intros; exact I|]. exact (ftree_prun pans0 pupd0 pans0_range _ L _ tt (free_INVL_closed st L BL LS c off n INV Hk)).
Qed.
