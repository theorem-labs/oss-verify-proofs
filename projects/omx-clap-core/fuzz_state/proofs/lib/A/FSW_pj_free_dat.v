(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/openssl/ct/lib/CtColB/W_set0A.v, with its module paths and module names changed; 44 of its 60 lines of code are new or changed and 129 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_scene/lib/Prog/SceneTac.v, with its module paths changed; 1051 of its 1066 lines of code are new or changed and 45 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_pcap/lib/U/Prog/pcap_source_open.v, with its module paths and module names changed; 547 of its 622 lines of code are new or changed and 991 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/KindBGlue.v, with its module paths and module names changed; 2130 of its 2257 lines of code are new or changed and 495 lines of the source are left out. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/omx-clap-core/fuzz_state/lib/Prog/CF/pj_free.v, with its module names changed; 185 of its 269 lines of code are new or changed and 2173 lines of the source are left out. *)
(* pj_free's walk (lib/A/FSW_pj_free.v), the data half: lemmas over the reader statements' data predicates
   (lib/Prog/PjStruct.v pj_fd / pf_items / pj_u64, FSH_Fn_reader.v udrop / rd_heads / rd_hblocks / rd_sum) that the walk
   needs between its machine segments. No machine code is read here and no function's contract is proved (rule 24).
   Port-from (bodies copied, not imported, so that no plain-image module enters this ASan file):
   pjf_items_frame / pjf_fd_frame / pjf_items_mono: fs's RELEASED plain proof lib/Prog/pj_free.v:435-504
   (c8557374ad2e pf_items_frame / pf_fd_frame / pf_items_mono), the memory premise restated in PjStruct's
   equality form (PjStruct.pj_hdr_eq / pj_u64_eq, as PjStruct.pj_node_frame states it).
   The PjStruct field -> val_mem bridges are a Theorem Labs lane's kit lib/A/FSW_pj.v (f098a0c2fa8), imported. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI00.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import YI16 YK06 YM05 YG0q.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import
AB1v AB1w FSupoison FSupoisonU FSH_YC20 FSH_Gen FSH_Base FSH_Rt FSPstat FSH_Fn_reader FSW_K FSW_ret FSW_rd FSW_pj.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YO0f YO0d.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Lib Require MState Mem.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require PjStruct.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.
Open Scope Z_scope.

Section p. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Variable segs : list Segment.

(* ---- PjStruct trees across a memory change that keeps their footprint (equality form) ---- *)
Lemma pjf_items_frame : forall m lblk m' lblk' (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  PjStruct.pf_items segs m lblk P ks a ka n D ->
  (forall j D1, (j < n)%nat -> incl D1 D -> P (a + 56 * Z.of_nat j) D1 -> P' (a + 56 * Z.of_nat j) D1) ->
  (ks = true -> forall j x, (j < n)%nat -> PjStruct.pj_u64 segs m (ka + 8 * Z.of_nat j) x ->
     PjStruct.pj_u64 segs m' (ka + 8 * Z.of_nat j) x) ->
  (forall a1 k1, In (a1, k1) D -> lblk' a1 k1) ->
  PjStruct.pf_items segs m' lblk' P' ks a ka n D.
Proof.
  intros m lblk m' lblk' P P' ks n. induction n as [|n IH]; intros a ka D H HP HK HL;
    cbn [PjStruct.pf_items] in H |- *.
  - exact H.
  - destruct H as (Dk & D1 & D2 & -> & Hk & H1 & H2).
    exists Dk, D1, D2. split; [reflexivity|]. split.
    + unfold PjStruct.pj_key in Hk |- *. destruct ks; [|exact Hk].
      destruct Hk as (x & Hx & Hc). exists x. split.
      * pose proof (HK eq_refl 0%nat x ltac:(lia)) as HK0. rewrite Z.add_0_r in HK0. apply HK0. exact Hx.
      * destruct Hc as [Hc|(k & Hl & EDk)]; [left; exact Hc|right]. exists k. split; [|exact EDk].
        apply HL. subst Dk. apply in_or_app. left. left. reflexivity.
    + split.
      * pose proof (HP 0%nat D1 ltac:(lia)) as HP0. rewrite Z.add_0_r in HP0. apply HP0; [|exact H1].
        intros b Hb. apply in_or_app. right. apply in_or_app. left. exact Hb.
      * apply IH; [exact H2 | | | ].
        -- intros j D3 Hj Hs HP3. replace (a + 56 + 56 * Z.of_nat j) with (a + 56 * Z.of_nat (S j)) in * by lia.
           apply HP; [lia | | exact HP3]. intros b Hb. apply in_or_app. right. apply in_or_app. right. apply Hs. exact Hb.
        -- intros Hks j x Hj Hx. replace (ka + 8 + 8 * Z.of_nat j) with (ka + 8 * Z.of_nat (S j)) in * by lia.
           apply (HK Hks (S j)); [lia | exact Hx].
        -- intros a1 k1 Hin. apply HL. apply in_or_app. right. apply in_or_app. right. exact Hin.
Qed.

Lemma pjf_fd_frame : forall d m lblk m' lblk' p D, PjStruct.pj_fd segs m lblk d p D ->
  (forall a k, In (a, k) D -> lblk' a k) ->
  (forall x : word, PjStruct.pj_foot p D (bv_unsigned x) -> m' x = m x) ->
  PjStruct.pj_fd segs m' lblk' d p D.
Proof.
  induction d as [|d IH]; intros m lblk m' lblk' p D H HL HM; cbn [PjStruct.pj_fd] in H |- *;
    destruct H as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HH & HS & HK & HY & HP & HI);
    (split; [exact HND|]); (split; [exact HAP|]);
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di;
    (assert (HD : forall b, In b (Ds ++ Dk ++ Dy ++ Di) -> In b D)
       by (intros b Hb; exact (Permutation_in b (Permutation_sym HP) Hb)));
    (split; [apply (PjStruct.pj_hdr_eq segs m); [exact HH | intros x Hx; apply HM; left; exact Hx]|]);
    (split; [destruct HS as [HS|(k0 & _ & ->)];
      [left; exact HS | right; exists k0; split; [apply HL, HD; left; reflexivity | reflexivity]]|]);
    (split; [destruct HK as [HK|(k0 & _ & Hk & ->)];
      [left; exact HK | right; exists k0; split;
        [apply HL, HD; apply in_or_app; right; left; reflexivity | split; [exact Hk | reflexivity]]]|]);
    (split; [destruct HY as [HY|(Hks & k0 & _ & Hk & ->)];
      [left; exact HY | right; split; [exact Hks|]; exists k0; split;
        [apply HL, HD; apply in_or_app; right; apply in_or_app; right; left; reflexivity
        | split; [exact Hk | reflexivity]]]|]);
    (split; [exact HP|]).
  - exact HI.
  - apply (pjf_items_frame m lblk m' lblk' (PjStruct.pj_fd segs m lblk d) _ ks _ kids keys Di HI).
    + intros j D1 Hj Hs HP1. apply (IH m lblk m' lblk' _ D1 HP1).
      * intros a k0 Hin. apply HL, HD. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
        apply Hs. exact Hin.
      * intros x Hx. apply HM. right. destruct Hx as [Hx|(b & Hb & Hx)].
        -- destruct HK as [(_ & En & _)|(k0 & _ & Hk & EDk)]; [rewrite En in Hj; cbn in Hj; lia|].
           exists (kids, k0). split; [apply HD; apply in_or_app; right; rewrite EDk; left; reflexivity|].
           unfold PjStruct.pj_holds; cbn [fst snd]. lia.
        -- exists b. split; [|exact Hx]. apply HD. apply in_or_app; right; apply in_or_app; right; apply in_or_app.
           right. apply Hs. exact Hb.
    + intros Hks j x Hj Hx. apply (PjStruct.pj_u64_eq segs m); [exact Hx|]. intros y Hy. apply HM. right.
      destruct HY as [(_ & Hf & _)|(_ & k0 & _ & Hk & EDy)]; [congruence|].
      exists (keys, k0).
      split; [apply HD; apply in_or_app; right; apply in_or_app; right; rewrite EDy; left; reflexivity|].
      unfold PjStruct.pj_holds; cbn [fst snd]. lia.
    + intros a1 k1 Hin. apply HL, HD. apply in_or_app; right; apply in_or_app; right; apply in_or_app; right.
      exact Hin.
Qed.

Lemma pjf_items_mono : forall m lblk (P P' : Z -> list (Z * Z) -> Prop) ks n a ka D,
  (forall a1 D1, P a1 D1 -> P' a1 D1) ->
  PjStruct.pf_items segs m lblk P ks a ka n D -> PjStruct.pf_items segs m lblk P' ks a ka n D.
Proof.
  intros m lblk P P' ks n. induction n as [|n IH]; intros a ka D HPP H; cbn [PjStruct.pf_items] in *; [exact H|].
  destruct H as (Dk & D1 & D2 & E & HK & H1 & H2). exists Dk, D1, D2.
  split; [exact E|]. split; [exact HK|]. split; [exact (HPP _ _ H1) | exact (IH _ _ _ HPP H2)].
Qed.

(* the kids of a node freeable at depth d, as one shape: freeable at a depth below d *)
Definition pjf_Pd (m : word -> option byte) (lblk : Z -> Z -> Prop) (d : nat) (a : Z) (D1 : list (Z * Z)) : Prop :=
  exists d', d = S d' /\ PjStruct.pj_fd segs m lblk d' a D1.
Lemma pjf_fd_items : forall m lblk d p D, PjStruct.pj_fd segs m lblk d p D ->
  PjStruct.pj_fshape segs m lblk
    (fun ks kids keys n Di => PjStruct.pf_items segs m lblk (pjf_Pd m lblk d) ks kids keys (Z.to_nat n) Di) p D.
Proof.
  intros m lblk d p D H. destruct d as [|d]; cbn [PjStruct.pj_fd] in H.
  - destruct H as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HH & HS & HK & HY & HP
      & (En & EDi)).
    split; [exact HND|]. split; [exact HAP|].
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
    repeat (split; [eassumption|]). rewrite En, EDi. reflexivity.
  - destruct H as (HND & HAP & ty & num & str & kids & keys & n & cap & ks & Ds & Dk & Dy & Di & HH & HS & HK & HY & HP
      & HI).
    split; [exact HND|]. split; [exact HAP|].
    exists ty, num, str, kids, keys, n, cap, ks, Ds, Dk, Dy, Di.
    repeat (split; [eassumption|]).
    apply (pjf_items_mono m lblk (PjStruct.pj_fd segs m lblk d)); [|exact HI].
    intros a1 D1 H1. exists d. split; [reflexivity | exact H1].
Qed.
End p.

(* ---- list algebra of the freed blocks ---- *)
Lemma pjf_hd_in_iff : forall H (h : Z * Z), hd_in H h = true <-> In h H.
Proof.
  intros H h. unfold hd_in. rewrite existsb_exists. split.
  - intros ((a, b) & Hin & E). apply andb_true_iff in E as [E1 E2]. apply Z.eqb_eq in E1, E2.
    destruct h as [x y]. cbn [fst snd] in *. subst. exact Hin.
  - intros Hin. exists h. split; [exact Hin|]. rewrite !Z.eqb_refl. reflexivity.
Qed.
Lemma pjf_hd_in_perm : forall A A' h, Permutation A A' -> hd_in A h = hd_in A' h.
Proof.
  intros A A' h HP. destruct (hd_in A h) eqn:E1, (hd_in A' h) eqn:E2; try reflexivity.
  - apply pjf_hd_in_iff in E1. apply (Permutation_in h HP) in E1. apply pjf_hd_in_iff in E1. congruence.
  - apply pjf_hd_in_iff in E2. apply (Permutation_in h (Permutation_sym HP)) in E2. apply pjf_hd_in_iff in E2. congruence.
Qed.
Lemma pjf_hd_in_app : forall A B h, hd_in (A ++ B) h = hd_in A h || hd_in B h.
Proof. intros A B h. unfold hd_in. apply existsb_app. Qed.
(* udrop is stdpp's list filter (FSH_Fn_reader.v's scope); the lemmas below go through Stdlib's List.filter *)
Lemma pjf_udrop_eq : forall U H, udrop U H = List.filter (fun h => negb (hd_in H h)) U.
Proof.
  intros U H. unfold udrop. induction U as [|a U IH]; [reflexivity|].
  cbn [List.filter]. destruct (negb (hd_in H a)) eqn:E.
  - rewrite list_basics.list.filter_cons_True by (cbv beta; rewrite E; exact I). rewrite IH. reflexivity.
  - rewrite list_basics.list.filter_cons_False by (cbv beta; rewrite E; intros []). rewrite IH. reflexivity.
Qed.
Lemma pjf_filter_all : forall {X} (f : X -> bool) l, (forall x, In x l -> f x = true) -> List.filter f l = l.
Proof.
  intros X f l. induction l as [|x l IH]; intros H; [reflexivity|]. cbn [List.filter].
  rewrite (H x (or_introl eq_refl)). rewrite IH; [reflexivity|]. intros y Hy. apply H. right. exact Hy.
Qed.
Lemma pjf_filter_filter : forall {X} (f g : X -> bool) l,
  List.filter f (List.filter g l) = List.filter (fun x => g x && f x) l.
Proof.
  intros X f g l. induction l as [|x l IH]; [reflexivity|]. cbn [List.filter].
  destruct (g x); cbn [List.filter andb]; [destruct (f x); cbn [List.filter]; rewrite IH; reflexivity | exact IH].
Qed.
Lemma pjf_udrop_nil : forall U, udrop U [] = U.
Proof. intros U. rewrite pjf_udrop_eq. apply pjf_filter_all. intros h _. reflexivity. Qed.
Lemma pjf_udrop_app : forall U A B, udrop (udrop U A) B = udrop U (A ++ B).
Proof.
  intros U A B. rewrite !pjf_udrop_eq. rewrite pjf_filter_filter. apply List.filter_ext. intros h.
  rewrite pjf_hd_in_app. destruct (hd_in A h), (hd_in B h); reflexivity.
Qed.
Lemma pjf_udrop_perm : forall U A A', Permutation A A' -> udrop U A = udrop U A'.
Proof.
  intros U A A' HP. rewrite !pjf_udrop_eq. apply List.filter_ext. intros h. rewrite (pjf_hd_in_perm A A' h HP).
  reflexivity.
Qed.
Lemma pjf_filter_skip : forall {X} (f : X -> bool) l1 x l2, f x = false ->
  List.filter f (l1 ++ x :: l2) = List.filter f (l1 ++ l2).
Proof. intros X f l1 x l2 H. rewrite !List.filter_app. cbn [List.filter]. rewrite H. reflexivity. Qed.
Lemma pjf_udrop_one : forall U1 U2 h, ~ In h (U1 ++ U2) -> udrop (U1 ++ h :: U2) [h] = U1 ++ U2.
Proof.
  intros U1 U2 h Hn. rewrite pjf_udrop_eq.
  rewrite pjf_filter_skip by (cbv beta; rewrite (proj2 (pjf_hd_in_iff [h] h) (or_introl eq_refl)); reflexivity).
  apply pjf_filter_all. intros g Hg. cbv beta.
  destruct (hd_in [h] g) eqn:E; [|reflexivity]. apply pjf_hd_in_iff in E. destruct E as [E|[]]. subst g. contradiction.
Qed.
Lemma pjf_pairwise_dup : forall {X} (R : X -> X -> Prop) l1 h l2, pairwise R (l1 ++ h :: l2) -> In h (l1 ++ l2) -> R h h.
Proof.
  intros X R l1. induction l1 as [|x l1 IH]; intros h l2 HP Hin; cbn [app pairwise] in *.
  - destruct HP as (HF & _). rewrite Forall_forall in HF. exact (HF h Hin).
  - destruct HP as (HF & HP). destruct Hin as [<-|Hin].
    + rewrite Forall_forall in HF. apply HF. apply in_or_app. right. left. reflexivity.
    + exact (IH h l2 HP Hin).
Qed.
(* a head appears once in U (upoison_ok's ranges are pairwise disjoint and nonempty) *)
Lemma pjf_head_once : forall B ly S U1 h U2, upoison_ok B ly S (U1 ++ h :: U2) -> 0 < snd h -> ~ In h (U1 ++ U2).
Proof.
  intros B ly S U1 h U2 (_ & HP) Hs Hin. pose proof (pjf_pairwise_dup _ U1 h U2 HP Hin) as Hd.
  unfold zdisjoint in Hd. lia.
Qed.
Lemma pjf_rd_sum_cons : forall b A, rd_sum (b :: A) = snd b + rd_sum A.
Proof. reflexivity. Qed.
Lemma pjf_rd_sum_app : forall A B, rd_sum (A ++ B) = rd_sum A + rd_sum B.
Proof.
  intros A B. induction A as [|a A IH]; [reflexivity|]. rewrite <- app_comm_cons, !pjf_rd_sum_cons, IH. lia.
Qed.
Lemma pjf_rd_sum_perm : forall A A', Permutation A A' -> rd_sum A = rd_sum A'.
Proof. intros A A' HP. induction HP; rewrite ?pjf_rd_sum_cons; lia. Qed.
Lemma pjf_rd_hblocks_app : forall A B, rd_hblocks (A ++ B) = rd_hblocks A ++ rd_hblocks B.
Proof. intros A B. unfold rd_hblocks. apply map_app. Qed.
Lemma pjf_rd_heads_app : forall A B, rd_heads (A ++ B) = rd_heads A ++ rd_heads B.
Proof. intros A B. unfold rd_heads. apply map_app. Qed.
Lemma pjf_EV_app : forall A B, EV_pj_free (A ++ B) = EV_pj_free A + EV_pj_free B.
Proof. intros A B. unfold EV_pj_free, EV_fuzz_free. rewrite length_app. lia. Qed.
Lemma pjf_EV_perm : forall A A', Permutation A A' -> EV_pj_free A = EV_pj_free A'.
Proof. intros A A' HP. unfold EV_pj_free. rewrite (Permutation_length HP). reflexivity. Qed.
Lemma pjf_perm_free1 : forall (A X l1 l2 : list (Z * Z)) hb,
  Permutation A (X ++ l1 ++ hb :: l2) -> Permutation A ((X ++ [hb]) ++ l1 ++ l2).
Proof.
  intros A X l1 l2 hb HP. rewrite HP. rewrite <- app_assoc. apply Permutation_app_head. cbn [app].
  symmetry. apply Permutation_middle.
Qed.

(* ---- journal footprints ---- *)
Lemma pjf_inFP_cons : forall r l a, inFP (r :: l) a <-> (fst r <= a < snd r) \/ inFP l a.
Proof.
  intros r l a. split.
  - intros (r' & [<-|Hin] & H); [left; exact H | right; exists r'; auto].
  - intros [H|(r' & Hin & H)]; [exists r; split; [left; reflexivity | exact H] | exists r'; split; [right; exact Hin | exact H]].
Qed.
Lemma pjf_inFP_app : forall l1 l2 a, inFP (l1 ++ l2) a <-> inFP l1 a \/ inFP l2 a.
Proof.
  intros l1 l2 a. split.
  - intros (r & Hin & H). apply in_app_or in Hin as [Hin|Hin]; [left | right]; exists r; auto.
  - intros [(r & Hin & H)|(r & Hin & H)]; exists r; split; try exact H; apply in_or_app; [left | right]; exact Hin.
Qed.
Lemma pjf_inFP_ablocks : forall bl a, inFP (ablocks_fp bl) a <-> exists p n, In (p, n) bl /\ p <= a < p + req_size n.
Proof.
  intros bl a. unfold ablocks_fp. split.
  - intros (r & Hin & H). apply in_map_iff in Hin as ((p, n) & <- & Hin). cbn [fst snd] in H. exists p, n. auto.
  - intros (p & n & Hin & H). exists (p, p + req_size n). split; [|cbn [fst snd]; lia].
    apply in_map_iff. exists (p, n). auto.
Qed.
Lemma pjf_inFP_hblocks : forall D a, inFP (ablocks_fp (rd_hblocks D)) a <->
  exists p k, In (p, k) D /\ p - HEAD <= a < p - HEAD + req_size (k + HEAD).
Proof.
  intros D a. rewrite pjf_inFP_ablocks. unfold rd_hblocks. split.
  - intros (p & n & Hin & H). apply in_map_iff in Hin as ((q, k) & E & Hin). cbn [fst snd] in E.
    injection E as <- <-. exists q, k. auto.
  - intros (p & k & Hin & H). exists (p - HEAD), (k + HEAD). split; [|exact H].
    apply in_map_iff. exists (p, k). auto.
Qed.

Section e. Context {fx : YK11.FPState} {rc : YM05.RunCeil} {SK : YI16.sink_head}.
Variable B : asyms.
Let LAWS : AR_laws tfibsegs B := AR_laws_ok tfibsegs B.

Lemma pjf_aview_of_raw : forall (H H' : word -> bool) (m m' : word -> option byte) a,
  mrestrict H' m' (Z_to_bv 64 a) = mrestrict H m (Z_to_bv 64 a) -> aview tfibsegs H' m' a = aview tfibsegs H m a.
Proof. intros H H' m m' a E. unfold aview, mbyte. rewrite E. reflexivity. Qed.
Lemma pjf_val_mem_eq : forall (m m' : word -> option byte) a (n : nat) v,
  (forall k, (k < n)%nat -> m' (Z_to_bv 64 (a + Z.of_nat k)) = m (Z_to_bv 64 (a + Z.of_nat k))) ->
  val_mem tfibsegs m a n v -> val_mem tfibsegs m' a n v.
Proof. intros m m' a n v E Hv k Hk. unfold mbyte. rewrite (E k Hk). exact (Hv k Hk). Qed.

(* the image covers fuzz/alloc.c's statics *)
Lemma pjf_img_cover : forall lo hi,
  existsb (fun sg => (Z.of_N (seg_base sg) <=? lo) && (hi <=? Z.of_N (seg_base sg) + Z.of_N (seg_size sg))) tfibsegs = true ->
  forall a, lo <= a < hi -> in_img tfibsegs a.
Proof.
  intros lo hi H a Ha. apply existsb_exists in H as (sg & Hin & E). apply andb_true_iff in E as [E1 E2].
  apply Z.leb_le in E1, E2. exists sg. split; [exact Hin | lia].
Qed.
Lemma pjf_pstat_img : forall a, inFP FS_PSTAT_FP a -> in_img tfibsegs a.
Proof.
  intros a (r & Hin & Ha). unfold FS_PSTAT_FP in Hin.
  destruct Hin as [<-|[<-|[<-|[<-|[]]]]]; cbn [fst snd] in Ha;
    [apply (pjf_img_cover 0xa3ca0 0xa3ca8) | apply (pjf_img_cover 0x5da5c0 0x5da5c8)
    | apply (pjf_img_cover 0x5da5e0 0x5da5e8) | apply (pjf_img_cover 0x5da600 0x5da608)];
    (try exact Ha); vm_compute; reflexivity.
Qed.

End e.
