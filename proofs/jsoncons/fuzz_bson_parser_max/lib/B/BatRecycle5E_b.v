(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require BvWfKernel.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.jsoncons.fuzz_bson_parser_max.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import PropExec CatExec CatSim SeqExec StepTac StoreOk Hoare WalkTac MmapSim As0StepLib As0Tables
     ArtMem ArtRegs ArtAtomics ArtAtomics2 ArtTac ArtFxTac. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatLeaf_b BatAllocG_b BatPoison_b. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib Require Import ArtRuns ArtRunsMem. From OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.B Require Import BatFp_b BatFxQ_b BatRecycle5R_b.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLia. Require OssFuzzTheorems.Proofs.jsoncons.fuzz_bson_parser_max.lib.L5FastLiaT. Local Ltac lia := L5FastLiaT.plia1.
Open Scope Z_scope.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation ASEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation cellA := (cell AsanUbsan.M.loaded_segments).
#[local] Abbreviation wrA := (wr AsanUbsan.M.loaded_segments).
#[local] Notation "'U' r" := (bv_unsigned r) (at level 10, r at level 9).

Fixpoint art_rcy_npop (mn : Z) (bs : list art_qbatch) : nat :=
  match bs with [] => O | b :: r => if mn <? art_qbytes (b :: r) then S (art_rcy_npop mn r) else O end.

Definition art_qlast (bs : list art_qbatch) : Z := match bs with [] => 0 | _ => qb_addr (last bs (0, [], 0)) end.
(* [comment removed for export] *)
Definition art_qin (HI : Z) (b : art_qbatch) : Prop := 0x696000 <= qb_addr b /\ qb_addr b + 8192 <= HI /\ 0 <= qb_size b < 2 ^ 64.

Lemma art_qlast_snoc : forall pp b, art_qlast (pp ++ [b]) = qb_addr b.
Proof. intros pp b. unfold art_qlast. destruct (pp ++ [b]) eqn:E; [destruct pp; discriminate|]. rewrite <- E. rewrite last_last. reflexivity. Qed.
Lemma art_qhead_app : forall pp r, pp <> [] -> art_qhead (pp ++ r) = art_qhead pp.
Proof. intros [|p pp] r H; [contradiction|reflexivity]. Qed.
Lemma art_qbytes_cons : forall b r, art_qbytes (b :: r) = qb_size b + art_qbytes r.
Proof. reflexivity. Qed.

(* [comment removed for export] *)
Lemma art_qlist_snoc_pop : forall (M M' : word -> option byte) HI tmp pp b,
  art_agree [(0x13c8b0 + 160, 32); (qb_addr b, 8); (tmp, 32); (art_qlast pp, if Z.of_nat (length pp) =? 0 then 0 else 8)] M M' ->
  art_qsep (pp ++ [b]) -> Forall (art_qin HI) (pp ++ [b]) -> 0x696000 <= HI -> HI <= tmp -> tmp + 32 < 2 ^ 64 ->
  art_qlist M pp (art_qhead pp) (art_qlast pp) -> art_qrec M b ->
  (pp <> [] -> cellA M' (art_qlast pp) 8 (qb_addr b)) -> cellA M' (qb_addr b) 8 0 ->
  art_qlist M' (pp ++ [b]) (art_qhead (pp ++ [b])) (qb_addr b).
Proof.
  intros M M' HI tmp pp b AG SEP IN HHI Htmp Htmp' QL QR Cl Cb.
  assert (Hb : art_qin HI b) by (apply Forall_app in IN; destruct IN as [_ X]; exact (Forall_inv X)).
  destruct Hb as (Hb0 & Hb1 & _).
  (* [comment removed for export] *)
  assert (TR : forall p, art_qin HI p -> (p = b \/ apart (qb_addr p) 8192 (qb_addr b) 8192) -> (qb_addr p = art_qlast pp \/ apart (qb_addr p) 8192 (art_qlast pp) 8 \/ pp = []) -> art_qrec M p -> art_qrec M' p).
  { intros p (P0 & P1 & _) Hpb Hpl (L & C1 & C2 & CI). unfold art_qrec.
    assert (T : forall a (k : nat) v, qb_addr p + 8 <= a -> a + Z.of_nat k <= qb_addr p + 8192 -> cellA M a k v -> cellA M' a k v).
    { intros a k v Ha Hk C. apply (art_cell_tr _ M M' a k v AG); [|lia|lia|exact C]. cbn [art_gap fst snd]. unfold apart in *.
      split; [lia|]. split; [destruct Hpb as [->|X]; lia|]. split; [lia|]. split; [|exact I].
      destruct pp as [|p0 pp0]; [right; unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
      destruct Hpl as [X|[X|X]]; [lia|lia|discriminate X]. }
    split; [exact L|]. split; [apply T; [lia|cbn; lia|exact C1]|]. split; [apply T; [lia|cbn; lia|exact C2]|].
    intros j it Hj. assert (Hjl : (j < length (qb_items p))%nat) by (apply nth_error_Some; congruence). apply T; [lia|cbn; lia|exact (CI j it Hj)]. }
  assert (TL : forall p v, art_qin HI p -> apart (qb_addr p) 8192 (qb_addr b) 8192 -> apart (qb_addr p) 8192 (art_qlast pp) 8 -> pp <> [] -> cellA M (qb_addr p) 8 v -> cellA M' (qb_addr p) 8 v).
  { intros p v (P0 & P1 & _) Apb Apl Hne C. apply (art_cell_tr _ M M' _ _ _ AG); [|lia|cbn; lia|exact C]. cbn [art_gap fst snd]. unfold apart in *.
    destruct pp as [|p0 pp0]; [contradiction|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
    change (Z.of_nat 8) with 8. repeat split; try exact I; lia. }
  destruct pp as [|p0 pp0].
  - cbn [app art_qhead art_qlist]. split; [reflexivity|]. split; [apply TR; [apply (Forall_inv IN)|left; reflexivity|right; right; reflexivity|exact QR]|]. split; [reflexivity|]. split; [exact Cb|reflexivity].
  - set (pp := p0 :: pp0) in *. assert (Hpp : pp <> []) by discriminate.
    assert (INNER : forall s, s <> [] -> (forall p, In p s -> In p pp) -> qb_addr (last s (0, [], 0)) = art_qlast pp -> art_qsep (s ++ [b]) ->
                      art_qlist M s (art_qhead s) (art_qlast pp) -> art_qlist M' (s ++ [b]) (art_qhead s) (qb_addr b)).
    { induction s as [|p r IHs]; [contradiction|]. intros _ Hsub Hlast SEPs QLs.
      assert (Hpin : art_qin HI p). { apply Forall_app in IN. destruct IN as [X _]. exact (proj1 (Forall_forall _ _) X p (Hsub p (or_introl eq_refl))). }
      destruct QLs as (_ & QRp & _ & Cn & QLr). cbn [app art_qsep] in SEPs. destruct SEPs as (_ & _ & Fp & SEPr).
      assert (Apb : apart (qb_addr p) 8192 (qb_addr b) 8192). { apply (proj1 (Forall_forall _ _) Fp b). apply in_or_app. right. left. reflexivity. }
      destruct r as [|p2 r2].
      - cbn [last] in Hlast. cbn [app art_qlist art_qhead]. split; [reflexivity|]. split; [apply TR; [exact Hpin|right; exact Apb|left; exact Hlast|exact QRp]|]. split; [exact I|].
        split; [rewrite Hlast; apply Cl; exact Hpp|]. split; [reflexivity|].
        split; [apply TR; [apply Forall_app in IN; destruct IN as [_ X]; exact (Forall_inv X)|left; reflexivity|right; left|exact QR]|].
        { destruct Hpin as (Q0 & Q1 & _). rewrite <- Hlast. unfold apart in *. lia. }
        split; [reflexivity|]. split; [exact Cb|reflexivity].
      - assert (Hl2 : In (last (p2 :: r2) (0, [], 0)) (p2 :: r2)) by (apply exists_last in Hpp; destruct (exists_last (l := p2 :: r2) ltac:(discriminate)) as (l' & a' & E); rewrite E, last_last; apply in_or_app; right; left; reflexivity).
        assert (Apl : apart (qb_addr p) 8192 (art_qlast pp) 8).
        { rewrite <- Hlast. change (last (p :: p2 :: r2) (0, [], 0)) with (last (p2 :: r2) (0, [], 0)).
          pose proof (proj1 (Forall_forall _ _) Fp _ (in_or_app _ _ _ (or_introl Hl2))) as X. unfold apart in *. lia. }
        change ((p :: p2 :: r2) ++ [b]) with (p :: (p2 :: r2) ++ [b]). cbn [art_qlist art_qhead]. split; [reflexivity|].
        split; [apply TR; [exact Hpin|right; exact Apb|right; left; exact Apl|exact QRp]|]. split; [exact I|].
        split; [change (art_qhead ((p2 :: r2) ++ [b])) with (qb_addr p2); apply TL; [exact Hpin|exact Apb|exact Apl|exact Hpp|exact Cn]|].
        apply IHs; [discriminate|intros q Hq; apply Hsub; right; exact Hq|exact Hlast|exact SEPr|exact QLr]. }
    rewrite (art_qhead_app pp [b] Hpp). apply INNER; [exact Hpp|tauto|reflexivity|exact SEP|exact QL].
Qed.


(* [comment removed for export] *)
Lemma art_qsep_mid : forall l1 x l2, art_qsep (l1 ++ x :: l2) ->
  art_qsep (l1 ++ [x]) /\ Forall (fun p => apart (qb_addr p) 8192 (qb_addr x) 8192) l1 /\ Forall (fun r => apart (qb_addr x) 8192 (qb_addr r) 8192) l2
  /\ Forall (fun p => Forall (fun r => apart (qb_addr p) 8192 (qb_addr r) 8192) l2) l1.
Proof.
  induction l1 as [|p l1 IH]; intros x l2 S; cbn [app art_qsep] in *.
  - destruct S as (S0 & S1 & SF & SR). repeat split; try assumption; constructor.
  - destruct S as (S0 & S1 & SF & SR). destruct (IH x l2 SR) as (A & B & C & D). apply Forall_app in SF. destruct SF as [SF1 SF2].
    pose proof (Forall_inv SF2) as Fx. pose proof (Forall_inv_tail SF2) as Fl2.
    split; [split; [exact S0|split; [exact S1|split; [apply Forall_app; split; [exact SF1|constructor; [exact Fx|constructor]]|exact A]]]|].
    split; [constructor; assumption|]. split; [exact C|constructor; assumption].
Qed.

Lemma art_qbytes_nonneg : forall HI l, Forall (art_qin HI) l -> 0 <= art_qbytes l.
Proof. induction l as [|b r IH]; intros F; [cbn; lia|]. rewrite art_qbytes_cons. pose proof (Forall_inv F) as (_ & _ & Hs). pose proof (IH (Forall_inv_tail F)). lia. Qed.

Lemma art_out_links : forall (l : list art_qbatch) x z, art_out (map (fun b => (qb_addr b, 8)) l) z -> In x l -> ~ (qb_addr x <= z < qb_addr x + 8).
Proof.
  induction l as [|b r IH]; intros x z O Hin; [destruct Hin|]. cbn [map art_out fst snd] in O. destruct O as [O1 O2].
  destruct Hin as [->|Hin]; [exact O1|exact (IH x z O2 Hin)].
Qed.

Lemma art_qlast_in : forall pp, pp <> [] -> exists p, In p pp /\ art_qlast pp = qb_addr p.
Proof.
  intros pp H. destruct (exists_last H) as (l' & a & E). exists a. split; [rewrite E; apply in_or_app; right; left; reflexivity|].
  unfold art_qlast. destruct pp; [contradiction|]. rewrite E, last_last. reflexivity.
Qed.

Section FPX. Context {fx : PropExec.FPState}.

#[using="Type"] Lemma art_rcy_deq_run : forall (rr pp : list art_qbatch) regs (M rom : word -> option byte) (HI tmp mn GL tf : Z),
  getr regs 2 = Z_to_bv 64 tmp -> getr regs 10 = Z_to_bv 64 0x13c8b0 -> getr regs 11 = Z_to_bv 64 mn ->
  getr regs 14 = Z_to_bv 64 (Z.of_nat (length pp)) -> getr regs 15 = Z_to_bv 64 (art_qlast pp) -> getr regs 16 = Z_to_bv 64 (Z.of_nat (length rr)) -> getr regs 5 = Z_to_bv 64 (art_qhead rr) ->
  0 <= mn < art_qbytes rr -> art_qsep (pp ++ rr) -> Forall (art_qin HI) (pp ++ rr) -> 0x696000 <= HI -> HI <= tmp -> tmp + 32 < 2 ^ 64 ->
  Z.of_nat (length (pp ++ rr)) < 2 ^ 40 -> art_qbytes (pp ++ rr) < 2 ^ 63 ->
  wrA M tmp 32 -> wrA M (0x13c8b0 + 160) 32 -> Forall (fun b => wrA M (qb_addr b) 8) (pp ++ rr) ->
  cellA M (0x13c8b0 + 184) 8 (art_qbytes rr) -> cellA M (0x13c8b0 + 176) 8 GL -> cellA M (tmp + 24) 8 (art_qbytes pp) -> cellA M (tmp + 8) 8 tf -> (pp <> [] -> tf = art_qhead pp) ->
  art_qlist M pp (art_qhead pp) (art_qlast pp) -> art_qlist M rr (art_qhead rr) GL ->
  exists regs' (M' : word -> option byte),
    msteps ASEGS (mkst regs (0x54550 : word) M rom) (mkst regs' (0x545a4 : word) M' rom)
    /\ getr regs' 14 = Z_to_bv 64 (Z.of_nat (length (pp ++ firstn (art_rcy_npop mn rr) rr))) /\ getr regs' 6 = Z_to_bv 64 (art_qlast (pp ++ firstn (art_rcy_npop mn rr) rr))
    /\ (forall r : reg, In r [1; 2; 3; 4; 8; 9; 10; 11; 12; 13; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv -> getr regs' r = getr regs r)
    /\ mem_grows M M'
    /\ art_agree ([(0x13c8b0 + 160, 32); (tmp, 32)] ++ map (fun b => (qb_addr b, 8)) (pp ++ rr)) M M'
    /\ cellA M' (0x13c8b0 + 160) 8 (Z.of_nat (length (skipn (art_rcy_npop mn rr) rr))) /\ cellA M' (0x13c8b0 + 168) 8 (art_qhead (skipn (art_rcy_npop mn rr) rr))
    /\ cellA M' (0x13c8b0 + 184) 8 (art_qbytes (skipn (art_rcy_npop mn rr) rr))
    /\ (skipn (art_rcy_npop mn rr) rr = [] -> cellA M' (0x13c8b0 + 176) 8 0) /\ (skipn (art_rcy_npop mn rr) rr <> [] -> cellA M' (0x13c8b0 + 176) 8 GL)
    /\ cellA M' (tmp + 8) 8 (art_qhead (pp ++ firstn (art_rcy_npop mn rr) rr)) /\ cellA M' (tmp + 24) 8 (art_qbytes (pp ++ firstn (art_rcy_npop mn rr) rr))
    /\ art_qlist M' (pp ++ firstn (art_rcy_npop mn rr) rr) (art_qhead (pp ++ firstn (art_rcy_npop mn rr) rr)) (art_qlast (pp ++ firstn (art_rcy_npop mn rr) rr))
    /\ art_qlist M' (skipn (art_rcy_npop mn rr) rr) (art_qhead (skipn (art_rcy_npop mn rr) rr)) GL
    /\ art_qbytes (skipn (art_rcy_npop mn rr) rr) <= mn /\ (1 <= art_rcy_npop mn rr)%nat.
Proof.
  induction rr as [|b rr' IH]; intros pp regs M rom HI tmp mn GL tf H2 H10 H11 H14 H15 H16 H5 Hmn SEP IN HHI Htmp Htmp' Hlen Hqb Wt Wq Wl Cgb Cgl Ctb Ctf Etf QLp QLr;
    [cbn in Hmn; lia|].
  destruct (art_qsep_mid pp b rr' SEP) as (SEPb & Fpb & Fbr & Fpr).
  pose proof (proj1 (Forall_app _ _ _) IN) as [INp INr]. pose proof (Forall_inv INr) as (Hb0 & Hb1 & Hbs). pose proof (Forall_inv_tail INr) as INr'.
  pose proof (art_qbytes_nonneg HI _ INp) as Hqp. pose proof (art_qbytes_nonneg HI _ INr') as Hqr'.
  rewrite art_qbytes_app, art_qbytes_cons in Hqb. rewrite art_qbytes_cons in Hmn, Cgb. rewrite length_app in Hlen. cbn [length] in Hlen, H16.
  destruct QLr as (_ & QRb & _ & Cnx & QLr'). pose proof QRb as (_ & _ & Csz & _).
  assert (Hnext : 0 <= art_qhead rr' < 2 ^ 64). { destruct rr' as [|b2 rr2]; cbn [art_qhead]; [lia|]. pose proof (Forall_inv INr') as (X0 & X1 & _). lia. }
  assert (Hpl : Z.of_nat (length pp) <> 0 -> 0x696000 <= art_qlast pp /\ art_qlast pp + 8 < 2 ^ 64 /\ apart (art_qlast pp) 8 (qb_addr b) 8192 /\ apart (art_qlast pp) 8 tmp 32 /\ wrA M (art_qlast pp) 8).
  { intros Hn0. assert (Hpp : pp <> []) by (intros ->; cbn in Hn0; lia). destruct (art_qlast_in pp Hpp) as (p & Hp & ->).
    pose proof (proj1 (Forall_forall _ _) INp p Hp) as (P0 & P1 & _). pose proof (proj1 (Forall_forall _ _) Fpb p Hp) as Ap.
    pose proof (proj1 (Forall_forall _ _) Wl p (in_or_app _ _ _ (or_introl Hp))) as Wp. unfold apart in *. repeat split; try lia; exact Wp. }
  destruct (art_rcy_pop regs M rom tmp (Z.of_nat (length pp)) (art_qlast pp) (Z.of_nat (S (length rr'))) (qb_addr b) (art_qhead rr') (qb_size b) (qb_size b + art_qbytes rr') GL (art_qbytes pp) tf
              H10 H14 H15 H16 H5 H2 ltac:(lia) Htmp' Hb0 ltac:(lia) ltac:(unfold apart; lia) ltac:(lia) ltac:(lia) Hnext Hbs ltac:(lia) ltac:(lia) Hpl Wt Wq
              (proj1 (Forall_forall _ _) Wl b (in_or_app pp (b :: rr') b (or_intror (or_introl eq_refl)))) Cnx Csz Cgb Cgl Ctb Ctf)
    as (r1 & M1 & RUN1 & A14 & A15 & A5 & A7 & A16 & A6 & AK & GW1 & AG1 & Cf1 & Cc1 & Cb1 & Cbz1 & Cl0 & Cl1 & Ct0 & Ct1 & Ctb1).
  replace (qb_size b + art_qbytes rr' - qb_size b) with (art_qbytes rr') in A7, Cb1 by lia.
  replace (Z.of_nat (S (length rr')) - 1) with (Z.of_nat (length rr')) in A16, Cc1 by lia.
  (* [comment removed for export] *)
  assert (QLp1 : art_qlist M1 (pp ++ [b]) (art_qhead (pp ++ [b])) (qb_addr b)).
  { apply (art_qlist_snoc_pop M M1 HI tmp pp b AG1 SEPb ltac:(apply Forall_app; split; [exact INp|constructor; [exact (Forall_inv INr)|constructor]]) HHI Htmp Htmp' QLp QRb); [|exact Cbz1].
    intros Hpp. apply Ct1. intros X. destruct pp; [contradiction|cbn in X; lia]. }
  assert (QLr1 : art_qlist M1 rr' (art_qhead rr') GL).
  { apply (art_qlist_tr _ M M1 rr' _ _ AG1); [|exact QLr']. apply Forall_forall. intros r Hr. pose proof (proj1 (Forall_forall _ _) INr' r Hr) as (R0 & R1 & _).
    pose proof (proj1 (Forall_forall _ _) Fbr r Hr) as Abr. split; [lia|]. split; [lia|]. cbn [art_gap fst snd]. unfold apart in *. repeat split; try exact I; try lia.
    destruct pp as [|p0 pp0]; [right; unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
    destruct (art_qlast_in (p0 :: pp0) ltac:(discriminate)) as (p & Hp & ->). pose proof (proj1 (Forall_forall _ _) (proj1 (Forall_forall _ _) Fpr p Hp) r Hr) as Apr.
    pose proof (proj1 (Forall_forall _ _) INp p Hp) as (P0 & P1 & _). unfold apart in Apr. lia. }
  assert (Ctf1 : cellA M1 (tmp + 8) 8 (art_qhead (pp ++ [b]))).
  { destruct pp as [|p0 pp0]; [apply Ct0; reflexivity|]. rewrite art_qhead_app by discriminate. rewrite <- (Etf ltac:(discriminate)). apply Ct1. cbn [length]. lia. }
  assert (AG1' : art_agree ([(0x13c8b0 + 160, 32); (tmp, 32)] ++ map (fun b0 => (qb_addr b0, 8)) (pp ++ b :: rr')) M M1).
  { eapply art_agree_sub; [exact AG1|]. intros z Hz H. apply art_out_app in H. destruct H as [H1 H2'].
    cbn [art_out fst snd] in H1 |- *. split; [tauto|]. split; [exact (art_out_links _ b z H2' (in_or_app pp (b :: rr') b (or_intror (or_introl eq_refl))))|]. split; [tauto|]. split; [|exact I].
    destruct pp as [|p0 pp0]; [unfold art_qlast; change (Z.of_nat (length (@nil art_qbatch)) =? 0) with true; cbv iota; lia|]. replace (Z.of_nat (length (p0 :: pp0)) =? 0) with false by (symmetry; apply Z.eqb_neq; cbn [length]; lia).
    destruct (art_qlast_in (p0 :: pp0) ltac:(discriminate)) as (p & Hp & ->). exact (art_out_links _ p z H2' (in_or_app _ _ _ (or_introl Hp))). }
  cbn [art_rcy_npop]. rewrite art_qbytes_cons. replace (mn <? qb_size b + art_qbytes rr') with true by (symmetry; apply Z.ltb_lt; lia).
  destruct (Z_lt_le_dec mn (art_qbytes rr')) as [More|Done].
  - (* [comment removed for export] *)
    destruct (art_rcy_more r1 M1 rom mn (art_qbytes rr') ltac:(rewrite AK by inl; exact H11) A7 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & BK).
    destruct (IH (pp ++ [b]) r2 M1 rom HI tmp mn GL (art_qhead (pp ++ [b]))
                ltac:(rewrite BK; rewrite AK by inl; exact H2) ltac:(rewrite BK; rewrite AK by inl; exact H10) ltac:(rewrite BK; rewrite AK by inl; exact H11)
                ltac:(rewrite BK; rewrite A14; f_equal; rewrite length_app; cbn [length]; lia) ltac:(rewrite BK; rewrite art_qlast_snoc; exact A15)
                ltac:(rewrite BK; exact A16) ltac:(rewrite BK; exact A5) ltac:(lia) ltac:(rewrite <- app_assoc; exact SEP) ltac:(rewrite <- app_assoc; exact IN) HHI Htmp Htmp'
                ltac:(rewrite !length_app; cbn [length]; lia) ltac:(rewrite !art_qbytes_app; cbn [art_qbytes fold_right]; lia)
                ltac:(eapply wr_grows; [exact GW1|exact Wt]) ltac:(eapply wr_grows; [exact GW1|exact Wq])
                ltac:(rewrite <- app_assoc; eapply Forall_impl; [|exact Wl]; intros a Wa; eapply wr_grows; [exact GW1|exact Wa])
                Cb1 ltac:(apply Cl1; destruct rr'; [cbn in More; lia|cbn [art_qhead]; pose proof (Forall_inv INr') as (X0 & _); lia])
                ltac:(rewrite art_qbytes_app; cbn [art_qbytes fold_right]; replace (art_qbytes pp + (qb_size b + 0)) with (art_qbytes pp + qb_size b) by lia; exact Ctb1)
                Ctf1 ltac:(intros _; reflexivity) ltac:(rewrite art_qlast_snoc; exact QLp1) QLr1)
      as (r3 & M3 & RUN3 & C14 & C6 & CK & GW3 & AG3 & D1 & D2 & D3 & D4 & D5 & D6 & D7 & D8 & D9 & D10 & D11).
    set (k' := art_rcy_npop mn rr') in *. cbn [firstn skipn].
    replace (pp ++ b :: firstn k' rr') with ((pp ++ [b]) ++ firstn k' rr') by (rewrite <- app_assoc; reflexivity).
    exists r3, M3. split; [eapply msteps_trans; [exact RUN1|]; eapply msteps_trans; [exact RUN2|exact RUN3]|].
    split; [exact C14|]. split; [exact C6|].
    split; [intros r Hr; rewrite (CK r Hr); rewrite BK; apply AK; exact Hr|].
    split; [eapply mem_grows_trans; [exact GW1|exact GW3]|].
    split. { replace ((pp ++ [b]) ++ rr') with (pp ++ b :: rr') in AG3 by (rewrite <- app_assoc; reflexivity). eapply art_agree_sub; [eapply art_agree_trans; [exact AG1'|exact AG3]|]. intros z Hz H. rewrite !art_out_app in H. rewrite !art_out_app. tauto. }
    repeat (split; [assumption|]). lia.
  - (* [comment removed for export] *)
    destruct (art_rcy_exit r1 M1 rom mn (art_qbytes rr') ltac:(rewrite AK by inl; exact H11) A7 ltac:(lia) ltac:(lia)) as (r2 & RUN2 & BK).
    assert (E0 : art_rcy_npop mn rr' = O). { destruct rr' as [|b2 rr2]; [reflexivity|]. cbn [art_rcy_npop]. replace (mn <? art_qbytes (b2 :: rr2)) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
    rewrite E0. cbn [firstn skipn]. rewrite ?firstn_O, ?skipn_O.
    exists r2, M1. split; [eapply msteps_trans; [exact RUN1|exact RUN2]|].
    split; [rewrite BK; rewrite A14; f_equal; rewrite length_app; cbn [length]; lia|]. split; [rewrite BK; rewrite art_qlast_snoc; exact A6|].
    split; [intros r Hr; rewrite BK; apply AK; exact Hr|]. split; [exact GW1|]. split; [exact AG1'|].
    split; [exact Cc1|]. split; [exact Cf1|]. split; [exact Cb1|].
    split; [intros ->; apply Cl0; reflexivity|]. split; [intros Hne; apply Cl1; destruct rr'; [contradiction|cbn [art_qhead]; pose proof (Forall_inv INr') as (X0 & _); lia]|].
    split; [exact Ctf1|]. split; [rewrite art_qbytes_app; cbn [art_qbytes fold_right]; replace (art_qbytes pp + (qb_size b + 0)) with (art_qbytes pp + qb_size b) by lia; exact Ctb1|].
    split; [rewrite art_qlast_snoc; exact QLp1|]. split; [exact QLr1|]. split; [lia|lia].
Qed.
End FPX.
