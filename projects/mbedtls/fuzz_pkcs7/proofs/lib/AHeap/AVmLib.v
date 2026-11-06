(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Abbreviation eB e := (bv_unsigned (fst e)).
Abbreviation eS e := (bv_unsigned (snd e)).
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Ltac2 gd_tbl_AVmLib () : Init.string Init.list := ["stdpp.bitvector.definitions.bv"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.prod"; "OSSVerify.KrLib.ABoot.BackingAlgebra.iv_wf"; "Corelib.Init.Datatypes.pair"; "Stdlib.Lists.List.In"; "LinuxProcessSemantics.LinuxProcessSem.State.iv_subtract"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.fst"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.snd"; "Corelib.Init.Logic.or"; "Corelib.Init.Datatypes.list"; "OSSVerify.KrLib.ABoot.BackingAlgebra.ivs_wf"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "Corelib.Init.Logic.ex"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.page_in_ranges"; "Corelib.Init.Datatypes.orb"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "LinuxProcessSemantics.LinuxProcessSem.State.page_size"; "Corelib.Init.Logic.iff"; "Corelib.Init.Datatypes.true"; "LinuxProcessSemantics.LinuxProcessSem.State.page_base_of"; "Stdlib.ZArith.BinInt.Z.modulo"; "ARUN_1.covers"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "stdpp.bitvector.definitions.Z_to_bv"; "ARUN_1.clear"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.app"; "ARUN_1.haslit"; "Corelib.Init.Logic.not"; "LinuxProcessSemantics.LinuxProcessSem.State.map_remove"].
   (* [comment removed for export] *)
Section ARUN_1. Context {hAR : arun}.

#[using="Type"] Lemma bv_eqb_refl : forall {n} (a : bv n), bv_eqb a a = true.
Proof. intros n a. unfold bv_eqb. apply Z.eqb_refl. Qed.
#[using="Type"] Lemma bv_eqb_eq : forall {n} (a b : bv n), bv_eqb a b = true <-> a = b.
Proof. intros n a b. unfold bv_eqb. rewrite Z.eqb_eq. split; [apply bv_eq | intros ->; reflexivity]. Qed.

#[using="Type"] Lemma u64_range : forall x : word, 0 <= bv_unsigned x < 2^64.
Proof. intros x. pose proof (bv_unsigned_in_range 64 x) as H. unfold bv_modulus in H. exact H. Qed.
#[using="Type"] Lemma u64_lit : forall z, 0 <= z < 2^64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros. apply unsigned_lit. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma iv_subtract_pieces : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pa,(0.&40.)Psz,(0.&40.)Plo,$1.Phi,$1.Pq,(2.(0.&40.)(0.&40.))P,(3.(4.(0.&40.)(0.&40.)R5.R4.))P,(5.(2.(0.&40.)(0.&40.))R2.(6.R6.R5.R4.R3.))(7.(8.(9.&40.R7.)(9.&40.(:.(0.&40.)(0.&40.)R3.)))(7.(8.(;.(9.&40.(:.(0.&40.)(0.&40.)R3.))(9.&40.(<.(0.&40.)(0.&40.)R3.)))(;.(9.&40.R7.)(9.&40.R6.)))(=.(8.(;.(9.&40.(:.(0.&40.)(0.&40.)R3.))(9.&40.(<.(0.&40.)(0.&40.)R3.)))R5.)(8.R4.(9.&40.(:.(0.&40.)(0.&40.)R3.))))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi q Hwf Hin. unfold iv_wf, B, S in Hwf. cbn [fst snd] in Hwf.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (bv_unsigned a <? lo) eqn:El; [|destruct Hin]. apply Z.ltb_lt in El.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (hi <? bv_unsigned a + bv_unsigned sz) eqn:Er; [|destruct Hin]. apply Z.ltb_lt in Er.
    destruct Hin as [<-|[]]. cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

#[using="Type"] Lemma maps_subtract_pieces : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pl,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Phi,$1.Pq,(2.(0.&40.)(0.&40.))P,(?.R4.)P,(5.(2.(0.&40.)(0.&40.))R2.(10.R5.R4.R3.))(11.(2.(0.&40.)(0.&40.))Lr,(2.(0.&40.)(0.&40.))(7.(5.(2.(0.&40.)(0.&40.))R1.R7.)(7.(8.(9.&40.(:.(0.&40.)(0.&40.)R1.))(9.&40.(:.(0.&40.)(0.&40.)R4.)))(7.(8.(;.(9.&40.(:.(0.&40.)(0.&40.)R4.))(9.&40.(<.(0.&40.)(0.&40.)R4.)))(;.(9.&40.(:.(0.&40.)(0.&40.)R1.))(9.&40.(<.(0.&40.)(0.&40.)R1.))))(=.(8.(;.(9.&40.(:.(0.&40.)(0.&40.)R4.))(9.&40.(<.(0.&40.)(0.&40.)R4.)))R6.)(8.R5.(9.&40.(:.(0.&40.)(0.&40.)R4.))))))))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q Hwf Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in Hwf as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - exists (a, sz). split; [left; reflexivity|]. cbn [fst snd]. exact (iv_subtract_pieces a sz lo hi q Ha Hin).
  - ddestruct (IH lo hi q Hl Hin) as (r & Hr & H). exists r. split; [right; exact Hr | exact H].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_disjoint : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pa,(0.&40.)Psz,(0.&40.)Plo,$1.Phi,$1.P,(12.R2.R1.)P,(12.=(9.&40.R4.))P,(=.(8.(;.(9.&40.R6.)(9.&40.R5.))R4.)(8.R3.(9.&40.R6.)))(13.(>.(2.(0.&40.)(0.&40.)))(6.R7.R6.R5.R4.)(14.(2.(0.&40.)(0.&40.))(4.(0.&40.)(0.&40.)R7.R6.)(15.(2.(0.&40.)(0.&40.)))))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi Hlh Hsz Hd. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs. unfold iv_subtract.
  destruct Hd as [Hd|Hd].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [|exfalso; lia].
    rewrite Z.min_l by lia. rewrite Z_to_bv_bv_unsigned.
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [exfalso; lia | reflexivity].
  - destruct (Z.ltb_spec (bv_unsigned a) lo) as [El|El]; [exfalso; lia|].
    destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [|exfalso; lia].
    cbn [app]. rewrite Z.max_l by lia. replace (bv_unsigned a + bv_unsigned sz - bv_unsigned a) with (bv_unsigned sz) by lia.
    rewrite !Z_to_bv_bv_unsigned. reflexivity.
Qed.

#[using="Type"] Lemma maps_subtract_keeps : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pl,(>.(2.(0.&40.)(0.&40.)))Pb,(0.&40.)Ps,(0.&40.)Plo,$1.Phi,$1.P,(12.R2.R1.)P,(12.=(9.&40.R4.))P,(5.(2.(0.&40.)(0.&40.))(4.(0.&40.)(0.&40.)R6.R5.)R7.)P,(=.(8.(;.(9.&40.R7.)(9.&40.R6.))R5.)(8.R4.(9.&40.R7.)))(5.(2.(0.&40.)(0.&40.))(4.(0.&40.)(0.&40.)R8.R7.)(10.R9.R6.R5.))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros b s lo hi Hlh Hs Hin Hd; [destruct Hin|].
  cbn [maps_subtract]. apply in_app_iff. destruct Hin as [Heq|Hin].
  - injection Heq as -> ->. left. rewrite (iv_subtract_disjoint b s lo hi Hlh Hs Hd). left. reflexivity.
  - right. apply IH; assumption.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma iv_subtract_pos : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pa,(0.&40.)Psz,(0.&40.)Plo,$1.Phi,$1.Pq,(2.(0.&40.)(0.&40.))P,(12.=(9.&40.R4.))P,(8.(;.(9.&40.R6.)(9.&40.R5.))(16.+2.+40.))P,(5.(2.(0.&40.)(0.&40.))R3.(6.R7.R6.R5.R4.))(12.=(9.&40.(<.(0.&40.)(0.&40.)R4.)))")
(* [comment removed for export] *).
Proof.
  intros a sz lo hi q Hs Hwf Hin. pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  unfold iv_subtract in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - destruct (Z.ltb_spec (bv_unsigned a) lo); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
  - destruct (Z.ltb_spec hi (bv_unsigned a + bv_unsigned sz)); [|destruct Hin]. destruct Hin as [<-|[]]. cbn [snd]. rewrite u64_lit by lia. lia.
Qed.
#[using="Type"] Lemma maps_subtract_pos : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pl,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Phi,$1.Pq,(2.(0.&40.)(0.&40.))P,(?.R4.)P,Pe,(2.(0.&40.)(0.&40.))P,(5.(2.(0.&40.)(0.&40.))R1.R6.)(12.=(9.&40.(<.(0.&40.)(0.&40.)R2.)))P,(5.(2.(0.&40.)(0.&40.))R3.(10.R6.R5.R4.))(12.=(9.&40.(<.(0.&40.)(0.&40.)R4.)))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros lo hi q WF POS Hin; [destruct Hin|].
  apply ivs_wf_cons_inv in WF as [Ha Hl]. cbn [maps_subtract] in Hin. apply in_app_iff in Hin as [Hin|Hin].
  - eapply iv_subtract_pos; [| | exact Hin]. { apply (POS (a, sz)). now left. } unfold iv_wf, B, S in Ha. cbn [fst snd] in Ha. exact Ha.
  - eapply IH; [exact Hl| intros; apply POS; now right| exact Hin].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma page_in_ranges_cons : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pp,(0.&40.)Piv,(2.(0.&40.)(0.&40.))Pl,(>.(2.(0.&40.)(0.&40.)))(13.$17.(18.R3.(14.(2.(0.&40.)(0.&40.))R2.R1.))(19.(1:.(1;.(9.&40.(:.(0.&40.)(0.&40.)R2.))(9.&40.R3.))(1;.(;.(9.&40.R3.)$1<.)(;.(9.&40.(:.(0.&40.)(0.&40.)R2.))(9.&40.(<.(0.&40.)(0.&40.)R2.)))))(18.R3.R1.)))")
(* [comment removed for export] *).
Proof. reflexivity. Qed.


#[using="Type"] Lemma page_in_ranges_true : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pp,(0.&40.)Pl,(>.(2.(0.&40.)(0.&40.)))(1=.(13.$17.(18.R2.R1.)$1>.)(11.(2.(0.&40.)(0.&40.))Liv,(2.(0.&40.)(0.&40.))(7.(5.(2.(0.&40.)(0.&40.))R1.R2.)(7.(8.(9.&40.(:.(0.&40.)(0.&40.)R1.))(9.&40.R3.))(8.(;.(9.&40.R3.)$1<.)(;.(9.&40.(:.(0.&40.)(0.&40.)R1.))(9.&40.(<.(0.&40.)(0.&40.)R1.))))))))")
(* [comment removed for export] *).
Proof.
  intros p l. unfold page_in_ranges. rewrite existsb_exists. split.
  - intros [iv [Hin Hb]]. apply andb_prop in Hb as [H1 H2]. apply Z.leb_le in H1. apply Z.leb_le in H2. eauto.
  - (intros dd_H; ddestruct dd_H as (iv & Hin & H1 & H2)). exists iv. split; [exact Hin|]. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.



#[using="Type"] Lemma page_base_of_facts : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pz,$1.P,(7.(8.=R1.)(12.R1.(16.+2.+40.)))(7.(8.(9.&40.(1?.R2.))R2.)(7.(12.R2.(;.(9.&40.(1?.R2.))+1000.))(13.$1.(20.(9.&40.(1?.R2.))+1000.)=)))")
(* [comment removed for export] *).
Proof.
  intros z Hz. unfold page_base_of, page_size.
  assert (H : 0 <= z / 4096 * 4096 <= z) by lia.
  rewrite u64_lit by lia. split; [lia|]. split; [lia|]. rewrite Z.mod_mul by lia. reflexivity.
Qed.



(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition covers (X : list (word * word)) (lo hi : Z) : Prop :=
  exists e, In e X /\ eB e <= lo /\ hi <= eB e + eS e.
Definition clear (X : list (word * word)) (lo hi : Z) : Prop :=
  forall e, In e X -> eB e + eS e <= lo \/ hi <= eB e.
Definition haslit (X : list (word * word)) (lo len : Z) : Prop :=
  In (Z_to_bv 64 lo, Z_to_bv 64 len) X.

(* [comment removed for export] *)
#[using="Type"] Lemma covers_map_contains : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Pn,$1.P,(8.=R2.)P,(8.=R2.)P,(12.(;.R4.R3.)(16.+2.+40.))P,(21.R6.R5.(;.R5.R4.))(13.$17.(22.R7.(23.&40.R6.)(23.&40.R5.))$1>.)")
(* [comment removed for export] *).
Proof.
  (intros X lo n H0 H1 H2 dd_H; ddestruct dd_H as (e & Hin & A & Bd)). unfold map_contains. apply existsb_exists. exists e. split; [exact Hin|].
  rewrite !u64_lit by lia. apply andb_true_intro. split; apply Z.leb_le; lia.
Qed.

#[using="Type"] Lemma clear_region_free : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Pn,$1.P,(8.=R2.)P,(8.=R2.)P,(12.(;.R4.R3.)(16.+2.+40.))P,(24.R6.R5.(;.R5.R4.))(13.$17.(25.R7.(23.&40.R6.)(23.&40.R5.))$1>.)")
(* [comment removed for export] *).
Proof.
  intros X lo n H0 H1 H2 CL. apply region_free_intro. intros a sz Hin.
  specialize (CL (a, sz) Hin). cbn [fst snd] in CL. unfold iv_overlap. rewrite !u64_lit by lia.
  apply Bool.andb_false_iff. destruct CL as [CL|CL]; [left| right]; apply Z.ltb_ge; lia.
Qed.

#[using="Type"] Lemma region_free_clear : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Pa,(0.&40.)Pn,(0.&40.)P,(12.=(9.&40.R1.))P,(13.$17.(25.R4.R3.R2.)$1>.)(24.R5.(9.&40.R4.)(;.(9.&40.R4.)(9.&40.R3.)))")
(* [comment removed for export] *).
Proof.
  intros X a n Hn RF e Hin. destruct e as [b s]. cbn [fst snd].
  pose proof (region_free_In X a n b s RF Hin) as OV. unfold iv_overlap in OV.
  apply Bool.andb_false_iff in OV. destruct OV as [OV|OV]; apply Z.ltb_ge in OV; lia.
Qed.

#[using="Type"] Lemma region_free_app : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pl1,(>.(2.(0.&40.)(0.&40.)))Pl2,(>.(2.(0.&40.)(0.&40.)))Plo,(0.&40.)Pn,(0.&40.)(13.$17.(25.(26.(2.(0.&40.)(0.&40.))R4.R3.)R2.R1.)(1:.(25.R4.R2.R1.)(25.R3.R2.R1.)))")
(* [comment removed for export] *).
Proof. induction l1 as [|[a s] l1 IH]; intros; cbn; [reflexivity|]. rewrite IH, andb_assoc. reflexivity. Qed.

#[using="Type"] Lemma haslit_map_has : forall X lo len, haslit X lo len -> map_has X (Z_to_bv 64 lo) (Z_to_bv 64 len) = true.
Proof.
  intros X lo len H. unfold map_has. apply existsb_exists. exists (Z_to_bv 64 lo, Z_to_bv 64 len). split; [exact H|].
  cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
Qed.


#[using="Type"] Lemma covers_weaken : forall X lo hi lo' hi', covers X lo hi -> lo <= lo' -> hi' <= hi -> covers X lo' hi'.
Proof. (intros X lo hi lo' hi' dd_H; ddestruct dd_H as (e & Hin & A & Bd); intros H1 H2). exists e. split; [exact Hin| lia]. Qed.
#[using="Type"] Lemma clear_weaken : forall X lo hi lo' hi', clear X lo hi -> lo <= lo' -> hi' <= hi -> clear X lo' hi'.
Proof. intros X lo hi lo' hi' CL H1 H2 e Hin. specialize (CL e Hin). lia. Qed.


(* [comment removed for export] *)
#[using="Type"] Lemma covers_cons : forall e X lo hi, covers X lo hi -> covers (e :: X) lo hi.
Proof. (intros e X lo hi dd_H; ddestruct dd_H as (e' & Hin & H)). exists e'. split; [right; exact Hin| exact H]. Qed.
#[using="Type"] Lemma covers_cons_new : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pa,(0.&40.)Pn,(0.&40.)PX,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Phi,$1.P,(8.(9.&40.R5.)R2.)P,(8.R2.(;.(9.&40.R6.)(9.&40.R5.)))(21.(14.(2.(0.&40.)(0.&40.))(4.(0.&40.)(0.&40.)R7.R6.)R5.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros a n X lo hi H1 H2. exists (a, n). split; [left; reflexivity| cbn [fst snd]; lia]. Qed.
#[using="Type"] Lemma clear_cons : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "Pa,(0.&40.)Pn,(0.&40.)PX,(>.(2.(0.&40.)(0.&40.)))Plo,$1.Phi,$1.P,(24.R3.R2.R1.)P,(=.(8.(;.(9.&40.R6.)(9.&40.R5.))R3.)(8.R2.(9.&40.R6.)))(24.(14.(2.(0.&40.)(0.&40.))(4.(0.&40.)(0.&40.)R7.R6.)R5.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros a n X lo hi CL H e [<-|Hin]; [cbn [fst snd]; exact H| apply CL; exact Hin]. Qed.
#[using="Type"] Lemma haslit_cons : forall e X lo len, haslit X lo len -> haslit (e :: X) lo len.
Proof. intros. right. assumption. Qed.
#[using="Type"] Lemma clear_app : forall X Y lo hi, clear X lo hi -> clear Y lo hi -> clear (X ++ Y) lo hi.
Proof. intros X Y lo hi CX CY e Hin. apply in_app_iff in Hin. destruct Hin; [apply CX| apply CY]; assumption. Qed.
#[using="Type"] Lemma clear_app_inv : forall X Y lo hi, clear (X ++ Y) lo hi -> clear X lo hi /\ clear Y lo hi.
Proof. intros X Y lo hi C. split; intros e Hin; apply C; apply in_app_iff; [left|right]; exact Hin. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma clear_subtract : forall X c d lo hi, ivs_wf X -> clear X lo hi -> clear (maps_subtract X c d) lo hi.
Proof.
  intros X c d lo hi WF CL q Hq. ddestruct (maps_subtract_pieces X c d q WF Hq) as (r & Hr & H1 & H2 & _).
  specialize (CL r Hr). lia.
Qed.

#[using="Type"] Lemma clear_subtract_cut : forall X c d lo hi, ivs_wf X -> c <= lo -> hi <= d -> clear (maps_subtract X c d) lo hi.
Proof.
  intros X c d lo hi WF H1 H2 q Hq. ddestruct (maps_subtract_pieces X c d q WF Hq) as (r & Hr & _ & _ & H3). lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma covers_subtract : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Pc,$1.Pd,$1.Plo,$1.Phi,$1.P,(?.R5.)P,(12.R5.R4.)P,(12.R4.R3.)P,(21.R8.R5.R4.)P,(=.(8.R5.R8.)(8.R7.R6.))(21.(10.R:.R9.R8.)R7.R6.)")
(* [comment removed for export] *).
Proof.
  (intros X c d lo hi WF CD LH dd_H; ddestruct dd_H as (e & Hin & A & Bd); intros AP).
  destruct e as [a sz]. cbn [fst snd] in A, Bd.
  pose proof (u64_range a) as Ra. pose proof (u64_range sz) as Rs.
  assert (WFe : bv_unsigned a + bv_unsigned sz <= 2^64) by (exact (WF (a, sz) Hin)).
  apply in_split in Hin. ddestruct Hin as (l1 & l2 & ->).
  (* [comment removed for export] *)
  unfold covers. rewrite maps_subtract_app. cbn [maps_subtract].
  destruct (Z.le_gt_cases (bv_unsigned a + bv_unsigned sz) c) as [E1|E1].
  { exists (a, sz). split; [| cbn [fst snd]; lia]. apply in_app_iff. right. apply in_app_iff. left.
    rewrite (iv_subtract_disjoint a sz c d CD ltac:(lia) ltac:(left; exact E1)). left. reflexivity. }
  destruct (Z.le_gt_cases d (bv_unsigned a)) as [E2|E2].
  { exists (a, sz). split; [| cbn [fst snd]; lia]. apply in_app_iff. right. apply in_app_iff. left.
    rewrite (iv_subtract_disjoint a sz c d CD ltac:(lia) ltac:(right; exact E2)). left. reflexivity. }
  (* [comment removed for export] *)
  unfold iv_subtract. destruct AP as [AP|AP].
  - (* [comment removed for export] *)
    destruct (Z.ltb_spec (bv_unsigned a) c) as [El|El]; [| exfalso; lia].
    exists (a, Z_to_bv 64 (Z.min (bv_unsigned sz) (c - bv_unsigned a))). split.
    + apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. left. left. reflexivity.
    + cbn [fst snd]. rewrite u64_lit by lia. lia.
  - destruct (Z.ltb_spec d (bv_unsigned a + bv_unsigned sz)) as [Er|Er]; [| exfalso; lia].
    exists (Z_to_bv 64 (Z.max (bv_unsigned a) d), Z_to_bv 64 (bv_unsigned a + bv_unsigned sz - Z.max (bv_unsigned a) d)). split.
    + apply in_app_iff. right. apply in_app_iff. left. apply in_app_iff. right.
      destruct (bv_unsigned a <? c); [left; reflexivity| left; reflexivity].
    + cbn [fst snd]. rewrite !u64_lit by lia. lia.
Qed.

#[using="Type"] Lemma haslit_subtract : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Pc,$1.Pd,$1.Plo,$1.Plen,$1.P,(12.R4.R3.)P,(8.=R3.)P,(12.=R3.)P,(12.(;.R5.R4.)(16.+2.+40.))P,(27.R9.R6.R5.)P,(=.(8.(;.R7.R6.)R9.)(8.R8.R7.))(27.(10.R;.R:.R9.)R8.R7.)")
(* [comment removed for export] *).
Proof.
  intros X c d lo len CD H0 H1 H2 HL AP. unfold haslit in *.
  apply maps_subtract_keeps; rewrite ?u64_lit by lia; try assumption; lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma in_map_remove : forall X (a : word) e, In e (map_remove X a) <-> In e X /\ fst e <> a.
Proof.
  intros X a e. unfold map_remove. rewrite filter_In. split.
  - intros [H1 H2]. split; [exact H1|]. intros E. rewrite E, bv_eqb_refl in H2. discriminate.
  - intros [H1 H2]. split; [exact H1|]. destruct (bv_eqb (fst e) a) eqn:E; [| reflexivity]. apply bv_eqb_eq in E. congruence.
Qed.
#[using="Type"] Lemma covers_remove : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Pa,(0.&40.)Plo,$1.Phi,$1.P,(21.R4.R2.R1.)P,Pe,(2.(0.&40.)(0.&40.))P,(5.(2.(0.&40.)(0.&40.))R1.R6.)P,(8.(9.&40.(:.(0.&40.)(0.&40.)R2.))R5.)P,(8.R5.(;.(9.&40.(:.(0.&40.)(0.&40.)R3.))(9.&40.(<.(0.&40.)(0.&40.)R3.))))(28.(13.(0.&40.)(:.(0.&40.)(0.&40.)R4.)R8.))(21.(29.R6.R5.)R4.R3.)")
(* [comment removed for export] *).
Proof.
  (intros X a lo hi dd_H; ddestruct dd_H as (e & Hin & A & Bd); intros NE). exists e. split; [| lia]. apply in_map_remove. split; [exact Hin|]. apply (NE e Hin A Bd).
Qed.
#[using="Type"] Lemma haslit_remove : ltac2:(CDefT.buildp (gd_tbl_AVmLib ()) "PX,(>.(2.(0.&40.)(0.&40.)))Pa,(0.&40.)Plo,$1.Plen,$1.P,(27.R4.R2.R1.)P,(28.(13.(0.&40.)(23.&40.R3.)R4.))(27.(29.R6.R5.)R4.R3.)")
(* [comment removed for export] *).
Proof. intros X a lo len H NE. unfold haslit in *. apply in_map_remove. split; [exact H| cbn [fst]; exact NE]. Qed.
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma ivs_wf_remove : forall X a, ivs_wf X -> ivs_wf (map_remove X a).
Proof. intros X a WF. unfold map_remove. apply ivs_wf_filter. exact WF. Qed.

End ARUN_1.
