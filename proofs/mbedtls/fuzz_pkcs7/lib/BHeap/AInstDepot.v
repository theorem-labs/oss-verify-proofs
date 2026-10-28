(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Bool Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase State.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import MState.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import BackingAlgebra.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import ALazy AShadow.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ASys ASysS. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AKinv. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import AFreeSlot AVmLib. From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BHeap Require Import AVm.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.LibA Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import LiaKitAH. (* [comment removed for export] *)
Local Ltac Stdlib.micromega.Lia.lia ::= lia_ah.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.AHeap Require Import ACeil.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AInstDepot () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Corelib.Init.Logic.and"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.HKv"; "Corelib.Init.Logic.ex"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.nil"; "ARUN_1.InstDepot.sane"; "Stdlib.ZArith.BinInt.Z.pow"; "ARUN_1.InstDepot.vN"; "ARUN_1.InstDepot.vS"; "ARUN_1.InstDepot.vNS"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vcs"; "Stdlib.Lists.List.In"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.length"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Logic.iff"; "ARUN_1.InstDepot.CSd"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "ARUN_1.InstDepot.Kd"; "RocqVerifyHarness.AgentSubmission.BHeap.AVm.vst"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.hull64"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_got"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_gsb"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Init.Datatypes.true"; "stdpp.bitvector.definitions.bv_unsigned"; "RocqVerifyHarness.AgentSubmission.AHeap.ACeil.ACEIL"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_lo"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.al_img_hi"; "ARUN_1.InstDepot.Gn"; "Stdlib.ZArith.BinInt.Z.modulo"; "stdpp.bitvector.definitions.Z_to_bv"; "RocqVerifyHarness.AgentSubmission.AHeap.ASys.anon_grant"; "RocqVerifyHarness.AgentSubmission.LibA.ALazy.crange"; "ARUN_1.InstDepot.Gs"].

Section ARUN_1. Context {hAR : arun}.
Definition RES_DEPOT : Z := 2^20 + 4096 * ((2^20 / 32768 + 3) + (2^23 / 32768 + 3) + (2^23 / 4096 + 1)).

Section InstDepot.
  Variable AL : asan_layout.
  Hypothesis ALWF : al_wf AL.
  Hypothesis ASB : al_sb AL = 0x7fff8000.
  Hypothesis IML : al_img_lo AL <= 0x10000.
  Hypothesis IMH : al_img_hi AL = 0x65f000.
  Hypothesis GOT64 : al_img_lo AL + 64 <= al_got AL /\ al_got AL + 128 <= al_img_hi AL /\ al_got AL mod 8 = 0.
  Hypothesis GSB64 : al_img_lo AL + 64 <= al_gsb AL /\ al_gsb AL + 128 <= al_img_hi AL /\ al_gsb AL mod 8 = 0.

  Variable v0 : vst.
  Variables nb0 bl0 : list Z.
  Hypothesis VR0 : vranges_ok AL v0.
  Hypothesis VWF0 : vwf AL v0.
  Hypothesis SLACK : v_eb v0 + 4096 * vnb v0 + RES_DEPOT <= VLIMIT.
  Hypothesis CB20 : v_cb20 v0 < J20.
  Hypothesis CB23 : v_cb23 v0 + (2^20 / 2^23 + 2) < J23.

  Definition vN (x : Z) : vst := v_add_eager v0 x (2^20) true.
  Definition vS (y : Z) : vst := v_add_lazy v0 y (2^23).
  Definition vNS (x y : Z) : vst := v_add_lazy (vN x) y (2^23).

  Definition sane (n b : Z) : Prop := 0x65f000 <= b /\ b + n <= ACEIL /\ (b + n <= 0x7fff7000 \/ 0x10007fff8000 <= b).

  Definition Kd (nb bl : list Z) (mo : Model) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "(0.(1.(2.(3.$4.)O3.Vnb0,)(1.(2.(3.$4.)O2.Vbl0,)(5.VhAR,VAL,Vv0,O1.)))(0.(6.$4.Lx,$4.(1.(2.(3.$4.)O3.(7.$4.Vnb0,(8.$4.R1.(9.$4.))))(1.(2.(3.$4.)O2.Vbl0,)(1.(:.(;.+2.+14.)R1.)(5.VhAR,VAL,(<.R1.)O1.)))))(0.(6.$4.Ly,$4.(1.(2.(3.$4.)O3.Vnb0,)(1.(2.(3.$4.)O2.(7.$4.Vbl0,(8.$4.R1.(9.$4.))))(1.(:.(;.+2.+17.)R1.)(5.VhAR,VAL,(=.R1.)O1.)))))(6.$4.Lx,$4.(6.$4.Ly,$4.(1.(2.(3.$4.)O3.(7.$4.Vnb0,(8.$4.R2.(9.$4.))))(1.(2.(3.$4.)O2.(7.$4.Vbl0,(8.$4.R1.(9.$4.))))(1.(:.(;.+2.+14.)R2.)(1.(:.(;.+2.+17.)R1.)(5.VhAR,VAL,(>.R2.R1.)O1.))))))))))")
(* [comment removed for export] *).

  Definition CSd (nb bl : list Z) (x : Z) : Prop := ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "(0.(?.VAL,Vv0,O1.)(0.(6.$4.Lb,$4.(1.(10.$4.R1.(11.$4.(12.$4.Vnb0,)O3.))(1.(:.(;.+2.+14.)R1.)(1.(13.R1.O1.)(14.O1.(15.R1.(;.+2.+14.)))))))(6.$4.Lb,$4.(1.(10.$4.R1.(11.$4.(12.$4.Vbl0,)O2.))(1.(:.(;.+2.+17.)R1.)(1.(13.R1.O1.)(14.O1.(15.R1.(;.+2.+17.)))))))))")
(* [comment removed for export] *).

  Definition Gn (nb bl : list Z) : Prop := nb = nb0 /\ bl = bl0.
  Definition Gs (nb bl : list Z) : Prop := bl = bl0 /\ (nb = nb0 \/ exists x, nb = nb0 ++ [x]).

  #[using="Type"] Lemma skipn_self : forall (l : list Z), skipn (length l) l = [].
  Proof. intros. apply skipn_all. Qed.
  #[using="Type"] Lemma skipn_self_app : forall (l r : list Z), skipn (length l) (l ++ r) = r.
  Proof. intros l r. rewrite skipn_app, skipn_all, Nat.sub_diag. reflexivity. Qed.
  #[using="Type"] Lemma app_cons_neq : forall (l : list Z) x, l ++ [x] <> l.
  Proof. intros l x E. apply (f_equal (@length Z)) in E. rewrite app_length in E. cbn in E. clear - E. lia. Qed.

  #[using="Type"] Lemma vcs_N : forall a x, vcs AL (vN a) x <-> vcs AL v0 x \/ a <= x < a + 2^20.
  Proof.
    intros a x. unfold vcs, vN. cbn [v_stk v_img v_tr v_add_eager]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R|].
      left. right. right. exists t. split; [exact Ht| split; [exact TC| exact R]].
    - intros [[A|[A|(t & Ht & TC & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.
  #[using="Type"] Lemma vcs_S : forall b x, vcs AL (vS b) x <-> vcs AL v0 x \/ b <= x < b + 2^23.
  Proof.
    intros b x. unfold vcs, vS. cbn [v_stk v_img v_tr v_add_lazy]. split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [left; left; exact A| left; right; left; exact A| right; unfold t_hi in R; cbn in R; exact R|].
      left. right. right. exists t. split; [exact Ht| split; [exact TC| exact R]].
    - intros [[A|[A|(t & Ht & TC & R)]]|R]; [left; exact A| right; left; exact A| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]|].
      right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.
  #[using="Type"] Lemma vcs_NS : forall a b x, vcs AL (vNS a b) x <-> vcs AL v0 x \/ a <= x < a + 2^20 \/ b <= x < b + 2^23.
  Proof.
    intros a b x. unfold vNS. unfold vcs at 1. cbn [v_stk v_img v_tr v_add_lazy]. fold (vN a). split.
    - intros [A|[A|(t & [<-|Ht] & TC & R)]]; [| | right; right; unfold t_hi in R; cbn in R; exact R|].
      + destruct (proj1 (vcs_N a x) ltac:(left; exact A)); [left| right; left]; assumption.
      + destruct (proj1 (vcs_N a x) ltac:(right; left; exact A)); [left| right; left]; assumption.
      + destruct (proj1 (vcs_N a x) ltac:(right; right; exists t; split; [exact Ht| split; [exact TC| exact R]])); [left| right; left]; assumption.
    - intros [A|[A|R]].
      + destruct (proj2 (vcs_N a x) ltac:(left; exact A)) as [B|[B|(t & Ht & TC & R)]]; [left; exact B| right; left; exact B| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]].
      + destruct (proj2 (vcs_N a x) ltac:(right; exact A)) as [B|[B|(t & Ht & TC & R)]]; [left; exact B| right; left; exact B| right; right; exists t; split; [right; exact Ht| split; [exact TC| exact R]]].
      + right. right. eexists. split; [left; reflexivity|]. unfold t_hi. cbn [t_cs t_lo t_len]. split; [reflexivity| exact R].
  Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma CSd_v0 : forall x, CSd nb0 bl0 x <-> vcs AL v0 x.
  Proof. intros x. unfold CSd. rewrite !skipn_self. cbn. split; [intros [A|[(b & [] & _)|(b & [] & _)]]; exact A| intros A; left; exact A]. Qed.
  #[using="Type"] Lemma CSd_N : forall a x, sane (2^20) a -> CSd (nb0 ++ [a]) bl0 x <-> vcs AL (vN a) x.
  Proof.
    intros a x SA. unfold CSd. rewrite skipn_self_app, skipn_self. rewrite vcs_N. cbn. split.
    - intros [A|[(b & [<-|[]] & _ & R)|(b & [] & _)]]; [left; exact A| right; exact R].
    - intros [A|R]; [left; exact A| right; left; exists a; auto].
  Qed.
  #[using="Type"] Lemma CSd_S : forall b x, sane (2^23) b -> CSd nb0 (bl0 ++ [b]) x <-> vcs AL (vS b) x.
  Proof.
    intros b x SB. unfold CSd. rewrite skipn_self_app, skipn_self. rewrite vcs_S. cbn. split.
    - intros [A|[(c & [] & _)|(c & [<-|[]] & _ & R)]]; [left; exact A| right; exact R].
    - intros [A|R]; [left; exact A| right; right; exists b; auto].
  Qed.
  #[using="Type"] Lemma CSd_NS : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pa,$4.Pb,$4.Px,$4.P,(:.(;.+2.+14.)R3.)P,(:.(;.+2.+17.)R3.)(16.(17.(7.$4.Vnb0,(8.$4.R5.(9.$4.)))(7.$4.Vbl0,(8.$4.R4.(9.$4.)))R3.)(?.VAL,(>.R5.R4.)R3.))")
(* [comment removed for export] *).
  Proof.
    intros a b x SA SB. unfold CSd. rewrite !skipn_self_app. rewrite vcs_NS. cbn. split.
    - intros [A|[(c & [<-|[]] & _ & R)|(c & [<-|[]] & _ & R)]]; [left; exact A| right; left; exact R| right; right; exact R].
    - intros [A|[R|R]]; [left; exact A| right; left; exists a; auto| right; right; exists b; auto].
  Qed.

  #[using="Type"] Lemma Kd_cases : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pnb,(3.$4.)Pbl,(3.$4.)Pmo,$18.P,(19.R3.R2.R1.)(6.$1:.Lv,$1:.(1.(5.VhAR,VAL,R1.R3.)(1.Px,$4.(16.(17.R6.R5.R1.)(?.VAL,R2.R1.))(0.(1.(2.(3.$4.)R5.Vnb0,)(1.(2.(3.$4.)R4.Vbl0,)(2.$1:.R1.Vv0,)))(0.(6.$4.La,$4.(1.(2.(3.$4.)R6.(7.$4.Vnb0,(8.$4.R1.(9.$4.))))(1.(2.(3.$4.)R5.Vbl0,)(1.(:.(;.+2.+14.)R1.)(2.$1:.R2.(<.R1.))))))(0.(6.$4.Lb,$4.(1.(2.(3.$4.)R6.Vnb0,)(1.(2.(3.$4.)R5.(7.$4.Vbl0,(8.$4.R1.(9.$4.))))(1.(:.(;.+2.+17.)R1.)(2.$1:.R2.(=.R1.))))))(6.$4.La,$4.(6.$4.Lb,$4.(1.(2.(3.$4.)R7.(7.$4.Vnb0,(8.$4.R2.(9.$4.))))(1.(2.(3.$4.)R6.(7.$4.Vbl0,(8.$4.R1.(9.$4.))))(1.(:.(;.+2.+14.)R2.)(1.(:.(;.+2.+17.)R1.)(2.$1:.R3.(>.R2.R1.))))))))))))))")
(* [comment removed for export] *).
  Proof.
    intros nb bl mo [(-> & -> & K)|[(a & -> & -> & SA & K)|[(b & -> & -> & SB & K)|(a & b & -> & -> & SA & SB & K)]]].
    - exists v0. split; [exact K|]. split; [apply CSd_v0|]. left. auto.
    - exists (vN a). split; [exact K|]. split; [intros x; apply CSd_N; exact SA|]. right. left. exists a. auto.
    - exists (vS b). split; [exact K|]. split; [intros x; apply CSd_S; exact SB|]. right. right. left. exists b. auto.
    - exists (vNS a b). split; [exact K|]. split; [intros x; apply CSd_NS; assumption|]. right. right. right. dexists a, b. auto 10.
  Qed.

  (* [comment removed for export] *)
  #[using="AL"] Lemma vnb_N : forall a, vnb (vN a) = vnb v0 + (2^20 / 32768 + 3).
  Proof. intros a. unfold vnb, vN, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_eager List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. cbn [snd]. lia. Qed.
  #[using="AL"] Lemma vnb_S : forall v b, vnb (v_add_lazy v b (2^23)) = vnb v + (2^23 / 32768 + 3) + (2^23 / 4096 + 1).
  Proof. intros v b. unfold vnb, csranges, lazyranges. cbn [v_stk v_img v_tr v_ghost v_add_lazy List.filter is_lazy_cs t_kind t_cs map app zsum]. cbn [t_lo t_len]. unfold npages_shadow at 3. unfold npages_inside at 1. cbn [snd]. lia. Qed.
  #[using="Type"] Lemma veb_N : forall a, v_eb (vN a) = v_eb v0 + 2^20.  Proof. reflexivity. Qed.
      #[using="Type"] Lemma vcb23_N : forall a, v_cb23 (vN a) = v_cb23 v0 + (2^20 / 2^23 + 2). Proof. reflexivity. Qed.

  #[using="Type"] Lemma vranges_ok_add_eager : forall v lo n, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_eager v lo n true).
  Proof.
    (intros v lo n dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. split.
    - unfold csranges in *. cbn [v_stk v_img v_tr v_ghost v_add_eager List.filter t_cs map]. inversion B as [|? ? B1 B2]; subst.
      constructor; [exact B1|]. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B3|]. cbn [app]. constructor; [cbn; lia| exact B4].
    - unfold lazyranges in *. cbn [v_tr v_add_eager List.filter is_lazy_cs t_kind map]. exact C.
  Qed.
  #[using="Type"] Lemma vranges_ok_add_lazy : forall v lo n, vranges_ok AL v -> 0 <= lo -> 0 <= n -> vranges_ok AL (v_add_lazy v lo n).
  Proof.
    (intros v lo n dd_H; ddestruct dd_H as (A & B & C); intros H0 H1). split; [exact A|]. split.
    - unfold csranges in *. cbn [v_stk v_img v_tr v_ghost v_add_lazy List.filter t_cs map]. inversion B as [|? ? B1 B2]; subst.
      constructor; [exact B1|]. inversion B2 as [|? ? B3 B4]; subst. constructor; [exact B3|]. cbn [app]. constructor; [cbn; lia| exact B4].
    - unfold lazyranges in *. cbn [v_tr v_add_lazy List.filter is_lazy_cs t_kind t_cs map]. constructor; [cbn; lia| exact C].
  Qed.

  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="hAR ALWF IML IMH GOT64 GSB64 VWF0"] Lemma vcs0_range : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Px,$4.P,(?.VAL,Vv0,R1.)(1.(1.(13.=R2.)(14.R2.(;.+2.+2?.)))(1.(0.(13.(15.R2.+1.)+7???7000.)(13.+10007???8000.R2.))(1.(1;.(1.(13.(1<.(1=.VAL,))R2.)(14.R2.(15.(1<.(15.(1=.VAL,)+7.))+40.))))(1;.(1.(13.(1<.(1>.VAL,))R2.)(14.R2.(15.(1<.(15.(1>.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros x Hx. dpose VWF0 as (TWF & _ & _ & _ & _ & STK0 & STK1 & STK2 & IMG0 & IMG1 & IMG2 & IMG3 & IMG4 & _ & BANDCS & _).
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5).
    aceilb. rewrite IMH in *.
    destruct Hx as [Y|[(Y & G1 & G2)|(t & Ht & TC & R)]].
    - lia.
    - rewrite IMG0, IMG1 in Y. lia.
    - pose proof (proj1 (Forall_forall _ _) TWF t Ht) as (T0 & T1 & T2 & _ & _ & _ & T6). pose proof (BANDCS t Ht TC) as B.
      unfold t_hi in *. lia.
  Qed.

  #[using="ALWF IML IMH GOT64 GSB64 VWF0"] Lemma CSd_range : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pnb,(3.$4.)Pbl,(3.$4.)Px,$4.P,(17.R3.R2.R1.)(1.(1.(13.=R2.)(14.R2.(;.+2.+2?.)))(1.(0.(13.(15.R2.+1.)+7???7000.)(13.+10007???8000.R2.))(1.(1;.(1.(13.(1<.(1=.VAL,))R2.)(14.R2.(15.(1<.(15.(1=.VAL,)+7.))+40.))))(1;.(1.(13.(1<.(1>.VAL,))R2.)(14.R2.(15.(1<.(15.(1>.VAL,)+7.))+40.)))))))")
(* [comment removed for export] *).
  Proof.
    intros nb bl x [A|[(b & _ & SB & R)|(b & _ & SB & R)]]; [apply vcs0_range; exact A| |];
    pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_got AL + 7)) as HG2; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_gsb AL + 7)) as HS2;
      dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5); rewrite IMH in *; unfold sane in SB;
      lia.
  Qed.

  #[using="ALWF ASB IML IMH GOT64 GSB64 VWF0"] Theorem D_CSOK : forall nb bl, cs_ok AL (CSd nb bl).
  Proof.
    intros nb bl. split; [| split; [| split]].
    all: (pose proof (hull64_le (al_got AL)) as HG1; pose proof (hull64_le (al_gsb AL)) as HS1; pose proof (hull64_le (al_got AL + 7)) as HG3; pose proof (hull64_le (al_gsb AL + 7)) as HS3; pose proof (hull64_al8 _ (proj2 (proj2 GOT64))) as HG2; pose proof (hull64_al8 _ (proj2 (proj2 GSB64))) as HS2; rewrite ?HG2, ?HS2 in *).
    - intros c Hc. dpose (CSd_range nb bl c Hc) as (R1 & R2 & R3 & R4). unfold shadow_of. rewrite ASB.
      pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). assert (c / 8 <= 2^47 / 8) by (apply Z.div_le_mono; lia). change (2^47 / 8) with 17592186044416 in *.
      split; [lia|]. split; [lia|]. split; [lia|]. intros Hs. pose proof (CSd_range nb bl _ Hs) as (S1 & S2 & _). lia.
    - intros i Hi. split; intros Hc; pose proof (CSd_range nb bl _ Hc) as (R1 & R2 & R3 & R4); lia.
    - intros c i Hc Hi. pose proof (CSd_range nb bl c Hc) as (R1 & _). dpose ALWF as (AW0 & AW1 & AW2 & AW3 & AW4 & AW5). rewrite IMH in *.
      unfold shadow_of. rewrite ASB. pose proof (Z.div_pos c 8 ltac:(lia) ltac:(lia)). lia.
    - rewrite ASB. lia.
  Qed.

  #[using="ALWF IML IMH GOT64 GSB64 VWF0"] Theorem D_noshadow : forall nb bl x, CSd nb bl x -> ~ (0x7fff8000 <= x < 0x10007fff8000).
  Proof. intros nb bl x Hx. dpose (CSd_range nb bl x Hx) as (_ & R & _). lia. Qed.

  #[using="VR0"] Theorem D_KL : forall nb bl, kinv AL (CSd nb bl) (Kd nb bl).
  Proof.
    intros nb bl. split.
    - intros mo K. ddestruct (Kd_cases nb bl mo K) as (v & HK & _). exact (proj1 HK).
    - intros mo K. ddestruct (Kd_cases nb bl mo K) as (v & HK & _). exact (HKv_top AL v mo HK).
    - intros mo acc K OK. ddestruct (Kd_cases nb bl mo K) as (v & HK & EQ & CASE).
      assert (VR : vranges_ok AL v).
      { destruct CASE as [(_ & _ & ->)|[(a & _ & _ & SA & ->)|[(b & _ & _ & SB & ->)|(a & b & _ & _ & SA & SB & ->)]]];
          unfold vN, vS, vNS, vN, sane in *; [exact VR0| apply vranges_ok_add_eager; [exact VR0| lia| lia]
          | apply vranges_ok_add_lazy; [exact VR0| lia| lia] | apply vranges_ok_add_lazy; [apply vranges_ok_add_eager; [exact VR0| lia| lia]| lia| lia]]. }
      destruct (ki_mat (HKv_kinv AL v VR) mo acc HK (acc_ok_mono AL _ _ acc (fun x H => proj1 (EQ x) H) OK)) as (mo' & E & HK' & MM).
      exists mo'. split; [exact E|]. split; [| exact MM].
      destruct CASE as [(-> & -> & ->)|[(a & -> & -> & SA & ->)|[(b & -> & -> & SB & ->)|(a & b & -> & -> & SA & SB & ->)]]].
      + left. auto.
      + right. left. exists a. auto.
      + right. right. left. exists b. auto.
      + right. right. right. dexists a, b. auto 10.
  Qed.

  #[using="Type"] Theorem D_CSmono_n : forall nb bl a x, CSd nb bl x -> CSd (nb ++ [a]) bl x.
  Proof.
    intros nb bl a x [A|[(b & Hb & SB & R)|A]]; [left; exact A| right; left| right; right; exact A].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.
  #[using="Type"] Theorem D_CSmono_s : forall nb bl a x, CSd nb bl x -> CSd nb (bl ++ [a]) x.
  Proof.
    intros nb bl a x [A|[A|(b & Hb & SB & R)]]; [left; exact A| right; left; exact A| right; right].
    exists b. split; [| auto]. rewrite skipn_app. apply in_app_iff. left. exact Hb.
  Qed.

  #[using="Type"] Theorem D_apart : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pnb,(3.$4.)Pbl,(3.$4.)Pmo,$18.Pa,(1?.&40.)Pn,(1?.&40.)P,(19.R5.R4.R3.)P,(2.$20.(21.(7.(22.(1?.&40.)(1?.&40.))(23.(24.R4.))(25.(24.R4.)))R3.R2.)$26.)P,(13.+10000.(27.&40.R3.))P,(13.(15.(27.&40.R5.)(27.&40.R4.))(28.VhAR,))Px,$4.P,(0.(17.R:.R9.R1.)(1.(13.(29.VAL,)R1.)(14.R1.(2:.VAL,))))(1;.(1.(13.(27.&40.R8.)R2.)(14.R2.(15.(27.&40.R8.)(27.&40.R7.)))))")
(* [comment removed for export] *).
  Proof.
    intros nb bl mo a n K RF N16 CE x Hx. ddestruct (Kd_cases nb bl mo K) as (v & HK & EQ & _).
    apply (HKv_apart AL v mo a n HK RF N16 CE). destruct Hx as [Hx|Hx]; [left; apply EQ; exact Hx| right; exact Hx].
  Qed.

  #[using="ASB IML IMH SLACK"] Theorem D_T_node : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pnb,(3.$4.)Pbl,(3.$4.)Pmo,$18.Pa,(1?.&40.)P,(2;.R4.R3.)P,(19.R5.R4.R3.)P,(2.$4.(2<.(27.&40.R3.)+1000.)=)P,(14.=(27.&40.R4.))P,(13.(15.(27.&40.R5.)(;.+2.+14.))(28.VhAR,))P,(2.$20.(21.(7.(22.(1?.&40.)(1?.&40.))(23.(24.R7.))(25.(24.R7.)))R6.(2=.&40.(;.+2.+14.)))$26.)(1.(19.(7.$4.R:.(8.$4.(27.&40.R7.)(9.$4.)))R9.(2>.+22.R7.(;.+2.+14.)R8.))(2?.(17.(7.$4.R:.(8.$4.(27.&40.R7.)(9.$4.)))R9.)(27.&40.R7.)(;.+2.+14.)))")
(* [comment removed for export] *).
  Proof.
    intros nb bl mo a [-> ->] K AAL A0 ACE RF.
    destruct K as [(_ & _ & K)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]]; [| exfalso; symmetry in E; exact (app_cons_neq _ _ E)..].
    assert (N20 : bv_unsigned (Z_to_bv 64 (2^20)) = 2^20) by (apply u64_lit; lia).
    pose proof (HKv_fresh_above_img AL v0 mo a (Z_to_bv 64 (2^20)) K RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite N20; lia) ltac:(rewrite N20; exact ACE)) as IMA.
    pose proof (HKv_fresh_band AL v0 mo a (Z_to_bv 64 (2^20)) K RF ltac:(rewrite N20; lia)) as BND. rewrite N20 in BND.
    assert (SA : sane (2^20) (bv_unsigned a)) by (unfold sane; rewrite IMH in IMA; split; [lia| split; [lia| exact BND]]).
    split.
    - right. left. exists (bv_unsigned a). split; [reflexivity|]. split; [reflexivity|]. split; [exact SA|].
      unfold vN. apply (HKv_grant_eager AL v0 mo a (2^20) true K); try assumption; try (rewrite ASB; lia); try lia; try reflexivity.
      fold (vN (bv_unsigned a)). rewrite vnb_N. unfold RES_DEPOT in SLACK. lia.
    - intros z Hz. apply (proj2 (CSd_N (bv_unsigned a) z SA)). apply (proj2 (vcs_N _ _)). right. exact Hz.
  Qed.

  #[using="ASB IML IMH SLACK"] Theorem D_T_store : ltac2:(CDefT.buildp (gd_tbl_AInstDepot ()) "Pnb,(3.$4.)Pbl,(3.$4.)Pmo,$18.Pa,(1?.&40.)P,(30.R4.R3.)P,(19.R5.R4.R3.)P,(2.$4.(2<.(27.&40.R3.)+1000.)=)P,(14.=(27.&40.R4.))P,(13.(15.(27.&40.R5.)(;.+2.+17.))(28.VhAR,))P,(2.$20.(21.(7.(22.(1?.&40.)(1?.&40.))(23.(24.R7.))(25.(24.R7.)))R6.(2=.&40.(;.+2.+17.)))$26.)(1.(19.R:.(7.$4.R9.(8.$4.(27.&40.R7.)(9.$4.)))(2>.+4022.R7.(;.+2.+17.)R8.))(2?.(17.R:.(7.$4.R9.(8.$4.(27.&40.R7.)(9.$4.))))(27.&40.R7.)(;.+2.+17.)))")
(* [comment removed for export] *).
  Proof.
    intros nb bl mo a [-> GN] K AAL A0 ACE RF.
    assert (N23 : bv_unsigned (Z_to_bv 64 (2^23)) = 2^23) by (apply u64_lit; lia).
    destruct (Kd_cases _ _ mo K) as (v & HK & EQ & CASE).
    pose proof (HKv_fresh_above_img AL v mo a (Z_to_bv 64 (2^23)) HK RF A0 IML ltac:(rewrite IMH; lia) ltac:(rewrite N23; lia) ltac:(rewrite N23; exact ACE)) as IMA.
    pose proof (HKv_fresh_band AL v mo a (Z_to_bv 64 (2^23)) HK RF ltac:(rewrite N23; lia)) as BND. rewrite N23 in BND.
    assert (SB : sane (2^23) (bv_unsigned a)) by (unfold sane; rewrite IMH in IMA; split; [lia| split; [lia| exact BND]]).
    destruct CASE as [(E1 & _ & ->)|[(x & E1 & _ & SA & ->)|[(y & _ & E & _)|(x & y & _ & E & _)]]].
    3:{ exfalso. symmetry in E. exact (app_cons_neq _ _ E). } 3:{ exfalso. symmetry in E. exact (app_cons_neq _ _ E). }
    - subst nb. split.
      + right. right. left. exists (bv_unsigned a). split; [reflexivity|]. split; [reflexivity|]. split; [exact SB|].
        unfold vS. apply (HKv_grant_lazy AL v0 mo a (2^23) HK); try assumption; try (rewrite ASB; lia); try lia; try reflexivity.
        rewrite vnb_S. unfold RES_DEPOT in SLACK. lia.
      + intros z Hz. apply (proj2 (CSd_S (bv_unsigned a) z SB)). apply (proj2 (vcs_S _ _)). right. exact Hz.
    - subst nb. split.
      + right. right. right. dexists x, (bv_unsigned a). split; [reflexivity|]. split; [reflexivity|]. split; [exact SA|]. split; [exact SB|].
        unfold vNS. apply (HKv_grant_lazy AL (vN x) mo a (2^23) HK); try assumption; try (rewrite ASB; lia); try lia; try reflexivity.
        rewrite vnb_S, vnb_N, veb_N. unfold RES_DEPOT in SLACK. lia.
      + intros z Hz. apply (proj2 (CSd_NS x (bv_unsigned a) z SA SB)). apply (proj2 (vcs_NS _ _ _)). right. right. exact Hz.
  Qed.

  #[using="VR0 SLACK CB20"] Theorem D_ROOM_n : forall nb bl mo, Gn nb bl -> Kd nb bl mo -> exists a, anon_grantable 0x22 (2^20) mo a.
  Proof.
    intros nb bl mo [-> ->] K.
    destruct K as [(_ & _ & K)|[(x & E & _)|[(y & _ & E & _)|(x & y & E & _)]]]; [| exfalso; symmetry in E; exact (app_cons_neq _ _ E)..].
    apply (HKv_room20 AL v0 mo 0x22 VR0 K CB20). intros _. unfold RES_DEPOT in SLACK. lia.
  Qed.

  #[using="VR0 CB23"] Theorem D_ROOM_s : forall nb bl mo, Gs nb bl -> Kd nb bl mo -> exists a, anon_grantable 0x4022 (2^23) mo a.
  Proof.
    intros nb bl mo [-> GN] K. destruct (Kd_cases _ _ mo K) as (v & HK & EQ & CASE).
    destruct CASE as [(E1 & _ & ->)|[(x & E1 & _ & SA & ->)|[(y & _ & E & _)|(x & y & _ & E & _)]]].
    3:{ exfalso. symmetry in E. exact (app_cons_neq _ _ E). } 3:{ exfalso. symmetry in E. exact (app_cons_neq _ _ E). }
    - apply (HKv_room23 AL v0 mo 0x4022 VR0 HK); [lia| intros F; discriminate].
    - apply (HKv_room23 AL (vN x) mo 0x4022); [| exact HK| rewrite vcb23_N; exact CB23| intros F; discriminate].
      unfold vN, sane in *. apply vranges_ok_add_eager; [exact VR0| lia| lia].
  Qed.
End InstDepot.

End ARUN_1.
