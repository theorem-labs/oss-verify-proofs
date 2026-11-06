(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Specs Run.
From LinuxProcessSemantics.LinuxProcessSem.Sys.Mm Require Import Mmap Mprotect.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import RelSpec.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require Import SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KReach MReach.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_KCost () : Init.string Init.list := ["Stdlib.ZArith.BinInt.Z.le"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vmmaps"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.m_vm_materialized"; "kgrow"; "LinuxProcessSemantics.LinuxProcessSem.State.VmMaps"; "Stdlib.ZArith.BinInt.Z.of_nat"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.State.mkVmMapsFull"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_start_brk"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_mmap_base"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_init_sp"; "Corelib.Init.Datatypes.nil"; "OSSVerify.KrLib.Heap.KInv.vmwf"; "Stdlib.Lists.List.In"; "OSSVerify.KrLib.Heap.KInv.elo"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.KInv.ehi"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.maps_subtract"; "Corelib.Init.Datatypes.S"; "Corelib.Lists.ListDef.Forall"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Lib.ITree.resp"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "LinuxProcessSemantics.LinuxProcessSem.State.event"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_brk"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "OSSVerify.KrLib.Heap.Malloc.PGSZ"; "OSSVerify.KrLib.Lib.Nodes.nstep"; "OSSVerify.KrLib.Lib.Nodes.NBrk"; "emaps"; "OSSVerify.KrLib.Heap.Malloc.EBrk"; "ecost"; "OSSVerify.KrLib.Lib.Nodes.NMmap"; "OSSVerify.KrLib.Heap.KReach.MAPF_Z"; "OSSVerify.KrLib.Lib.Decode.mmap_len"; "Stdlib.ZArith.BinInt.Z.modulo"; "Stdlib.ZArith.BinInt.Z.add"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.State.map_contains"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_noaccess"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Init.Datatypes.true"; "OSSVerify.KrLib.Lib.Nodes.NMprotect"; "LinuxProcessSemantics.LinuxProcessSem.State.TASK_SIZE"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "OSSVerify.KrLib.Lib.Nodes.NMunmap"; "LinuxProcessSemantics.LinuxProcessSem.State.alloc_top"; "LinuxProcessSemantics.LinuxProcessSem.State.region_free"; "OSSVerify.KrLib.Heap.Malloc.PROT_NONE"; "OSSVerify.KrLib.Heap.KInv.MAPFX"; "OSSVerify.KrLib.Heap.KInv.KL"; "OSSVerify.KrLib.Heap.Prog.ps_brk"; "OSSVerify.KrLib.Heap.KInv.event_pre"; "eall"; "OSSVerify.KrLib.Heap.Prog.PState"; "OSSVerify.KrLib.Heap.Prog.ev_step"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record kgrow (K : nat) (C : Z) (mo mo' : Model) : Prop := mkKG {
  kg_C : 0 <= C;
  kg_mat : m_vm_materialized mo = [] -> m_vm_materialized mo' = [];
  kg_len : (length (kmaps mo') <= length (kmaps mo) + K)%nat;
  kg_resv : vm_reserved (m_vmmaps mo') = vm_reserved (m_vmmaps mo);
  kg_lim : vm_limit (m_vmmaps mo') = vm_limit (m_vmmaps mo);
  kg_live : vm_live_bytes (m_vmmaps mo') <= vm_live_bytes (m_vmmaps mo) + C;
  kg_size : forall S, C <= S -> Forall (fun p => bv_unsigned (snd p) <= S) (kmaps mo) -> Forall (fun p => bv_unsigned (snd p) <= S) (kmaps mo')
}.

Lemma kgrow_refl mo : kgrow 0 0 mo mo.
Proof. constructor; auto; lia. Qed.

Lemma kgrow_trans K1 C1 K2 C2 mo1 mo2 mo3 : kgrow K1 C1 mo1 mo2 -> kgrow K2 C2 mo2 mo3 -> kgrow (K1 + K2) (C1 + C2) mo1 mo3.
Proof.
  intros [A0 A1 A2 A3 A4 A5 A6] [B0 B1 B2 B3 B4 B5 B6]. constructor.
  - lia.
  - auto.
  - lia.
  - congruence.
  - congruence.
  - lia.
  - intros S HS HF. apply B6; [lia|]. apply A6; [lia| exact HF].
Qed.

Lemma kgrow_mono K C K' C' mo mo' : kgrow K C mo mo' -> (K <= K')%nat -> C <= C' -> kgrow K' C' mo mo'.
Proof. intros [A0 A1 A2 A3 A4 A5 A6] HK HC. constructor; auto; try lia. intros S HS. apply A6. lia. Qed.

Lemma kgrow_maps_eq K C mo mo' : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(0.=O3.)P,(1.(2.(3.(4.&40.)(4.&40.)))(5.(6.O1.))(5.(6.O2.)))P,(1.(2.(3.(4.&40.)(4.&40.)))(7.(6.O1.))(7.(6.O2.)))P,(1.$8.(9.(6.O1.))(9.(6.O2.)))P,(1.(2.(4.&40.))(:.O1.)(:.O2.))(;.O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. intros HC E1 E2 E3 E4. constructor; unfold kmaps, vm_live_bytes; rewrite ?E1, ?E2, ?E3, ?E4; auto; try lia. Qed.

Lemma kgrow_vm_eq K C mo mo' : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(0.=O3.)P,(1.$<.(6.O1.)(6.O2.))P,(1.(2.(4.&40.))(:.O1.)(:.O2.))(;.O4.O3.O2.O1.)")
(* [comment removed for export] *).
Proof. intros HC E1 E2. apply kgrow_maps_eq; rewrite ?E1; auto. Qed.

Lemma live_bytes_app l1 l2 : live_bytes (l1 ++ l2) = live_bytes l1 + live_bytes l2.
Proof. induction l1 as [|[a n] l1 IH]; [reflexivity|]. cbn [live_bytes app]. rewrite IH. lia. Qed.

(* [comment removed for export] *)
Lemma kgrow_cons K C mo mo' (a n : word) noacc brk : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(0.+1.(=.O8.))P,(0.(>.&40.O3.)O7.)P,(1.$<.(6.O5.)(?.(7.(6.O6.))(10.(3.(4.&40.)(4.&40.))(11.(4.&40.)(4.&40.)O4.O3.)(5.(6.O6.)))O2.(12.(6.O6.))O1.(9.(6.O6.))(13.(6.O6.))(14.(6.O6.))))P,P,(1.(2.(4.&40.))(:.O6.)(15.(4.&40.)))(1.(2.(4.&40.))(:.O5.)(15.(4.&40.)))(;.O8.O7.O6.O5.)")
(* [comment removed for export] *).
Proof.
  intros HK HC E HM. pose proof (u64_range n). constructor; unfold kmaps, vm_live_bytes; rewrite ?E; cbn [vm_reserved vm_maps vm_limit live_bytes]; auto; try lia.
  - rewrite !length_app. cbn [length]. lia.
  - intros S HS HF. apply Forall_app in HF as [F1 F2]. apply Forall_app. split; [exact F1|]. constructor; [cbn; lia| exact F2].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma map_remove_sub l (a : word) x : In x (map_remove l a) -> In x l.
Proof. unfold map_remove. intros H. apply filter_In in H. tauto. Qed.

Lemma map_remove_length l (a : word) : (length (map_remove l a) <= length l)%nat.
Proof. unfold map_remove. induction l as [|y l IH]; cbn; [lia|]. destruct (negb _); cbn; lia. Qed.

Lemma iv_subtract_length a sz lo hi : (length (iv_subtract a sz lo hi) <= 2)%nat.
Proof. unfold iv_subtract. destruct (_ <? _); destruct (_ <? _); cbn; lia. Qed.

Lemma maps_subtract_id l lo hi : vmwf l -> lo < hi -> (forall e, In e l -> ehi e <= lo \/ hi <= elo e) -> maps_subtract l lo hi = l.
Proof.
  induction l as [|[a sz] l IH]; intros [Hb Hp] Hlh Hd; [reflexivity|]. cbn [maps_subtract].
  rewrite iv_subtract_disjoint.
  - cbn. f_equal. apply IH; [| exact Hlh| intros e He; apply Hd; right; exact He].
    split; [intros e He; apply Hb; right; exact He| inversion Hp; assumption].
  - specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
  - exact Hlh.
  - specialize (Hd (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hd. cbn in Hd. lia.
Qed.

(* [comment removed for export] *)
Lemma maps_subtract_length_cover l lo hi e0 : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(16.O4.)P,(17.(3.(4.&40.)(4.&40.))O1.O4.)P,(0.(18.O1.)O3.)P,(19.O3.O2.)P,(0.O2.(1:.O1.))(1;.(1<.(3.(4.&40.)(4.&40.))(1=.O4.O3.O2.))(1>.(1<.(3.(4.&40.)(4.&40.))O4.)))")
(* [comment removed for export] *).
Proof.
  induction l as [|[a sz] l IH]; intros [Hb Hp] Hin H1 H2 H3; [destruct Hin|].
  inversion Hp as [|e l' Hd Hp']; subst. cbn [maps_subtract]. rewrite length_app. cbn [length].
  assert (Hwf' : vmwf l) by (split; [intros x Hx; apply Hb; right; exact Hx| exact Hp']).
  destruct Hin as [<-|Hin].
  - rewrite (maps_subtract_id l lo hi Hwf' H2).
    + pose proof (iv_subtract_length a sz lo hi). lia.
    + intros x Hx. specialize (Hd x Hx). unfold edisj in Hd. lia.
  - rewrite iv_subtract_disjoint; [cbn [length]| | exact H2|].
    + specialize (IH Hwf' Hin H1 H2 H3). lia.
    + specialize (Hb (a, sz) (or_introl eq_refl)). unfold elo, ehi in Hb. cbn in Hb. lia.
    + specialize (Hd e0 Hin). unfold edisj, elo, ehi in *. cbn in *. lia.
Qed.

Lemma maps_subtract_sizes l lo hi S : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(16.O4.)P,(1?.(3.(4.&40.)(4.&40.))Lp,(3.(4.&40.)(4.&40.))(0.(>.&40.(20.(4.&40.)(4.&40.)R1.))O1.)O4.)(1?.(3.(4.&40.)(4.&40.))Lp,(3.(4.&40.)(4.&40.))(0.(>.&40.(20.(4.&40.)(4.&40.)R1.))O1.)(1=.O4.O3.O2.))")
(* [comment removed for export] *).
Proof.
  intros [Hb _] HF. apply Forall_forall. intros x Hx. destruct (maps_subtract_In _ _ _ _ Hx) as ([a sz] & H0 & H1).
  pose proof (proj1 (List.Forall_forall _ _) HF _ H0) as B0. cbn in B0.
  specialize (Hb _ H0). unfold elo, ehi in Hb. cbn in Hb.
  dpose (iv_subtract_sub a sz lo hi x ltac:(lia) ltac:(lia) H1) as (X1 & X2 & X3). unfold elo, ehi in *. pose proof (u64_range (snd x)). lia.
Qed.

Lemma live_bytes_maps_subtract_le' l lo hi : vmwf l -> lo < hi -> live_bytes (maps_subtract l lo hi) <= live_bytes l.
Proof. intros _ H. apply live_bytes_maps_subtract_le. lia. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Fixpoint tall {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
  match t with
  | Ret r => P r mo
  | Vis n k => forall rsp mo' evs, nstep n mo rsp mo' evs -> tall (k rsp) mo' P
  end.

Definition eall {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  tall t mo (fun r mo' => match r with Unr => True | Ok a => Q a mo' end).

Lemma tall_mono {R} (t : itree node R) mo (P P' : R -> Model -> Prop) :
  tall t mo P -> (forall r mo', P r mo' -> P' r mo') -> tall t mo P'.
Proof. revert mo. induction t as [r|n k IH]; intros mo H HP; cbn in *; [auto|]. intros rsp mo' evs Hst. eapply IH; eauto. Qed.

Lemma tall_bind {A B} (t : itree node A) (f : A -> itree node B) mo (P1 : A -> Model -> Prop) P :
  tall t mo P1 -> (forall a mo1, P1 a mo1 -> tall (f a) mo1 P) -> tall (ITree.bind node t f) mo P.
Proof. revert mo. induction t as [r|n k IH]; intros mo H Hf; cbn in *; [auto|]. intros rsp mo' evs Hst. eapply IH; eauto. Qed.

Lemma eall_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q1 Q :
  eall t mo Q1 -> (forall a mo1, Q1 a mo1 -> eall (f a) mo1 Q) -> eall (ebind t f) mo Q.
Proof.
  intros H Hf. unfold eall, ebind in *. eapply tall_bind; [exact H|]. cbn beta. intros [|a] mo1 Ha; [exact I| apply Hf; exact Ha].
Qed.

Lemma eall_twf_conj {A} (t : itree node (exc A)) mo Q Q' : eall t mo Q -> etwf t mo Q' -> etwf t mo (fun a mo' => Q a mo' /\ Q' a mo').
Proof.
  revert mo. unfold eall, etwf. induction t as [r|n k IH]; intros mo H W; cbn in *.
  - destruct r; auto.
  - destruct W as [Hs W]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH; eauto.
Qed.

Lemma eall_conj_twf {A} (t : itree node (exc A)) mo Q Q' : eall t mo Q -> etwf t mo Q' -> eall t mo (fun a mo' => Q a mo' /\ Q' a mo').
Proof.
  revert mo. unfold eall, etwf. induction t as [r|n k IH]; intros mo H W; cbn in *.
  - destruct r; auto.
  - destruct W as [Hs W]. intros rsp mo' evs Hst. apply IH; eauto.
Qed.

Lemma eall_mono {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop) :
  eall t mo Q -> (forall a mo', Q a mo' -> Q' a mo') -> eall t mo Q'.
Proof. intros H HQ. eapply tall_mono; [exact H|]. cbn beta. intros [|a] mo'; auto. Qed.

Section MonadForms.
Context {St : Type}.
#[using="Type"] Lemma eall_mbind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo Q1 Q :
  eall (m s) mo Q1 -> (forall a s1 mo1, Q1 (a, s1) mo1 -> eall (f a s1) mo1 Q) -> eall (mbind m f s) mo Q.
Proof. intros H Hf. unfold mbind. eapply eall_ebind; [exact H|]. intros [a s1] mo1 HQ. apply Hf. exact HQ. Qed.
#[using="Type"] Lemma eall_mret {A} (a : A) s mo (Q : A * St -> Model -> Prop) : Q (a, s) mo -> eall (mret a s) mo Q.
Proof. intros H. exact H. Qed.
#[using="Type"] Lemma eall_munr {A} s mo (Q : A * St -> Model -> Prop) : eall (munr s) mo Q.
Proof. exact I. Qed.
#[using="Type"] Lemma eall_msys {A} n (dec : resp -> option A) s mo (Q : A * St -> Model -> Prop) :
  (forall rsp mo' evs a, nstep n mo rsp mo' evs -> dec rsp = Some a -> Q (a, s) mo') -> eall (msys n dec s) mo Q.
Proof.
  intros H. unfold eall, msys, enode. cbn. intros rsp mo' evs Hst. destruct (dec rsp) as [a|] eqn:E; cbn; [| exact I]. eapply H; eauto.
Qed.
End MonadForms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma m_vmmaps_vm_forget_range lo hi m : m_vmmaps (vm_forget_range lo hi m) = m_vmmaps m.
Proof. reflexivity. Qed.
Lemma m_vm_materialized_vm_forget_range lo hi m :
  m_vm_materialized m = [] -> m_vm_materialized (vm_forget_range lo hi m) = [].
Proof. intros H. unfold vm_forget_range, with_vm_backing. cbn. rewrite H. reflexivity. Qed.
Lemma m_vm_materialized_forget_vm_ranges rs m :
  m_vm_materialized m = [] -> m_vm_materialized (forget_vm_ranges rs m) = [].
Proof.
  revert m. induction rs as [|[a n] rs IH]; intros m H; cbn [forget_vm_ranges]; [exact H|].
  apply IH. apply m_vm_materialized_vm_forget_range. exact H.
Qed.
Lemma m_vmmaps_forget_vm_ranges' rs m : m_vmmaps (forget_vm_ranges rs m) = m_vmmaps m.
Proof. revert m. induction rs as [|[a n] rs IH]; intros m; cbn [forget_vm_ranges]; [reflexivity|]. rewrite IH. reflexivity. Qed.

(* [comment removed for export] *)
Definition ecost (e : ev) : Z :=
  match e with
  | EBrk req => if req =? 0 then 0 else 3 * PGSZ
  | EMmap _ len _ _ => mmap_len len
  | _ => 0
  end.
Definition emaps (e : ev) : nat :=
  match e with
  | EBrk req => if req =? 0 then 0%nat else 1%nat
  | EMmap _ _ _ _ => 1%nat
  | _ => 0%nat
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EV.
Variable L : mled.
Variable G : PState -> Model -> Prop.
Variable s : PState.
Variable mo : Model.
Hypothesis HK : KL L (ps_brk s) mo.

#[using="Type"] Lemma kg_same K C mo' : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(0.=O2.)P,(1.$<.(6.O1.)(6.Vmo,))P,(1.(2.(4.&40.))(:.O1.)(:.Vmo,))(;.O3.O2.Vmo,O1.)")
(* [comment removed for export] *).
Proof. intros. apply kgrow_vm_eq; auto. Qed.

(* [comment removed for export] *)
#[using="L s HK"] Lemma brk_kgrow req : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "Prsp,$21.Pmo',$22.Pevs,(2.$23.)P,(24.(0.=O1.)(19.O1.(25.+2.+40.)))P,(26.(1.$8.O1.=)(24.(0.(>.&40.(27.(6.Vmo,)))O1.)(0.(28.O1.(>.&40.(27.(6.Vmo,))))(29.+3.$2:.))))P,(2;.(2<.O1.)Vmo,R5.R4.R3.)(;.(2=.(2>.O1.))(2?.(2>.O1.))Vmo,R5.)")
(* [comment removed for export] *).
Proof.
  intros rsp mo' evs Hreq Hcase Hst.
  destruct (Decode.nstep_brk_inv _ _ _ _ _ Hst) as (r & Hok & Emo & _ & _). subst mo'.
  pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (u64_range (vm_brk (m_vmmaps mo))) as Hb. pose proof (u64_range r) as Hr.
  assert (Ureq : bv_unsigned (Z_to_bv 64 req) = req) by (apply unsigned_lit; lia).
  assert (SAME : r = vm_brk (m_vmmaps mo) -> kgrow (emaps (EBrk req)) (ecost (EBrk req)) mo (with_brk_next mo (Z_to_bv 64 req) r)).
  { intros ->. dpose (with_brk_next_same mo (Z_to_bv 64 req)) as (E1 & E2 & _). apply kg_same; [| exact E1| exact E2].
    unfold ecost, PGSZ. destruct (req =? 0); lia. }
  unfold brk_r_ok in Hok.
  destruct (w_is0 (Z_to_bv 64 req) || (bv_unsigned (Z_to_bv 64 req) <? bv_unsigned (min_brk (m_vmmaps mo)))) eqn:E1.
  { apply bv_eqb_eq in Hok. apply SAME. exact Hok. }
  rewrite Ureq in Hok. apply orb_false_iff in E1 as [E1 E1']. rewrite Ureq in E1'.
  assert (Hne : req <> 0). { intros ->. unfold w_is0, bv_eqb in E1. cbn in E1. discriminate. }
  destruct Hcase as [Hc|[Hc Hc3]]; [lia|].
  rewrite (proj2 (Z.ltb_ge _ _) Hc) in Hok. apply andb_prop in Hok as [Hok _].
  apply orb_prop in Hok as [Hok|Hok]; apply bv_eqb_eq in Hok; [| apply SAME; exact Hok]. subst r.
  destruct (Z.eq_dec req (bv_unsigned (vm_brk (m_vmmaps mo)))) as [Ereq|NE].
  { apply SAME. rewrite Ereq. apply Z_to_bv_bv_unsigned. }
  (* [comment removed for export] *)
  unfold with_brk_next. rewrite (brk_unmaps_nogrow (Z_to_bv 64 req) (vm_brk (m_vmmaps mo))) by (rewrite Ureq; lia). cbn [forget_vm_ranges].
  unfold emaps, ecost. rewrite (proj2 (Z.eqb_neq _ _) Hne).
  eapply (kgrow_cons 1%nat (3 * PGSZ) mo _ (vm_brk (m_vmmaps mo)) (Z_to_bv 64 req - vm_brk (m_vmmaps mo))%bv (maps_subtract_ranges (vm_noaccess (m_vmmaps mo)) (brk_unmaps (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))) (Z_to_bv 64 req)); [lia| | | intros M; exact M].
  - rewrite bv_sub_unsigned, Ureq, bv_wrap_small by (unfold bv_modulus; lia). lia.
  - rewrite m_vmmaps_with_vmmaps. unfold brk_model_next, brk_maps_next, brk_grants, brk_is_grow.
    rewrite Ureq, E1. cbn [negb andb]. rewrite (proj2 (Z.ltb_ge req (bv_unsigned (vm_brk (m_vmmaps mo))))) by lia. rewrite andb_false_r.
    rewrite (proj2 (Z.ltb_lt 0 _)) by lia. rewrite (proj2 (Z.ltb_lt _ req)) by lia. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mmap_kgrow len prot : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "Prsp,$21.Pmo',$22.Pevs,(2.$23.)P,(24.(19.=O2.)(19.O2.(25.+2.+3?.)))P,(26.(1.$8.O1.=)(1.$8.O1.+3.))P,(2;.(30.=O2.O1.$31.)Vmo,R5.R4.R3.)(;.#1.(32.O2.)Vmo,R5.)")
(* [comment removed for export] *).
Proof.
  intros rsp mo' evs Hlen0 Hprot Hst. assert (Hlen : 0 < len < 2 ^ 64) by lia.
  pose proof (mmap_len_bound len ltac:(lia)) as Hml.
  apply (proj1 (nstep_mm_iff (NMmap 0 len prot MAPF_Z) _ mo rsp mo' evs eq_refl I)) in Hst as [-> Hsp].
  apply (proj1 (syscall_spec_222 _ _ _ ltac:(rewrite in_sysno_pure; apply unsigned_lit; lia))) in Hsp.
  cbn [in_arg pure_input in_args nth] in Hsp.
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  destruct Hprot as [-> | ->].
  - apply (proj1 (mmap_noaccess_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len Hlen) mmap_off0 mmap_anon_MAPF mmap_modeled_none mmap_noaccess_none)) in Hsp.
    destruct Hsp as [(e & He & E)|(a & _ & E)]; apply Ok_inj in E as (E1 & Emo & _); subst mo'.
    + apply kg_same; [lia| reflexivity| reflexivity].
    + unfold with_mmap_backing. rewrite mmap_noreserve_MAPF. rewrite Ulen. fold (mmap_len len).
      eapply (kgrow_cons 1%nat (mmap_len len) mo _ a (Z_to_bv 64 (mmap_len len))); [lia| rewrite unsigned_lit by lia; lia| reflexivity| intros M; exact M].
  - apply (proj1 (mmap_rw_outcome _ _ _ _ _ _ _ mo _ (w_is0_false len Hlen) mmap_off0 mmap_anon_MAPF mmap_modeled_rw)) in Hsp.
    destruct Hsp as [(e & He & E)|(a & _ & E)]; apply Ok_inj in E as (E1 & Emo & _); subst mo'.
    + apply kg_same; [lia| reflexivity| reflexivity].
    + unfold with_mmap_backing. rewrite mmap_noreserve_MAPF. rewrite Ulen. fold (mmap_len len).
      eapply (kgrow_cons 1%nat (mmap_len len) mo _ a (Z_to_bv 64 (mmap_len len))); [lia| rewrite unsigned_lit by lia; lia| reflexivity| intros M; exact M].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma mprotect_kgrow (a : Z) : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "Prsp,$21.Pmo',$22.Pevs,(2.$23.)P,(0.=O1.)P,(1.$8.(33.O1.+1000.)=)P,(19.(34.O1.+1000.)(25.+2.+40.))P,(1.$35.(36.(37.(6.Vmo,))(38.&40.O1.)(38.&40.+1000.))$39.)P,(1.$35.(36.(5.(6.Vmo,))(38.&40.O1.)(38.&40.+1000.))$39.)P,(2;.(3:.O1.+1000.+3.)Vmo,R8.R7.R6.)(;.#0.=Vmo,R8.)")
(* [comment removed for export] *).
Proof.
  intros rsp mo' evs Ha Hal Hhi Hna Hma Hst.
  set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 4096) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Un : bv_unsigned nw = 4096) by (subst nw; apply unsigned_lit; lia).
  apply (proj1 (nstep_mm_iff (NMprotect a 4096 3) _ mo rsp mo' evs eq_refl I)) in Hst as [-> Hsp].
  apply (proj1 (syscall_spec_226 _ _ _ ltac:(rewrite in_sysno_pure; apply unsigned_lit; lia))) in Hsp.
  cbn [in_arg pure_input in_args nth] in Hsp. fold aw nw in Hsp.
  assert (E4 : Z_to_bv 64 (page_round_up_Z (bv_unsigned nw)) = nw) by (rewrite Un; reflexivity).
  apply (proj1 (mprotect_expose_outcome aw nw (Z_to_bv 64 3) _ mo _ ltac:(vm_compute; reflexivity)
             ltac:(rewrite Ua; unfold page_size; exact Hal) ltac:(subst nw; apply w_is0_false; lia)
             ltac:(rewrite Ua, Un; change (page_round_up_Z 4096) with 4096; unfold two_pow_64; lia)
             ltac:(vm_compute; reflexivity) ltac:(rewrite E4; exact Hna) ltac:(rewrite E4; exact Hma))) in Hsp.
  destruct Hsp as [(e & He & E)|(Hb & E)]; apply Ok_inj in E as (E1 & Emo & _); subst mo'.
  - apply kg_same; [lia| reflexivity| reflexivity].
  - apply kgrow_maps_eq; [lia| reflexivity| reflexivity| reflexivity| reflexivity].
Qed.

(* [comment removed for export] *)
#[using="L s HK"] Lemma munmap_kgrow (a len : Z) : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "Prsp,$21.Pmo',$22.Pevs,(2.$23.)P,(0.=O2.)P,(1.$8.(33.O2.+1000.)=)P,(19.=O1.)P,(0.(34.O2.(32.O1.))$3;.)P,(1.$35.(3<.(5.(6.Vmo,))(38.&40.O2.)(38.&40.(32.O1.)))$39.)P,(2;.(3=.O2.O1.)Vmo,R8.R7.R6.)(;.#0.=Vmo,R8.)")
(* [comment removed for export] *).
Proof.
  intros rsp mo' evs Ha Hal Hlen Hts Hhas Hst.
  pose proof (mmap_len_bound len Hlen) as Hml.
  assert (Hhi : a + mmap_len len < 2 ^ 64) by (unfold TASK_SIZE in Hts; lia).
  set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 (mmap_len len)) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; lia).
  assert (Ulen : bv_unsigned (Z_to_bv 64 len) = len) by (apply unsigned_lit; lia).
  apply (proj1 (nstep_mm_iff (NMunmap a len) _ mo rsp mo' evs eq_refl I)) in Hst as [-> Hsp].
  apply (proj1 (syscall_spec_215 _ _ _ ltac:(rewrite in_sysno_pure; apply unsigned_lit; lia))) in Hsp.
  cbn [in_arg pure_input in_args nth] in Hsp. fold aw in Hsp.
  pose proof (munmap_exact_outcome aw (Z_to_bv 64 len) (pure_input 215 [aw; Z_to_bv 64 len]) mo (Monad.Ok rsp mo' [])
                ltac:(rewrite Ua; unfold page_size; exact Hal) (w_is0_false len ltac:(lia))
                ltac:(rewrite Ua, Ulen; fold (mmap_len len); exact Hts)) as X.
  cbv zeta in X. rewrite Ulen in X. fold (mmap_len len) in X. fold nw in X.
  apply (proj1 (X Hhas)) in Hsp. clear X. apply Ok_inj in Hsp as (_ & Emo & _). subst mo'.
  unfold with_mmap_destroyed. pose proof (kl_wf _ _ _ HK) as WF.
  constructor; unfold kmaps, vm_live_bytes; rewrite ?m_vmmaps_vm_forget_range, ?m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_limit]; try lia; try reflexivity.
  - intros M. apply m_vm_materialized_vm_forget_range. exact M.
  - rewrite !length_app. pose proof (map_remove_length (vm_maps (m_vmmaps mo)) aw). lia.
  - pose proof (live_bytes_map_remove_le (vm_maps (m_vmmaps mo)) aw). lia.
  - intros S HS HF. apply Forall_app in HF as [F1 F2]. apply Forall_app. split; [exact F1|].
    apply Forall_forall. intros x Hx. apply map_remove_sub in Hx. exact (proj1 (List.Forall_forall _ _) F2 _ Hx).
Qed.

(* [comment removed for export] *)
#[using="L s HK"] Lemma mmap_fixed_kgrow (a : Z) e0 : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "Prsp,$21.Pmo',$22.Pevs,(2.$23.)P,(19.=O2.)P,(1.$8.(33.O2.+1000.)=)P,(0.(34.O2.$2:.)(3>.(6.Vmo,)))P,(1.$35.(3?.(7.(6.Vmo,))(38.&40.O2.)(38.&40.$2:.))$39.)P,(17.(3.(4.&40.)(4.&40.))O1.(5.(6.Vmo,)))P,(0.(18.O1.)O2.)P,(0.(34.O2.$2:.)(1:.O1.))P,(2;.(30.O2.$2:.$40.$41.)Vmo,R:.R9.R8.)(;.#1.$2:.Vmo,R:.)")
(* [comment removed for export] *).
Proof.
  intros rsp mo' evs Ha Hal Hce Hrf Hin Hlo Hhi Hst. pose proof (alloc_top_lt (m_vmmaps mo)) as Hcl. unfold two_pow_64 in Hcl.
  set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
  assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
  assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
  assert (Hmc : map_contains (vm_maps (m_vmmaps mo)) aw nw = true).
  { unfold map_contains. apply existsb_exists. exists e0. split; [exact Hin|]. rewrite Ua, Un. unfold elo, ehi in *.
    rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
  apply (proj1 (nstep_mm_iff (NMmap a PGSZ PROT_NONE MAPFX) _ mo rsp mo' evs eq_refl I)) in Hst as [-> Hsp].
  apply (proj1 (syscall_spec_222 _ _ _ ltac:(rewrite in_sysno_pure; apply unsigned_lit; lia))) in Hsp.
  cbn [in_arg pure_input in_args nth] in Hsp. fold aw nw in Hsp.
  assert (E4 : Z_to_bv 64 (page_round_up_Z (bv_unsigned nw)) = nw) by (rewrite Un; reflexivity).
  pose proof (mmap_fixed_noaccess_outcome aw nw (Z_to_bv 64 PROT_NONE) (Z_to_bv 64 MAPFX) (Z_to_bv 64 (-1)) (Z_to_bv 64 0)
                (pure_input 222 [aw; nw; Z_to_bv 64 PROT_NONE; Z_to_bv 64 MAPFX; Z_to_bv 64 (-1); Z_to_bv 64 0]) mo (Monad.Ok rsp mo' [])
                ltac:(subst nw; apply w_is0_false; unfold PGSZ; lia) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)
                ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as X.
  cbv zeta in X. rewrite E4, Ua, Un in X. change (page_round_up_Z PGSZ) with PGSZ in X.
  apply (proj1 (X Hce ltac:(unfold page_size; exact Hal) Ha Hrf Hmc)) in Hsp. clear X.
  pose proof (kl_wf _ _ _ HK) as WF.
  destruct Hsp as [(e & He & E)|[E|(e & He & E & _)]]; apply Ok_inj in E as (_ & Emo & _); subst mo'.
  - apply kg_same; [unfold PGSZ; lia| reflexivity| reflexivity].
  - unfold with_mmap_replacement, with_mmap_backing. replace (mmap_noreserve_b (Z_to_bv 64 MAPFX)) with false by (vm_compute; reflexivity).
    constructor; unfold kmaps, vm_live_bytes; rewrite ?m_vmmaps_vm_forget_range, ?m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_limit]; try (unfold PGSZ; lia); try reflexivity.
    + intros M. apply m_vm_materialized_vm_forget_range. exact M.
    + intros S HS HF. exact HF.
  - (* [comment removed for export] *)
    unfold with_mmap_destroyed, mmap_fixed_destroyed_next. rewrite Ua, Un.
    constructor; unfold kmaps, vm_live_bytes; rewrite ?m_vmmaps_vm_forget_range, ?m_vmmaps_with_vmmaps; cbn [vm_reserved vm_maps vm_limit]; try (unfold PGSZ; lia); try reflexivity.
    + intros M. apply m_vm_materialized_vm_forget_range. exact M.
    + rewrite !length_app. pose proof (maps_subtract_length_cover (vm_maps (m_vmmaps mo)) a (a + PGSZ) e0 WF Hin Hlo ltac:(unfold PGSZ; lia) Hhi). lia.
    + pose proof (live_bytes_maps_subtract_le (vm_maps (m_vmmaps mo)) a (a + PGSZ) ltac:(unfold PGSZ; lia)). unfold PGSZ in *. lia.
    + intros S HS HF. apply Forall_app in HF as [F1 F2]. apply Forall_app. split; [exact F1|].
      exact (maps_subtract_sizes _ _ _ _ WF F2).
Qed.

End EV.

Lemma round_up_pg_bound' x : x <= round_up_pg x <= x + 4095.
Proof.
  unfold round_up_pg, PGSZ. change (4096 - 1) with 4095. rewrite KArith.land_4095.
  pose proof (Z.mod_pos_bound (-x) 4096 ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma ev_kgrow L e s mo : ltac2:(CDefT.buildp (gd_tbl_KCost ()) "P,(42.O4.(43.O2.)O1.)P,(44.O4.O3.)(45.(3.$8.$46.)(47.O3.O2.)O1.L,(3.$8.$46.)Lmo',$22.(;.(2=.O3.)(2?.O3.)O1.R1.))")
(* [comment removed for export] *).
Proof.
  intros HK Hpre. pose proof (kl_start _ _ _ HK) as (S1 & S2 & S3 & S4). pose proof (ld_ceil_lt63 _ _ _ HK) as Hcl.
  pose proof (kl_ceil _ _ _ HK) as Kcl. pose proof (kl_ceil_ok _ _ _ HK) as [Kclo Kchi]. unfold ALLOC_CEIL_LO in Kclo. unfold ALLOC_CEIL_HI in Kchi.
  destruct e as [req|a len prot flags|a len|a len prot|? ? ?|?]; cbn [event_pre] in Hpre; try contradiction.
  - (* [comment removed for export] *)
    assert (Hcase : 0 <= req < 2 ^ 64 /\ (req = 0 \/ bv_unsigned (vm_brk (m_vmmaps mo)) <= req /\ req - bv_unsigned (vm_brk (m_vmmaps mo)) <= 3 * PGSZ)).
    { pose proof (kl_phase _ _ _ HK) as PH.
      destruct Hpre as [[-> _]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]]; [lia| |].
      - rewrite Hph in PH. ddestruct PH as (-> & Hb & _). pose proof (round_up_pg_bound' (bv_unsigned (vm_start_brk (m_vmmaps mo)))). unfold PGSZ in *. lia.
      - rewrite Hph in PH. ddestruct PH as (b' & l' & Hreg' & Hb & _). rewrite Hreg in Hreg'. injection Hreg' as <- <-.
        pose proof (kl_brkreg _ _ _ HK b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _). unfold PGSZ in *. lia. }
    destruct Hcase as [Hreq Hcase].
    unfold ev_step. destruct (Z.eqb_spec req 0) as [->|Hne].
    + eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow (emaps (EBrk 0)) (ecost (EBrk 0)) mo mo'));
        [apply eall_msys; intros rsp mo' evs r Hst _; exact (brk_kgrow L s mo HK 0 rsp mo' evs Hreq Hcase Hst)|].
      cbn beta. intros r s1 mo1 KG. exact KG.
    + change (mbind mget ?f s) with (f s s).
      eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow (emaps (EBrk req)) (ecost (EBrk req)) mo mo'));
        [apply eall_msys; intros rsp mo' evs r Hst _; exact (brk_kgrow L s mo HK req rsp mo' evs Hreq Hcase Hst)|].
      cbn beta. intros [|] s1 mo1 KG; exact KG.
  - (* [comment removed for export] *)
    destruct Hpre as [(Hq & -> & -> & Hprot & Hlen)|(cur & Hph & -> & -> & -> & ->)].
    + unfold ev_step. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
      assert (Hprot' : prot = 0 \/ prot = 3) by (destruct Hprot as [-> | ->]; [left|right]; reflexivity).
      unfold LEN_MAX in Hlen.
      destruct (prot =? 0);
        (eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow 1%nat (mmap_len len) mo mo'));
         [apply eall_msys; intros rsp mo' evs r Hst _; exact (mmap_kgrow mo len prot rsp mo' evs Hlen Hprot' Hst)|];
         cbn beta; intros r s1 mo1 KG; exact KG).
    + (* [comment removed for export] *)
      pose proof (kl_phase _ _ _ HK) as PH. rewrite Hph in PH. ddestruct PH as (Ecur & Ebrk & Epbrk & Ereg & Hceil & (e0 & He0 & He0l & He0h) & _).
      assert (Ha : round_up_pg cur = cur) by (apply round_up_pg_aligned; rewrite Ecur; exact S2).
      unfold ev_step. change (Z.land MAPFX MAP_FIXED_Z =? 0) with false. cbn [negb].
      eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow 1%nat (mmap_len PGSZ) mo mo')); [apply eall_msys; intros rsp mo' evs r Hst _|].
      * change (mmap_len PGSZ) with PGSZ.
        apply (mmap_fixed_kgrow L s mo HK (round_up_pg cur) e0 rsp mo' evs); rewrite ?Ha.
        -- lia.
        -- rewrite Ecur. exact S2.
        -- rewrite <- Kcl. lia.
        -- apply region_free_above. intros e He. rewrite unsigned_lit by (unfold PGSZ in *; lia). rewrite Ecur. apply (kl_resv_top _ _ _ HK). exact He.
        -- exact He0.
        -- exact He0l.
        -- unfold PGSZ in *; lia.
        -- rewrite <- Ha at 1. exact Hst.
      * cbn beta. intros r s1 mo1 KG. exact KG.
  - (* [comment removed for export] *)
    ddestruct Hpre as (Hq & l0 & Hin & Hlen).
    pose proof (kl_groups _ _ _ HK a l0 Hin) as (A1 & A2 & A3 & A4 & A5 & A6).
    rewrite round_up_pg_eq in Hlen. fold (mmap_len l0) in Hlen.
    assert (Hnn : mmap_len (mmap_len l0) = mmap_len l0) by (apply mmap_len_of_aligned; [pose proof (mmap_len_bound l0 ltac:(lia)); lia| apply mmap_len_aligned]).
    assert (Hlen3 : 0 < len /\ mmap_len len = mmap_len l0).
    { destruct Hlen as [-> | ->]; [split; [lia| reflexivity]| split; [pose proof (mmap_len_bound l0 ltac:(lia)); lia| exact Hnn]]. }
    destruct Hlen3 as [Hlen1 Hlen2].
    unfold ev_step.
    eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow 0%nat 0 mo mo')); [apply eall_msys; intros rsp mo' evs r Hst _|].
    + apply (munmap_kgrow L s mo HK a len rsp mo' evs); try lia.
      * unfold PGSZ in A3. exact A3.
      * rewrite Hlen2. unfold TASK_SIZE. lia.   (* [comment removed for export] *)
      * rewrite Hlen2. unfold map_has. apply existsb_exists. exists (went a (mmap_len l0)). split; [exact A5|]. unfold went, wz. cbn [fst snd]. rewrite !bv_eqb_refl. reflexivity.
      * exact Hst.
    + cbn beta. intros r s1 mo1 KG. exact KG.
  - (* [comment removed for export] *)
    ddestruct Hpre as (Hq & -> & -> & b & l & k & Hin & -> & Hk2).
    rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
    pose proof (kl_metas _ _ _ HK b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HK (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    set (nb := mmap_len l) in *. set (a := b + (1 + k) * PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Ua : bv_unsigned (Z_to_bv 64 a) = a) by (apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned (Z_to_bv 64 4096) = 4096) by (apply unsigned_lit; lia).
    assert (Hcn : map_contains (vm_noaccess (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 4096) = true).
    { ddestruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    assert (Hcm : map_contains (vm_maps (m_vmmaps mo)) (Z_to_bv 64 a) (Z_to_bv 64 4096) = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    unfold ev_step. change PGSZ with 4096. change PROT_RW with 3.
    eapply (eall_mbind _ _ s mo (fun _ mo' => kgrow 0%nat 0 mo mo')); [apply eall_msys; intros rsp mo' evs r Hst _|].
    + apply (mprotect_kgrow mo a rsp mo' evs); [unfold PGSZ in *; lia| exact Hamod| unfold PGSZ in *; lia| exact Hcn| exact Hcm| exact Hst].
    + cbn beta. intros r s1 mo1 KG. exact KG.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive sall {R} (Q : R -> Prop) : nat -> Z -> stree ev Z R -> Prop :=
| sa_ret K C r : Q r -> 0 <= C -> sall Q K C (SRet r)
| sa_undef K C u k : 0 <= C -> sall Q K C (SVis (EUndef u) k)
| sa_vis K C e k : 0 <= C -> 0 <= ecost e <= 2 ^ 35 -> (forall z, sall Q K C (k z)) -> sall Q (K + emaps e)%nat (C + ecost e) (SVis e k).

Lemma sall_C_nonneg {R} Q K C (t : stree ev Z R) : sall Q K C t -> 0 <= C.
Proof. intros H. destruct H; lia. Qed.

Lemma sall_mono {R} (Q Q' : R -> Prop) K C K' C' (t : stree ev Z R) :
  sall Q K C t -> (forall r, Q r -> Q' r) -> (K <= K')%nat -> C <= C' -> sall Q' K' C' t.
Proof.
  intros H HQ. revert K' C'. induction H as [K C r Hr HC|K C u k HC|K C e k HC He Hk IH]; intros K' C' LK LC.
  - constructor; auto; lia.
  - constructor; lia.
  - replace K' with ((K' - emaps e) + emaps e)%nat by lia. replace C' with ((C' - ecost e) + ecost e) by lia.
    apply sa_vis; [lia| exact He|]. intros z. apply (IH z); lia.
Qed.

Lemma sall_bind {R S} (Q1 : R -> Prop) (Q : S -> Prop) K1 C1 K2 C2 (t : stree ev Z R) (f : R -> stree ev Z S) :
  sall Q1 K1 C1 t -> 0 <= C2 -> (forall r, Q1 r -> sall Q K2 C2 (f r)) -> sall Q (K1 + K2)%nat (C1 + C2) (sbind t f).
Proof.
  intros H HC2 Hf. induction H as [K C r Hr HC|K C u k HC|K C e k HC He Hk IH]; cbn [sbind].
  - eapply sall_mono; [apply Hf; exact Hr| auto| lia| lia].
  - constructor. lia.
  - replace (K + emaps e + K2)%nat with ((K + K2) + emaps e)%nat by lia. replace (C + ecost e + C2) with ((C + C2) + ecost e) by lia.
    apply sa_vis; [lia| exact He|]. intros z. apply IH.
Qed.

Lemma sall_guard {R} Q K C tag (c : bool) (k bail : stree ev Z R) :
  0 <= C -> (c = true -> sall Q K C k) -> sall Q K C (guard tag c k bail).
Proof. intros HC H. unfold guard. destruct c; [apply H; reflexivity| constructor; exact HC]. Qed.

Lemma sall_bad_answer {R} Q K C (bail : stree ev Z R) : 0 <= C -> sall Q K C (bad_answer bail).
Proof. intros HC. unfold bad_answer. constructor. exact HC. Qed.

(* [comment removed for export] *)
Theorem membed_kall {R} (Q : R -> Prop) G : frame_ok G -> forall (t : stree ev Z R) K C L (Post : mled -> R -> Prop) s mo,
  sall Q K C t -> ctree_ok L t Post -> KL L (ps_brk s) mo -> G s mo ->
  eall (membed t s) mo (fun p mo' => Q (fst p) /\ kgrow K C mo mo'
                        /\ exists L', cpath L t L' (fst p) /\ Post L' (fst p) /\ KL L' (ps_brk (snd p)) mo' /\ G (snd p) mo'
                        /\ ps_m (snd p) = ps_m s /\ ps_fa (snd p) = ps_fa s /\ ps_so (snd p) = ps_so s).
Proof.
  intros HG t K C L Post s mo H. revert L s mo.
  induction H as [K C r Hr HC|K C u k HC|K C e k HC He Hk IH]; intros L s mo Hok HKL HGs.
  - cbn [membed]. apply eall_mret. cbn [fst snd]. split; [exact Hr|]. split; [eapply kgrow_mono; [apply kgrow_refl| lia| lia]|].
    exists L. split; [constructor|]. cbn in Hok. split; [exact Hok|]. split; [exact HKL|]. split; [exact HGs|]. split; [reflexivity| split; reflexivity].
  - cbn [membed ev_step]. rewrite mbind_munr. exact I.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hok].
    assert (W : etwf (ev_step e s) mo (fun p mo' => ev_step_post L e G s (fst p) (snd p) mo')) by (apply (ev_step_spec L e G s HG Hpre); auto).
    eapply eall_mbind; [eapply eall_conj_twf; [apply (ev_kgrow L e s mo HKL Hpre)| exact W]|].
    cbn beta. (intros z s1 mo1 dd_H; ddestruct dd_H as (KG1 & (Hans & HKL1 & HG1 & Hm & Hfa & Hso))). cbn [fst snd] in *.
    eapply eall_mono; [apply (IH z (event_post L e z) s1 mo1); [apply Hok; exact Hans| exact HKL1| exact HG1]|].
    cbn beta. (intros [r s'] mo' dd_H; ddestruct dd_H as (HQ & KG2 & L' & Hp & HP & HKL' & HG' & Hm' & Hfa' & Hso')). cbn [fst snd] in *.
    split; [exact HQ|]. split.
    + replace (K + emaps e)%nat with (emaps e + K)%nat by lia. replace (C + ecost e) with (ecost e + C) by lia.
      eapply kgrow_trans; [exact KG1| exact KG2].
    + exists L'. split; [econstructor; [exact Hans| exact Hp]|]. split; [exact HP|]. split; [exact HKL'|]. split; [exact HG'|].
      split; [congruence| split; congruence].
Qed.
