(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec MState ITree Nodes Decode.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Sys Require SysNodes.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Prelim Monad MSafe STree Malloc Prog KInv KStep KReach.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_MReach () : Init.string Init.list := ["kstep"; "OSSVerify.KrLib.Heap.KInv.event_pre"; "Transfer.TI"; "Corelib.Init.Nat.add"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.le"; "reachT"; "Corelib.Init.Datatypes.prod"; "Corelib.Numbers.BinNums.Z"; "OSSVerify.KrLib.Heap.Prog.PState"; "OSSVerify.KrLib.Heap.Prog.ev_step"; "LinuxProcessSemantics.LinuxProcessSem.State.Model"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.fst"; "OSSVerify.KrLib.Heap.KInv.ev_step_post"; "Corelib.Init.Datatypes.snd"; "OSSVerify.KrLib.Heap.KReach.kres"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition reachT {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
  exists r mo', tpath nstep t mo [] r mo' /\ match r with Unr => True | Ok a => Q a mo' end.

Lemma reachT_ret {A} (a : A) mo (Q : A -> Model -> Prop) : Q a mo -> reachT (Ret (Ok a)) mo Q.
Proof. intros H. dexists (Ok a), mo. cbn. auto. Qed.

Lemma reachT_unr {A} mo (Q : A -> Model -> Prop) : reachT (Ret Unr) mo Q.
Proof. dexists Unr, mo. cbn. auto. Qed.

Lemma reachT_vis {A} n k rsp mo mo1 (Q : A -> Model -> Prop) :
  nstep n mo rsp mo1 [] -> reachT (k rsp) mo1 Q -> reachT (Vis n k) mo Q.
Proof.
  (intros Hst dd_H; ddestruct dd_H as (r & mo' & Hp & HQ)). dexists r, mo'. split; [|exact HQ]. cbn. dexists rsp, mo1, [], []. auto.
Qed.

Lemma reachT_mono {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop) :
  reachT t mo Q -> (forall a mo', Q a mo' -> Q' a mo') -> reachT t mo Q'.
Proof. (intros dd_H; ddestruct dd_H as (r & mo' & Hp & HQ); intros H). dexists r, mo'. split; [exact Hp|]. destruct r; auto. Qed.

Lemma tpath_nil_bind {A B} (t : itree node A) (f : A -> itree node B) mo r mo1 rb mo2 :
  tpath nstep t mo [] r mo1 -> tpath nstep (bind node t f) mo1 [] rb mo2 ->
  False \/ tpath nstep (bind node t f) mo [] rb mo2.
Proof. intros. right. Abort.

Lemma tpath_bind_nil {A B} (t : itree node A) (f : A -> itree node B) mo r mo1 rb mo2 :
  tpath nstep t mo [] r mo1 -> tpath nstep (f r) mo1 [] rb mo2 -> tpath nstep (ITree.bind node t f) mo [] rb mo2.
Proof.
  intros H1 H2. apply (proj2 (tpath_bind node nstep t f mo [] rb mo2)). dexists [], r, mo1, []. auto.
Qed.

Lemma reachT_ebind {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q1 Q :
  reachT t mo Q1 -> (forall a mo1, Q1 a mo1 -> reachT (f a) mo1 Q) -> reachT (ebind t f) mo Q.
Proof.
  (intros dd_H; ddestruct dd_H as (r & mo1 & Hp & HQ); intros Hf). unfold ebind. destruct r as [|a].
  - dexists Unr, mo1. split; [| exact I]. eapply tpath_bind_nil; [exact Hp|]. cbn. auto.
  - ddestruct (Hf a mo1 HQ) as (rb & mo2 & Hp2 & HQ2). dexists rb, mo2. split; [| exact HQ2].
    eapply tpath_bind_nil; [exact Hp| exact Hp2].
Qed.

(* [comment removed for export] *)
Lemma reachT_etwf {A} (t : itree node (exc A)) mo Q Q' :
  reachT t mo Q -> etwf t mo Q' -> exists a mo', tpath nstep t mo [] (Ok a) mo' /\ Q a mo' /\ Q' a mo'.
Proof.
  (intros dd_H; ddestruct dd_H as (r & mo' & Hp & HQ); intros Hw). pose proof (twf_tpath t mo _ [] r mo' Hw Hp) as HP. cbn in HP.
  destruct r as [|a]; [destruct HP|]. dexists a, mo'. auto.
Qed.

Lemma reachT_conj {A} (t : itree node (exc A)) mo Q Q' :
  reachT t mo Q -> etwf t mo Q' -> reachT t mo (fun a mo' => Q a mo' /\ Q' a mo').
Proof.
  intros HR Hw. ddestruct (reachT_etwf t mo Q Q' HR Hw) as (a & mo' & Hp & HQ & HQ'). dexists (Ok a), mo'. auto.
Qed.

(* [comment removed for export] *)
Section MonadForms.
Context {St : Type}.

#[using="Type"] Lemma reachT_mbind {A B} (m : Monad.M St A) (f : A -> Monad.M St B) s mo Q1 Q :
  reachT (m s) mo Q1 -> (forall a s1 mo1, Q1 (a, s1) mo1 -> reachT (f a s1) mo1 Q) -> reachT (mbind m f s) mo Q.
Proof. intros H Hf. unfold mbind. eapply reachT_ebind; [exact H|]. intros [a s1] mo1 HQ. apply Hf. exact HQ. Qed.

#[using="Type"] Lemma reachT_mret {A} (a : A) s mo (Q : A * St -> Model -> Prop) : Q (a, s) mo -> reachT (mret a s) mo Q.
Proof. intros H. apply reachT_ret. exact H. Qed.

#[using="Type"] Lemma reachT_munr {A} s mo (Q : A * St -> Model -> Prop) : reachT (munr s) mo Q.
Proof. apply reachT_unr. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma reachT_msys {A} n (dec : resp -> option A) s mo rsp mo1 (Q : A * St -> Model -> Prop) :
  nstep n mo rsp mo1 [] -> (forall a, dec rsp = Some a -> Q (a, s) mo1) -> reachT (msys n dec s) mo Q.
Proof.
  intros Hst HQ. unfold msys, enode. eapply reachT_vis; [exact Hst|].
  destruct (dec rsp) as [a|] eqn:E; [apply reachT_ret; apply HQ; reflexivity| apply reachT_unr].
Qed.
End MonadForms.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive kstep : ev -> (Z -> Prop) -> Z -> nat -> Prop :=
| ks_brk req : kstep (EBrk req) (fun z => req = 0 \/ z <> req) 0 0
| ks_mmap_fail len prot : kstep (EMmap 0 len prot MAPF) (fun z => is_err z = true) 0 0
| ks_mmap_ok len prot : 0 < len -> mmap_len len <= 2 ^ 35 -> kstep (EMmap 0 len prot MAPF) (fun z => is_err z = false) (mmap_len len) 1
| ks_mprotect a : kstep (EMprotect a PGSZ PROT_RW) (fun z => z = 0) 0 0.

Inductive sreach {R} (Q : R -> Prop) : Z -> nat -> stree ev Z R -> Prop :=
| sr_ret B N r : Q r -> 0 <= B -> sreach Q B N (SRet r)
| sr_undef B N u k : 0 <= B -> sreach Q B N (SVis (EUndef u) k)
| sr_vis B N e (C : Z -> Prop) cb cn k :
    kstep e C cb cn -> 0 <= B ->
    (forall z, C z -> sreach Q B N (k z)) ->
    sreach Q (B + cb) (N + cn)%nat (SVis e k).

Lemma sreach_B_nonneg {R} Q B N (t : stree ev Z R) : sreach Q B N t -> 0 <= B.
Proof.
  intros H. destruct H as [| |B N e C cb cn k HK HB Hk]; try lia. destruct HK as [| |len prot Hl|]; try lia.
  pose proof (mmap_len_bound len Hl). lia.
Qed.

Lemma sreach_mono {R} (Q Q' : R -> Prop) B N B' N' (t : stree ev Z R) :
  sreach Q B N t -> (forall r, Q r -> Q' r) -> B <= B' -> (N <= N')%nat -> sreach Q' B' N' t.
Proof.
  intros H HQ. revert B' N'. induction H as [B N r Hr HB|B N u k HB|B N e C cb cn k HK HB Hk IH]; intros B' N' LB LN.
  - constructor; auto; lia.
  - constructor; lia.
  - replace B' with ((B' - cb) + cb) by lia. replace N' with ((N' - cn) + cn)%nat by lia.
    apply (sr_vis Q' (B' - cb) (N' - cn) e C cb cn k HK); [destruct HK as [| |len prot Hl|]; try lia; pose proof (mmap_len_bound len Hl); lia|].
    intros z Hz. apply (IH z Hz); lia.
Qed.

Lemma sreach_bind {R S} (Q1 : R -> Prop) (Q : S -> Prop) B1 N1 B2 N2 (t : stree ev Z R) (f : R -> stree ev Z S) :
  sreach Q1 B1 N1 t -> 0 <= B2 -> (forall r, Q1 r -> sreach Q B2 N2 (f r)) -> sreach Q (B1 + B2) (N1 + N2)%nat (sbind t f).
Proof.
  intros H HB2 Hf. induction H as [B N r Hr HB|B N u k HB|B N e C cb cn k HK HB Hk IH]; cbn [sbind].
  - eapply sreach_mono; [apply Hf; exact Hr| auto| lia| lia].
  - constructor. lia.
  - replace (B + cb + B2) with ((B + B2) + cb) by lia. replace (N + cn + N2)%nat with ((N + N2) + cn)%nat by lia.
    apply (sr_vis Q (B + B2) (N + N2) e C cb cn _ HK); [lia|]. intros z Hz. apply IH. exact Hz.
Qed.

Lemma sreach_guard {R} Q B N tag (c : bool) (k bail : stree ev Z R) :
  0 <= B -> (c = true -> sreach Q B N k) -> sreach Q B N (guard tag c k bail).
Proof. intros HB H. unfold guard. destruct c; [apply H; reflexivity| constructor; exact HB]. Qed.

Lemma sreach_bad_answer {R} Q B N (bail : stree ev Z R) : 0 <= B -> sreach Q B N (bad_answer bail).
Proof. intros HB. unfold bad_answer. constructor. exact HB. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Transfer.
Variable G : PState -> Model -> Prop.
Hypothesis HG : frame_ok G.

(* [comment removed for export] *)
Definition TI (L : mled) (N : nat) (B : Z) (s : PState) (mo : Model) : Prop :=
  KL L (ps_brk s) mo /\ G s mo /\ kres N B mo.

#[using="Type"] Lemma MAPF_eq : MAPF = MAPF_Z. Proof. reflexivity. Qed.

#[using="Type"] Lemma dec_brk_same cur req : dec_brk cur req (eff0 (Z_to_bv 64 cur)) = Some BrkSame \/ cur < 0 \/ 2 ^ 64 <= cur.
Proof.
  destruct (Z_lt_le_dec cur 0); [tauto|]. destruct (Z_lt_le_dec cur (2 ^ 64)); [|tauto]. left.
  unfold dec_brk, eff0. cbn. rewrite unsigned_lit by lia. rewrite Z.eqb_refl. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma is_err_false z c : 0 <= z -> z + 1 <= c -> ceil_ok c -> is_err z = false.
Proof. intros Hz Hc Hok. unfold is_err, TWO64. apply Z.ltb_ge. pose proof (ceil_ok_lt63 c Hok). lia. Qed.

(* [comment removed for export] *)
#[using="HG"] Lemma ev_step_reach L e (C : Z -> Prop) cb cn N B s mo : ltac2:(CDefT.buildp (gd_tbl_MReach ()) "P,(0.O8.O7.O6.O5.)P,(1.O9.O8.)P,(2.O9.(3.O4.O5.)(4.O3.O6.)O2.O1.)P,(5.=O3.)(6.(7.$8.$9.)(:.O8.O2.)O1.Lp,(7.$8.$9.)Lmo1,$;.(<.A1.O7.(=.$8.$9.R2.)(<.(>.O9.O8.VG,O2.(=.$8.$9.R2.)(?.$8.$9.R2.)R1.)(10.O4.O3.R1.))))")
(* [comment removed for export] *).
Proof.
  (intros HK Hpre dd_H; ddestruct dd_H as (HKL & HGs & KR); intros HB).
  assert (W : etwf (ev_step e s) mo (fun p mo' => ev_step_post L e G s (fst p) (snd p) mo')).
  { apply (ev_step_spec L e G s HG Hpre). auto. }
  enough (K : reachT (ev_step e s) mo (fun p mo1 => C (fst p) /\ kres N B mo1)).
  { eapply reachT_mono; [eapply reachT_conj; [exact K| exact W]|].
    cbn beta. intros a mo' [[HC HR] HP]. split; [exact HC|]. split; [exact HP| exact HR]. }
  clear W.
  pose proof (kl_minv _ _ _ HKL) as Hlazy. unfold minv in Hlazy.
  destruct HK as [req|len prot|len prot Hl0 Hlen35|a].
  - (* [comment removed for export] *)
    rewrite Nat.add_0_r, Z.add_0_r in KR.
    dpose (with_brk_next_same mo (Z_to_bv 64 req)) as (E1 & E2 & E3 & E4).
    assert (KR' : kres N B (with_brk_next mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))) by (eapply kres_vm_eq; [exact E1| exact E2| exact KR]).
    unfold ev_step. destruct (Z.eqb_spec req 0) as [->|Hne].
    + eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => mo1 = with_brk_next mo (Z_to_bv 64 0) (vm_brk (m_vmmaps mo)))).
        - apply (kcan_brk_same 0 mo). lia.
        - intros; reflexivity. }
      cbn beta. intros r s1 mo1 ->. apply (reachT_ret (r, set_brk_ps r s1)). cbn [fst]. split; [left; reflexivity| exact KR'].
    + (* [comment removed for export] *)
      assert (Hcur : ps_brk s = bv_unsigned (vm_brk (m_vmmaps mo)) /\ ps_brk s < req).
      { cbn in Hpre. pose proof (kl_phase _ _ _ HKL) as PH. pose proof (kl_start _ _ _ HKL) as (S1 & S2 & S3 & S4).
        destruct Hpre as [[-> _]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]]; [congruence| |].
        - rewrite Hph in PH. ddestruct PH as (-> & Hb & -> & _). split; [symmetry; exact Hb|].
          pose proof (round_up_pg_ge (bv_unsigned (vm_start_brk (m_vmmaps mo)))). unfold PGSZ. lia.
        - rewrite Hph in PH. ddestruct PH as (b' & l' & Hreg' & Hb & ->). rewrite Hreg in Hreg'. injection Hreg' as <- <-.
          split; [symmetry; exact Hb| unfold PGSZ; lia]. }
      destruct Hcur as [Ecur Hlt]. pose proof (u64_range (vm_brk (m_vmmaps mo))) as Hbr.
      assert (Hreq : 0 <= req < 2 ^ 64).
      { cbn in Hpre. destruct Hpre as [[-> _]|[(cur & Hph & ->)|(b & l & Hph & Hreg & ->)]]; [lia| |].
        - pose proof (kl_phase _ _ _ HKL) as PH. rewrite Hph in PH. destruct PH as (-> & _).
          pose proof (kl_start _ _ _ HKL) as (S1 & S2 & S3 & S4). rewrite round_up_pg_aligned by exact S2.
          pose proof (ld_ceil_lt63 _ _ _ HKL). unfold PGSZ in *. lia.
        - pose proof (kl_brkreg _ _ _ HKL b l Hreg) as (R1 & R2 & R3 & R4 & R5 & _). pose proof (ld_ceil_lt63 _ _ _ HKL). unfold PGSZ in *. lia. }
      change (mbind mget ?f s) with (f s s).
      eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = BrkSame /\ mo1 = with_brk_next mo (Z_to_bv 64 req) (vm_brk (m_vmmaps mo)))).
        - apply (kcan_brk_same req mo Hreq).
        - intros a Hd. destruct (dec_brk_same (ps_brk s) req) as [E|E]; [| exfalso; lia].
          rewrite Ecur, Z_to_bv_bv_unsigned, <- Ecur in E. rewrite E in Hd. injection Hd as <-. split; reflexivity. }
      cbn beta. intros a s1 mo1 [Ea ->]; cbn [fst] in Ea; subst a. apply reachT_mret. cbn [fst]. split; [right; lia| exact KR'].
  - (* [comment removed for export] *)
    rewrite Nat.add_0_r, Z.add_0_r in KR.
    assert (Hlen : 0 < len < 2 ^ 64 /\ (prot = PROT_NONE \/ prot = PROT_RW)).
    { cbn in Hpre. destruct Hpre as [(Hq & _ & _ & Hprot & Hlen)|(cur & _ & _ & _ & _ & Hfx)]; [| discriminate Hfx]. unfold LEN_MAX in Hlen. split; [lia| exact Hprot]. }
    destruct Hlen as [Hlen Hprot].
    pose proof (kcan_mmap_fail len prot mo Hlen ltac:(destruct Hprot as [-> | ->]; [left|right]; reflexivity)) as ST.
    unfold ev_step. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
    destruct Hprot as [-> | ->].
    + change (PROT_NONE =? 0) with true. cbv iota.
      eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = MmErr ENOMEM /\ mo1 = mo)); [rewrite MAPF_eq; exact ST|].
        intros a Hd. cbn in Hd. injection Hd as <-. split; reflexivity. }
      cbn beta. intros a s1 mo1 [Ea ->]; cbn [fst] in Ea; subst a. apply reachT_mret. cbn [fst]. split; [apply is_err_neg; unfold ENOMEM; lia| exact KR].
    + change (PROT_RW =? 0) with false. cbv iota.
      eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = MmErr ENOMEM /\ mo1 = mo)); [rewrite MAPF_eq; exact ST|].
        intros a Hd. cbn in Hd. injection Hd as <-. split; reflexivity. }
      cbn beta. intros a s1 mo1 [Ea ->]; cbn [fst] in Ea; subst a. apply reachT_mret. cbn [fst]. split; [apply is_err_neg; unfold ENOMEM; lia| exact KR].
  - (* [comment removed for export] *)
    rewrite Nat.add_1_r in KR.
    assert (Hlen : 0 < len < 2 ^ 64 /\ (prot = PROT_NONE \/ prot = PROT_RW)).
    { cbn in Hpre. destruct Hpre as [(Hq & _ & _ & Hprot & Hlen)|(cur & _ & _ & _ & _ & Hfx)]; [| discriminate Hfx]. unfold LEN_MAX in Hlen. split; [lia| exact Hprot]. }
    destruct Hlen as [Hlen Hprot].
    pose proof (kl_ceil _ _ _ HKL) as Kcl. pose proof (kl_ceil_ok _ _ _ HKL) as Kcok.
    assert (Htop : SysNodes.alloc_top_min <= alloc_top (m_vmmaps mo)).
    { rewrite <- Kcl. destruct Kcok as [Klo _]. unfold SysNodes.alloc_top_min. unfold ALLOC_CEIL_LO in Klo. exact Klo. }
    ddestruct (kcan_mmap_ok len prot mo N (B + mmap_len len) Hl0 Hlen35 ltac:(destruct Hprot as [-> | ->]; [left|right]; reflexivity) Hlazy KR ltac:(lia) Htop)
      as (a & rsp & mo' & ST & Ersp & Ha0 & Hace & Evm & Emat & Elz & Ehl & KR').
    replace (B + mmap_len len - mmap_len len) with B in KR' by lia.
    pose proof (u64_range a) as Har. pose proof (mmap_len_bound len Hl0) as Hmlb. rewrite <- Kcl in Hace.
    assert (NE : is_err (bv_unsigned a) = false) by (apply (is_err_false _ (ld_ceil L)); [lia| lia| exact Kcok]).
    unfold ev_step. change (Z.land MAPF MAP_FIXED_Z =? 0) with true. cbn [negb].
    destruct Hprot as [-> | ->].
    + change (PROT_NONE =? 0) with true. cbv iota. change (PROT_NONE =? 0) with true in Ersp. cbv iota in Ersp. subst rsp.
      eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = MmOk (bv_unsigned a) /\ mo1 = mo')); [rewrite MAPF_eq; exact ST|].
        intros x Hd. unfold dec_mmap_none in Hd. rewrite !bv_eqb_refl in Hd. cbn [andb] in Hd.
        destruct (mmap_addr_ok len [] (bv_unsigned a)); [| discriminate Hd]. injection Hd as <-. split; reflexivity. }
      cbn beta. intros x s1 mo1 [Ex ->]; cbn [fst] in Ex; subst x. apply reachT_mret. cbn [fst]. split; [exact NE| exact KR'].
    + change (PROT_RW =? 0) with false. cbv iota. change (PROT_RW =? 0) with false in Ersp. cbv iota in Ersp. subst rsp.
      eapply reachT_mbind.
      { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = MmOk (bv_unsigned a) /\ mo1 = mo')); [rewrite MAPF_eq; exact ST|].
        intros x Hd. unfold dec_mmap in Hd. rewrite !bv_eqb_refl in Hd. cbn [andb] in Hd.
        destruct (mmap_addr_ok len [] (bv_unsigned a)); [| discriminate Hd]. injection Hd as <-. split; reflexivity. }
      cbn beta. intros x s1 mo1 [Ex ->]; cbn [fst] in Ex; subst x. apply reachT_mret. cbn [fst]. split; [exact NE| exact KR'].
  - (* [comment removed for export] *)
    rewrite Nat.add_0_r, Z.add_0_r in KR.
    cbn in Hpre. ddestruct Hpre as (Hq & _ & _ & b & l & k & Hin & Ea & Hk2).
    rewrite round_up_pg_eq in Hk2. fold (mmap_len l) in Hk2.
    pose proof (kl_metas _ _ _ HKL b l k Hin) as (A1 & A2 & A3 & A4 & Ak & Ak1 & A5 & A6 & Ana).
    pose proof (went_In_bounds _ _ _ b l HKL (or_intror (ex_intro _ k Hin))) as (_ & B2 & _ & _ & B5 & B6).
    pose proof (ld_ceil_lt63 _ _ _ HKL) as Hcl.
    set (nb := mmap_len l) in *. set (h := m_vmmaps mo) in *. set (aw := Z_to_bv 64 a) in *. set (nw := Z_to_bv 64 PGSZ) in *.
    assert (Hab : b + PGSZ <= a /\ a + PGSZ <= b + nb) by (subst a; unfold PGSZ in *; nia).
    assert (Ua : bv_unsigned aw = a) by (subst aw; apply unsigned_lit; unfold PGSZ in *; lia).
    assert (Un : bv_unsigned nw = PGSZ) by (subst nw; apply unsigned_lit; unfold PGSZ; lia).
    assert (Hamod : a mod 4096 = 0). { subst a. unfold PGSZ in *. rewrite Z.add_mod, A3, Z.mod_mul by lia. reflexivity. }
    assert (Hcn : map_contains (vm_noaccess h) aw nw = true).
    { ddestruct (Ana (1 + k) ltac:(lia) ltac:(lia)) as (e & He & Hel & Heh). unfold map_contains. apply existsb_exists. exists e. split; [exact He|].
      rewrite Ua, Un. unfold elo, ehi in Hel, Heh. subst a. rewrite (proj2 (Z.leb_le _ _)) by lia. rewrite (proj2 (Z.leb_le _ _)) by lia. reflexivity. }
    assert (Hcm : map_contains (vm_maps h) aw nw = true).
    { unfold map_contains. apply existsb_exists. exists (went b nb). split; [exact A5|]. rewrite Ua, Un. unfold elo, ehi in B5, B6. rewrite B5.
      replace (bv_unsigned (fst (went b nb)) + bv_unsigned (snd (went b nb))) with (b + nb) by (symmetry; exact B6).
      rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). rewrite (proj2 (Z.leb_le _ _)) by (unfold PGSZ in *; lia). reflexivity. }
    ddestruct (kcan_mprotect_ok a mo N B ltac:(unfold PGSZ in *; lia) Hamod ltac:(unfold PGSZ in *; lia) Hcn Hcm Hlazy KR) as (mo' & ST & Emo' & KR' & Elz & Ehl).
    unfold ev_step.
    eapply reachT_mbind.
    { eapply (reachT_msys _ _ s mo _ _ (fun p mo1 => fst p = RgDone true /\ mo1 = mo')); [exact ST|].
      intros x Hd. unfold dec_mprotect_rw, dec_mprotect in Hd. change (bv_unsigned (Z_to_bv 64 0) =? 0) with true in Hd.
      fold aw in Hd. change (Z_to_bv 64 (mmap_len PGSZ)) with nw in Hd. rewrite !bv_eqb_refl in Hd. cbn in Hd. injection Hd as <-. split; reflexivity. }
    cbn beta. intros x s1 mo1 [Ex ->]; cbn [fst] in Ex; subst x. apply reachT_mret. cbn [fst]. split; [reflexivity| exact KR'].
Qed.

(* [comment removed for export] *)
#[using="HG"] Theorem membed_reach {R} (Q : R -> Prop) : forall (t : stree ev Z R) B N L (Post : mled -> R -> Prop) s mo,
  sreach Q B N t -> ctree_ok L t Post -> TI L N B s mo ->
  reachT (membed t s) mo (fun p mo' => Q (fst p) /\ exists L', cpath L t L' (fst p) /\ Post L' (fst p)
                                      /\ TI L' 0%nat 0 (snd p) mo'
                                      /\ ps_m (snd p) = ps_m s /\ ps_fa (snd p) = ps_fa s /\ ps_so (snd p) = ps_so s).
Proof.
  intros t B N L Post s mo H. revert L s mo.
  induction H as [B N r Hr HB|B N u k HB|B N e C cb cn k HK HB Hk IH]; (intros L s mo Hok dd_H; ddestruct dd_H as (HKL & HGs & KR)).
  - cbn [membed]. apply reachT_mret. cbn [fst snd]. split; [exact Hr|]. exists L. split; [constructor|].
    cbn in Hok. split; [exact Hok|]. split; [| repeat split; reflexivity]. split; [exact HKL|]. split; [exact HGs|]. eapply kres_mono; [exact KR| lia| lia].
  - cbn [membed ev_step]. rewrite mbind_munr. apply reachT_unr.
  - cbn [membed]. cbn in Hok. destruct Hok as [Hpre Hok].
    eapply reachT_mbind; [eapply (ev_step_reach L e C cb cn N B s mo HK Hpre); [split; [exact HKL| split; [exact HGs| exact KR]]| exact HB]|].
    cbn beta. (intros z s1 mo1 dd_H; ddestruct dd_H as (HC & (Hans & HKL1 & HG1 & Hm & Hfa & Hso) & KR1)).
    eapply reachT_mono; [apply (IH z HC (event_post L e z) s1 mo1); [apply Hok; exact Hans| split; [exact HKL1| split; [exact HG1| exact KR1]]]|].
    cbn beta. (intros p mo' dd_H; ddestruct dd_H as (HQ & L' & Hp & HP & HTI & Hm' & Hfa' & Hso')). split; [exact HQ|]. exists L'.
    split; [econstructor; [exact Hans| exact Hp]|]. split; [exact HP|]. split; [exact HTI|]. cbn [fst snd] in *. repeat split; congruence.
Qed.

End Transfer.
