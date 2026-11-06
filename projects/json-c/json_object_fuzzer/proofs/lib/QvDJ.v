(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qc6I QJFf Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq0.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc6I QJFf.
Import Qpj5.Mq1.
Import ListNotations.
Import Qc6I.Exc.

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
match t with
| Ret r => P r mo
| Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
end.

Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

End MSpec.

Arguments assn St : clear implicits.
Arguments mspec {St A} P m Q.
End Mq0.

Module Mq1.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qc6I QJFf.
Import Qpj5.Mq1.
Import ListNotations.
Import Qc6I.Exc.

Section MSafeG.
Variable nstep : node -> Model -> resp -> Model -> list event -> Prop.
Variable nsafe : node -> Model -> Prop.

Fixpoint twf {R} (t : itree node R) (mo : Model) (P : R -> Model -> Prop) : Prop :=
match t with
| Ret r => P r mo
| Vis n k => nsafe n mo /\ forall rsp mo' evs, nstep n mo rsp mo' evs -> twf (k rsp) mo' P
end.

Lemma twf_mono : forall {R} (t : itree node R) mo (P P' : R -> Model -> Prop),
twf t mo P -> (forall r mo1, P r mo1 -> P' r mo1) -> twf t mo P'.
Proof.
intros R t. induction t as [r|n k IH]; intros mo P P' H HP; cbn in *.
- apply HP. exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. eapply IH; eauto.
Qed.

Lemma twf_bind : forall {A B} (t : itree node A) (f : A -> itree node B) mo (P : B -> Model -> Prop),
twf t mo (fun a mo1 => twf (f a) mo1 P) -> twf (Qc6I.bind node t f) mo P.
Proof.
intros A B t. induction t as [r|n k IH]; intros f mo P H; cbn in *.
- exact H.
- destruct H as [Hs Hk]. split; [exact Hs|]. intros rsp mo' evs Hst. apply IH. eapply Hk; eauto.
Qed.

Lemma twf_tpath : forall {R} (t : itree node R) mo P tr r mo',
twf t mo P -> tpath nstep t mo tr r mo' -> P r mo'.
Proof.
intros R t. induction t as [r0|n k IH]; intros mo P tr r mo' H Hp; cbn in *.
- destruct Hp as (<- & -> & ->). exact H.
- destruct H as [_ Hk]. destruct Hp as (rsp & mo1 & evs & tr' & Hst & Hp & _).
eapply IH; [eapply Hk; exact Hst| exact Hp].
Qed.

Definition etwf {A} (t : itree node (exc A)) (mo : Model) (Q : A -> Model -> Prop) : Prop :=
twf t mo (fun r mo1 => match r with Unr => False | Ok a => Q a mo1 end).

Lemma etwf_mono : forall {A} (t : itree node (exc A)) mo (Q Q' : A -> Model -> Prop),
etwf t mo Q -> (forall a mo1, Q a mo1 -> Q' a mo1) -> etwf t mo Q'.
Proof.
intros A t mo Q Q' H HQ. unfold etwf in *. eapply twf_mono; [exact H|].
intros [|a] mo1; cbn; auto.
Qed.

Lemma etwf_ebind : forall {A B} (t : itree node (exc A)) (f : A -> itree node (exc B)) mo Q,
etwf t mo (fun a mo1 => etwf (f a) mo1 Q) -> etwf (ebind t f) mo Q.
Proof.
intros A B t f mo Q H. unfold etwf, ebind in *. apply twf_bind.
eapply twf_mono; [exact H|]. intros [|a] mo1 Ha; cbn; [destruct Ha| exact Ha].
Qed.

Section MSpec.
Context {St : Type}.

Definition assn : Type := St -> Model -> Prop.

Definition mspec {A} (P : assn) (m : M St A) (Q : A -> assn) : Prop :=
forall s mo, P s mo -> etwf (m s) mo (fun p mo' => Q (fst p) (snd p) mo').

Lemma mspec_ret {A} (a : A) (P : assn) (Q : A -> assn) :
(forall s mo, P s mo -> Q a s mo) -> mspec P (mret a) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_bind {A B} (m : M St A) (f : A -> M St B) (P : assn) (Q1 : A -> assn) (Q : B -> assn) :
mspec P m Q1 -> (forall a, mspec (Q1 a) (f a) Q) -> mspec P (mbind m f) Q.
Proof.
intros Hm Hf s mo HP. unfold mbind. apply etwf_ebind.
eapply etwf_mono; [exact (Hm s mo HP)|]. intros [a s1] mo1 H1. cbn in *. exact (Hf a s1 mo1 H1).
Qed.

Lemma mspec_conseq {A} (m : M St A) (P P' : assn) (Q Q' : A -> assn) :
mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> (forall a s mo, Q a s mo -> Q' a s mo) -> mspec P' m Q'.
Proof.
intros Hm HP HQ s mo HP'. eapply etwf_mono; [exact (Hm s mo (HP _ _ HP'))|].
intros [a s1] mo1; cbn; auto.
Qed.

Lemma mspec_pre {A} (m : M St A) (P P' : assn) (Q : A -> assn) :
mspec P m Q -> (forall s mo, P' s mo -> P s mo) -> mspec P' m Q.
Proof. intros Hm HP. eapply mspec_conseq; eauto. Qed.

Lemma mspec_get (P : assn) : mspec P mget (fun s' s mo => s' = s /\ P s mo).
Proof. intros s mo HP. cbn. auto. Qed.

Lemma mspec_upd (P : assn) (f : St -> St) : mspec P (mupd f) (fun _ s mo => exists s0, s = f s0 /\ P s0 mo).
Proof. intros s mo HP. cbn. eauto. Qed.

Lemma mspec_upd' (P : assn) (Q : unit -> assn) (f : St -> St) :
(forall s mo, P s mo -> Q tt (f s) mo) -> mspec P (mupd f) Q.
Proof. intros H s mo HP. cbn. apply H. exact HP. Qed.

Lemma mspec_sys {A} (n : node) (dec : resp -> option A) (P : assn) (Q : A -> assn) :
(forall s mo, P s mo ->
nsafe n mo /\
forall rsp mo' evs, nstep n mo rsp mo' evs -> exists a, dec rsp = Some a /\ Q a s mo') ->
mspec P (msys n dec) Q.
Proof.
intros H s mo HP. destruct (H s mo HP) as [Hs Hk]. unfold msys. cbn. split; [exact Hs|].
intros rsp mo' evs Hst. destruct (Hk rsp mo' evs Hst) as (a & -> & HQ). exact HQ.
Qed.

Lemma mspec_pointwise {A} (P : assn) (m : M St A) (Q : A -> assn) :
(forall s mo, P s mo -> mspec (fun s' mo' => s' = s /\ mo' = mo) m Q) -> mspec P m Q.
Proof. intros H s mo HP. apply (H s mo HP). auto. Qed.

End MSpec.
End MSafeG.

Arguments assn St : clear implicits.
Arguments twf nstep nsafe {R} t mo P.
Arguments etwf nstep nsafe {A} t mo Q.
Arguments mspec nstep nsafe {St A} P m Q.
End Mq1.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qcrs QUcd QCUT QwAs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq2.

Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import Qcrs QUcd QCUT QwAs.Mq0 Qc6I QJFf.
Import Qpj5.Mq1.
Import ListNotations.
Import Qc6I.Exc.

Section MonadG.
Context {St : Type}.
Local Notation M := (Qpj5.Mq1.M St).

Section MachineG.
Variable segs : list Segment.

Variable atn : node -> machine_state -> Prop.

Definition implMG {A} (c : M A) (s : St) (Q : A -> St -> machine_state -> Prop) (ms : machine_state) : Prop :=
impl segs atn (c s) (epost (fun p => Q (fst p) (snd p))) ms.

Lemma implMG_ret : forall {A} (a : A) s Q ms, evt segs (Q a s) ms -> implMG (mret a) s Q ms.
Proof. intros A a s Q ms H. unfold implMG, mret. apply impl_ret_ok. exact H. Qed.

Lemma implMG_unr : forall {A} s (Q : A -> St -> machine_state -> Prop) ms, implMG munr s Q ms.
Proof. intros. unfold implMG, munr. apply impl_ret_unr. Qed.

Lemma implMG_bind : forall {A B} (m : M A) (f : A -> M B) s Q1 Q ms,
implMG m s Q1 ms ->
(forall a s' ms', Q1 a s' ms' -> implMG (f a) s' Q ms') ->
implMG (mbind m f) s Q ms.
Proof.
intros A B m f s Q1 Q ms Hm Hf. unfold implMG, mbind in *.
eapply impl_ebind; [exact Hm|]. intros [a s'] ms' H. cbn in *. apply Hf. exact H.
Qed.

Lemma implMG_mono : forall {A} (m : M A) s (Q Q' : A -> St -> machine_state -> Prop) ms,
implMG m s Q ms -> (forall a s' ms', Q a s' ms' -> Q' a s' ms') -> implMG m s Q' ms.
Proof.
intros A m s Q Q' ms H HQ. unfold implMG in *. eapply impl_epost_mono; [exact H|].
intros [a s'] ms'; cbn; auto.
Qed.

Lemma implMG_sys : forall {A} n (dec : resp -> option A) s Q ms,
evt segs (fun ms1 => atn n ms1 /\
forall rsp a, dec rsp = Some a -> evt segs (Q a s) (nret ms1 rsp)) ms ->
implMG (msys n dec) s Q ms.
Proof.
intros A n dec s Q ms H. unfold implMG, msys. apply impl_enode.
eapply evt_mono; [exact H|]. intros ms1 [Hat Hk]. split; [exact Hat|].
intros rsp [a s'] E. cbn. specialize (Hk rsp).
destruct (dec rsp) as [a'|]; [|discriminate]. inversion E; subst. apply Hk. reflexivity.
Qed.

Lemma implMG_get : forall s Q ms, evt segs (Q s s) ms -> implMG mget s Q ms.
Proof. intros. unfold implMG, mget. apply impl_ret_ok. exact H. Qed.

Lemma implMG_upd : forall f s Q ms, evt segs (Q tt (f s)) ms -> implMG (mupd f) s Q ms.
Proof. intros. unfold implMG, mupd. apply impl_ret_ok. exact H. Qed.

Lemma implMG_evt : forall {A} (c : M A) s Q P ms,
evt segs P ms -> (forall ms', P ms' -> implMG c s Q ms') -> implMG c s Q ms.
Proof. intros A c s Q P ms H K. unfold implMG in *. eapply impl_evt; eauto. Qed.

End MachineG.
End MonadG.

End Mq2.
From Stdlib Require NArith.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QMow QoSL Q13u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Module Mq3.

Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import QUcd QCUT QMow QoSL Q13u QwAs.
Import ListNotations.
Open Scope Z_scope.

Fixpoint find_byte (c : Z) (l : list byte) : option nat :=
match l with
| [] => None
| b :: l' => if bv_unsigned b =? c then Some 0%nat
else match find_byte c l' with Some i => Some (S i) | None => None end
end.

Lemma find_byte_Some : forall c l i, find_byte c l = Some i ->
(i < length l)%nat /\ (exists b, nth_error l i = Some b /\ bv_unsigned b = c) /\
(forall j b, (j < i)%nat -> nth_error l j = Some b -> bv_unsigned b <> c).
Proof.
intros c l; induction l as [|b l IH]; intros i H; cbn in H; [discriminate|].
destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE].
- injection H as <-. cbn. split; [lia|]. split. { exists b. auto. } intros; lia.
- destruct (find_byte c l) as [i'|] eqn:F; [|discriminate]. injection H as <-.
destruct (IH i' eq_refl) as (Hl & (b' & Hn & Hb') & Hmin). cbn. split; [lia|]. split. { exists b'. auto. }
intros [|j] b2 Hj Hn2; cbn in Hn2. { injection Hn2 as <-. exact NE. } eapply Hmin; [|exact Hn2]. lia.
Qed.

Lemma find_byte_None : forall c l, find_byte c l = None -> forall j b, nth_error l j = Some b -> bv_unsigned b <> c.
Proof.
intros c l; induction l as [|b l IH]; intros H j b2 Hn; [destruct j; discriminate|].
cbn in H. destruct (Z.eqb_spec (bv_unsigned b) c) as [E|NE]; [discriminate|].
destruct (find_byte c l) eqn:F; [discriminate|].
destruct j as [|j]; cbn in Hn. { injection Hn as <-. exact NE. } eapply IH; eauto.
Qed.

Lemma find_byte_app_r : forall c l1 l2, find_byte c l1 = None ->
find_byte c (l1 ++ l2) = match find_byte c l2 with Some i => Some (length l1 + i)%nat | None => None end.
Proof.
intros c l1; induction l1 as [|b l1 IH]; intros l2 H; cbn in *. { destruct (find_byte c l2); reflexivity. }
destruct (bv_unsigned b =? c); [discriminate|]. destruct (find_byte c l1) eqn:F; [discriminate|].
rewrite (IH l2 eq_refl). destruct (find_byte c l2); reflexivity.
Qed.

Lemma find_byte_charact : forall c l i b,
nth_error l i = Some b -> bv_unsigned b = c ->
(forall j b', (j < i)%nat -> nth_error l j = Some b' -> bv_unsigned b' <> c) ->
find_byte c l = Some i.
Proof.
intros c l i b Hn Hb Hmin. destruct (find_byte c l) as [i'|] eqn:F.
- destruct (find_byte_Some _ _ _ F) as (Hl & (b' & Hn' & Hb') & Hmin').
destruct (Nat.lt_trichotomy i i') as [Hlt|[->|Hgt]].
+ exfalso. exact (Hmin' _ _ Hlt Hn Hb).
+ reflexivity.
+ exfalso. exact (Hmin _ _ Hgt Hn' Hb').
- exfalso. exact (find_byte_None _ _ F _ _ Hn Hb).
Qed.

Lemma find_byte_None_intro : forall c l,
(forall j b, nth_error l j = Some b -> bv_unsigned b <> c) -> find_byte c l = None.
Proof.
intros c l H. destruct (find_byte c l) as [i|] eqn:F; [|reflexivity].
destruct (find_byte_Some _ _ _ F) as (_ & (b & Hn & Hb) & _). exfalso. exact (H _ _ Hn Hb).
Qed.

Lemma find_byte_notin : forall c l, (forall b, In b l -> bv_unsigned b <> c) -> find_byte c l = None.
Proof.
intros c l H. apply find_byte_None_intro. intros j b Hn. apply H. eapply nth_error_In; eauto.
Qed.

Lemma find_byte_hit : forall c l b rest,
(forall b', In b' l -> bv_unsigned b' <> c) -> bv_unsigned b = c ->
find_byte c (l ++ b :: rest) = Some (length l).
Proof.
intros c l b rest Hl Hb. rewrite find_byte_app_r by (apply find_byte_notin; exact Hl).
cbn. rewrite (proj2 (Z.eqb_eq _ _) Hb). f_equal. lia.
Qed.

Definition memchr_res (A : Z) (c : Z) (n : Z) (buf : list byte) : Z :=
match find_byte c (firstn (Z.to_nat n) buf) with Some i => A + Z.of_nat i | None => 0 end.

Definition memchr_ok (A c n : Z) (buf : list byte) : Prop :=
match find_byte c (firstn (Z.to_nat n) buf) with
| Some j => (n <= Z.of_nat (length buf) \/
Z.of_nat j + 1 + (- (A + Z.of_nat j + 1)) mod 8 <= Z.of_nat (length buf))%Z
| None => (n <= Z.of_nat (length buf))%Z
end.

Definition strnlen_res (n : Z) (buf : list byte) : Z :=
match find_byte 0 (firstn (Z.to_nat n) buf) with Some i => Z.of_nat i | None => n end.

Section NulTerminated.
Variables (A n : Z) (str slack : list byte).
Hypothesis NONUL : ~ In (Z_to_bv 8 0) str.
Hypothesis PAD : ((- (A + Z.of_nat (length str) + 1)) mod 8 <= Z.of_nat (length slack))%Z.

Lemma str_bytes_nz : forall b, In b str -> bv_unsigned b <> 0.
Proof. intros b Hb E. apply NONUL. replace (Z_to_bv 8 0) with b; [exact Hb|]. apply bv_eq. rewrite E. reflexivity. Qed.

Lemma find_byte_cstr : (Z.of_nat (length str) < n)%Z ->
find_byte 0 (firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: slack)) = Some (length str).
Proof.
intros Hn. rewrite firstn_app. rewrite firstn_all2 by lia.
destruct (Z.to_nat n - length str)%nat as [|k] eqn:E; [lia|]. cbn [firstn].
apply find_byte_hit; [apply str_bytes_nz| reflexivity].
Qed.

Lemma find_byte_cstr_short : (n <= Z.of_nat (length str))%Z ->
find_byte 0 (firstn (Z.to_nat n) (str ++ Z_to_bv 8 0 :: slack)) = None.
Proof.
intros Hn. rewrite firstn_app. replace (Z.to_nat n - length str)%nat with 0%nat by lia. cbn [firstn]. rewrite app_nil_r.
apply find_byte_notin. intros b Hb. apply str_bytes_nz. rewrite <- (firstn_skipn (Z.to_nat n) str). apply in_or_app. left. exact Hb.
Qed.

Lemma memchr_ok_cstr : memchr_ok A 0 n (str ++ Z_to_bv 8 0 :: slack).
Proof.
unfold memchr_ok. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n) as [Hn|Hn].
- rewrite find_byte_cstr by lia. right. rewrite length_app. cbn [length]. lia.
- rewrite find_byte_cstr_short by lia. rewrite length_app. cbn [length]. lia.
Qed.

Lemma strnlen_res_cstr :
strnlen_res n (str ++ Z_to_bv 8 0 :: slack) = Z.min (Z.of_nat (length str)) n.
Proof.
unfold strnlen_res. destruct (Z.lt_ge_cases (Z.of_nat (length str)) n).
- rewrite find_byte_cstr by lia. lia.
- rewrite find_byte_cstr_short by lia. lia.
Qed.
End NulTerminated.

Fixpoint strncmp_walk (l r : list byte) (k : nat) {struct l} : option Z :=
match l, r with
| a :: l', b :: r' =>
if ((bv_unsigned a =? 0) || (bv_unsigned b =? 0) || Nat.eqb k 0 || negb (bv_unsigned a =? bv_unsigned b))%bool
then Some (bv_unsigned a - bv_unsigned b)
else match k with O => Some (bv_unsigned a - bv_unsigned b) | S k' => strncmp_walk l' r' k' end
| _, _ => None
end.
Definition strncmp_model (l r : list byte) (n : Z) : option Z :=
if n =? 0 then Some 0 else strncmp_walk l r (Z.to_nat (n - 1)).

Fixpoint memcmp_model (l r : list byte) (n : nat) {struct n} : option Z :=
match n with
| O => Some 0
| S n' =>
match l, r with
| a :: l', b :: r' => if bv_unsigned a =? bv_unsigned b then memcmp_model l' r' n' else Some (bv_unsigned a - bv_unsigned b)
| _, _ => None
end
end.

Section WithSegs.
Variable segs : list MemImageType.Segment.

Lemma u8arr_write_bytes : forall m A bs (i : Z) xs,
u8arr segs m A bs -> (0 <= i)%Z -> (Z.to_nat i + length xs <= length bs)%nat ->
u8arr segs (write_to_mem m (wa (A + i)) xs) A (upd_bytes bs (Z.to_nat i) xs).
Proof.
intros m A bs i xs [Hb Hw] Hi Hl. split.
- apply bytes_at_write_inside; assumption.
- rewrite upd_bytes_length by lia. apply wr_at_write. exact Hw.
Qed.

Lemma u8arr_store_ok_n : forall m A bs (i : Z) n a,
u8arr segs m A bs -> (0 <= i)%Z -> (i + Z.of_nat n <= Z.of_nat (length bs))%Z -> a = wa (A + i) ->
store_ok segs m a n = true.
Proof. intros m A bs i n a [_ Hw] Hi Hn ->. eapply wr_at_store_ok; eauto; lia. Qed.

Lemma rw_cells_CB_length : forall m A n bs, rw_cells segs m A [CB n bs] -> length bs = n.
Proof. intros m A n bs [[H _] _]. cbn in H. tauto. Qed.
End WithSegs.

Definition filled (c : byte) (bs : list byte) (Q : Z -> Prop) : Prop :=
forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j -> nth_error bs (Z.to_nat j) = Some c.

Lemma filled_init : forall c bs, filled c bs (fun _ => False).
Proof. intros c bs j _ []. Qed.

Lemma nth_error_repeat' : forall {X} (x : X) k i, (i < k)%nat -> nth_error (repeat x k) i = Some x.
Proof. intros X x k; induction k as [|k IH]; intros [|i] H; cbn; try lia; auto. apply IH. lia. Qed.

Lemma filled_upd : forall c bs Q i k,
filled c bs Q -> (i + k <= length bs)%nat ->
filled c (upd_bytes bs i (repeat c k)) (fun j => Q j \/ (Z.of_nat i <= j < Z.of_nat i + Z.of_nat k)%Z).
Proof.
intros c bs Q i k HF Hk j Hj HQ. rewrite upd_bytes_length in Hj by (rewrite repeat_length; lia).
rewrite upd_bytes_nth by (rewrite ?repeat_length; lia). rewrite repeat_length.
destruct (Nat.leb_spec0 i (Z.to_nat j)); destruct (Nat.ltb_spec0 (Z.to_nat j) (i + k)); cbn [andb];
first [ apply nth_error_repeat'; lia | destruct HQ as [HQ|HQ]; [apply HF; [lia| exact HQ] | exfalso; lia] ].
Qed.

Lemma filled_updZ : forall c bs Q (i : Z) k,
filled c bs Q -> (0 <= i)%Z -> (Z.to_nat i + k <= length bs)%nat ->
filled c (upd_bytes bs (Z.to_nat i) (repeat c k)) (fun j => Q j \/ (i <= j < i + Z.of_nat k)%Z).
Proof.
intros c bs Q i k HF Hi Hk j Hj HQ. apply (filled_upd c bs Q (Z.to_nat i) k HF Hk j Hj). destruct HQ; [left; assumption| right; lia].
Qed.

Lemma filled_all : forall c bs Q, filled c bs Q -> (forall j, (0 <= j < Z.of_nat (length bs))%Z -> Q j) -> bs = repeat c (length bs).
Proof.
intros c bs Q HF HQ. apply nth_error_ext. intros i.
destruct (Nat.lt_ge_cases i (length bs)) as [Hi|Hi].
- rewrite nth_error_repeat' by lia. replace i with (Z.to_nat (Z.of_nat i)) by lia. apply HF; [lia|]. apply HQ. lia.
- rewrite (proj2 (nth_error_None _ _)) by lia. rewrite (proj2 (nth_error_None _ _)) by (rewrite repeat_length; lia). reflexivity.
Qed.

Lemma Z_to_bv8_mod : forall z, Z_to_bv 8 z = Z_to_bv 8 (z mod 256).
Proof. intros z. apply bv_eq. rewrite !Z_to_bv_unsigned. change (bv_wrap 8 ?x) with (x mod 256)%Z. rewrite Z.mod_mod by lia. reflexivity. Qed.

Lemma land_align_down : forall x j, 0 <= x < 2^64 -> 0 <= j <= 64 ->
Z.land x (2^64 - 2^j) = x - x mod 2^j.
Proof.
intros x j Hx Hj.
replace (2^64 - 2^j)%Z with (Z.ldiff (Z.ones 64) (Z.ones j)).
2:{ rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
unfold Z.ones. rewrite Z.shiftl_mul_pow2 by lia.
replace (2^64)%Z with (2^j * 2^(64-j))%Z by (rewrite <- Z.pow_add_r by lia; f_equal; lia).
replace (Z.pred (1 * (2 ^ j * 2 ^ (64 - j))))%Z with ((2^(64-j) - 1) * 2^j + (2^j - 1))%Z by lia.
rewrite Z.div_add_l by lia. rewrite Z.div_small by (split; [lia| apply Z.lt_pred_l || lia]). lia. }
rewrite Z.ldiff_land, Z.land_assoc. rewrite <- Z.ldiff_land.
rewrite Z.land_ones by lia. rewrite Z.mod_small by lia.
rewrite Z.ldiff_ones_r by lia. rewrite Z.shiftr_div_pow2, Z.shiftl_mul_pow2 by lia.
pose proof (Z.div_mod x (2^j)%Z ltac:(lia)). lia.
Qed.

Definition zseq (n : nat) : list Z := map Z.of_nat (seq 0 n).
Lemma forallb_zseq : forall n f, forallb f (zseq n) = true -> forall c, 0 <= c < Z.of_nat n -> f c = true.
Proof.
intros n f H c Hc. rewrite forallb_forall in H. apply H. unfold zseq. apply in_map_iff.
exists (Z.to_nat c). split; [lia|]. apply in_seq. lia.
Qed.

Lemma brute256_ok : forall (P : Z -> bool), forallb P (zseq 256) = true -> forall c, 0 <= c < 256 -> P c = true.
Proof. intros P H c Hc. exact (forallb_zseq 256 P H c Hc). Qed.

Lemma word_eq_of_eqb : forall x y : Z, (x mod 2^64 =? y mod 2^64) = true -> Z_to_bv 64 x = Z_to_bv 64 y.
Proof. intros x y H. apply Z.eqb_eq in H. apply bv_eq. rewrite !Z_to_bv_unsigned. exact H. Qed.

Lemma map_unsigned_inj : forall (l1 l2 : list byte), map bv_unsigned l1 = map bv_unsigned l2 -> l1 = l2.
Proof.
induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
injection H as Hx Hl. f_equal; [apply bv_eq; exact Hx| apply IH; exact Hl].
Qed.

Definition list_Z_eqb (l1 l2 : list Z) : bool := if list_eq_dec Z.eq_dec l1 l2 then true else false.
Lemma list_Z_eqb_eq : forall l1 l2, list_Z_eqb l1 l2 = true -> l1 = l2.
Proof. intros l1 l2. unfold list_Z_eqb. destruct (list_eq_dec Z.eq_dec l1 l2); [auto|discriminate]. Qed.

Lemma bcast_ok : forall (F : Z -> list byte) k,
forallb (fun c => list_Z_eqb (map bv_unsigned (F c)) (repeat c k)) (zseq 256) = true ->
forall c, 0 <= c < 256 -> F c = repeat (Z_to_bv 8 c) k.
Proof.
intros F k H c Hc. apply map_unsigned_inj.
pose proof (forallb_zseq 256 _ H c Hc) as E. cbn beta in E. apply list_Z_eqb_eq in E. rewrite E.
rewrite map_repeat. f_equal. rewrite Z_to_bv_unsigned. symmetry. apply bv_wrap_small. unfold bv_modulus. cbn. lia.
Qed.

Definition BC4 := 16843009.
Definition BC8 := 72340172838076673.

Lemma le4_bcast : forall c, 0 <= c < 256 -> le4 (Z_to_bv 64 (c * BC4)) = repeat (Z_to_bv 8 c) 4.
Proof. apply (bcast_ok (fun c => le4 (Z_to_bv 64 (c * BC4))) 4). vm_compute. reflexivity. Qed.
Lemma le8_bcast : forall c, 0 <= c < 256 -> le8 (Z_to_bv 64 (c * BC8)) = repeat (Z_to_bv 8 c) 8.
Proof. apply (bcast_ok (fun c => le8 (Z_to_bv 64 (c * BC8))) 8). vm_compute. reflexivity. Qed.
Lemma le1_byte : forall x : word, le1 x = [Z_to_bv 8 (bv_unsigned x mod 256)].
Proof. intros x. cbn. rewrite <- Z_to_bv8_mod. reflexivity. Qed.

Definition copied (src bs : list byte) (k : nat) : Prop :=
length bs = length src /\ firstn k bs = firstn k src.

Lemma copied_0 : forall src bs, length bs = length src -> copied src bs 0.
Proof. intros src bs H. split; [exact H| reflexivity]. Qed.

Lemma copied_all : forall src bs k, copied src bs k -> (length src <= k)%nat -> bs = src.
Proof.
intros src bs k [Hl Hf] Hk. rewrite <- (firstn_all2 (n:=k) bs) by lia. rewrite <- (firstn_all2 (n:=k) src) by lia. exact Hf.
Qed.

Lemma firstn_app_len : forall {X} (a b : list X) k, k = length a -> firstn k (a ++ b) = a.
Proof. intros X a b k ->. rewrite firstn_app, firstn_all, Nat.sub_diag. cbn. apply app_nil_r. Qed.

Lemma app_firstn_mid_skipn : forall {X} (l : list X) p k,
firstn p l ++ firstn k (skipn p l) ++ skipn (p + k) l = l.
Proof.
intros X l p k. rewrite <- (firstn_skipn p l) at 4. f_equal.
replace (skipn (p + k) l) with (skipn k (skipn p l)) by (rewrite skipn_skipn; f_equal; lia). apply firstn_skipn.
Qed.

Lemma copied_upd : forall src bs p xs,
copied src bs p -> firstn (length xs) (skipn p src) = xs -> (p + length xs <= length src)%nat ->
copied src (upd_bytes bs p xs) (p + length xs).
Proof.
intros src bs p xs [Hl Hf] Hx Hp. split.
- rewrite upd_bytes_length by lia. exact Hl.
- unfold upd_bytes. rewrite app_assoc.
assert (L1 : length (firstn p bs ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
rewrite (firstn_app_len (firstn p bs ++ xs)) by lia.
transitivity (firstn (p + length xs) (firstn p src ++ xs ++ skipn (p + length xs) src)).
+ assert (L2 : length (firstn p src ++ xs) = (p + length xs)%nat) by (rewrite app_length, firstn_length; lia).
rewrite app_assoc, (firstn_app_len (firstn p src ++ xs)) by lia. rewrite Hf. reflexivity.
+ f_equal. etransitivity; [ | apply (app_firstn_mid_skipn src p (length xs))]. rewrite Hx. reflexivity.
Qed.

Lemma copied_updZ : forall src bs (P : Z) xs,
copied src bs (Z.to_nat P) -> (0 <= P)%Z -> firstn (length xs) (skipn (Z.to_nat P) src) = xs ->
(Z.to_nat P + length xs <= length src)%nat ->
copied src (upd_bytes bs (Z.to_nat P) xs) (Z.to_nat (P + Z.of_nat (length xs))).
Proof.
intros src bs P xs HC HP Hx Hl. replace (Z.to_nat (P + Z.of_nat (length xs))) with (Z.to_nat P + length xs)%nat by lia.
apply copied_upd; assumption.
Qed.

Lemma window_ex : forall (l : list byte) (i : Z) (k : nat), (Z.to_nat i + k <= length l)%nat ->
exists xs, firstn k (skipn (Z.to_nat i) l) = xs /\ length xs = k.
Proof. intros l i k H. eexists. split; [reflexivity|]. rewrite firstn_length, skipn_length. lia. Qed.

Lemma window_nth : forall (l xs : list byte) (base : Z) (k c : nat) (i : Z),
firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c < k)%nat -> i = base + Z.of_nat c ->
nth_error l (Z.to_nat i) = nth_error xs c.
Proof.
intros l xs base k c i H Hb Hc ->. rewrite <- H. rewrite nth_error_firstn.
replace (Nat.ltb c k) with true by (symmetry; apply Nat.ltb_lt; lia).
rewrite nth_error_skipn. f_equal. lia.
Qed.

Lemma window_sub : forall (l xs : list byte) (base : Z) (k c j : nat) (i : Z),
firstn k (skipn (Z.to_nat base) l) = xs -> (0 <= base)%Z -> (c + j <= k)%nat -> i = base + Z.of_nat c ->
firstn j (skipn (Z.to_nat i) l) = firstn j (skipn c xs).
Proof.
intros l xs base k c j i H Hb Hc ->. rewrite <- H.
rewrite skipn_firstn_comm, firstn_firstn, skipn_skipn by lia. f_equal; [lia|]. f_equal. lia.
Qed.

Lemma byte_range : forall b : byte, 0 <= bv_unsigned b < 256.
Proof. intros b. pose proof (bv_unsigned_in_range 8 b) as H. unfold bv_modulus in H. cbn in H. cbn. lia. Qed.

Lemma bv_wrap32_eq : forall z, bv_wrap 32 z = z mod 2^32.
Proof. reflexivity. Qed.
Lemma bv_swrap32_eq : forall z, bv_swrap 32 z = (z + 2^31) mod 2^32 - 2^31.
Proof. reflexivity. Qed.

Lemma le_bytes_to_word4 : forall b0 b1 b2 b3 : byte,
bv_unsigned (le_bytes_to_word [b0;b1;b2;b3]) = bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3.
Proof.
intros. unfold le_bytes_to_word. rewrite bytes_le_to_Z_le_val. cbn [map le_val].
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
rewrite unsigned_lit by lia. lia.
Qed.

Lemma lw_unsigned4 : forall b0 b1 b2 b3 : byte,
bv_unsigned (sext 64 (bv_extract 0 32 (le_bytes_to_word [b0;b1;b2;b3]))) =
bv_unsigned b0 + 256 * bv_unsigned b1 + 65536 * bv_unsigned b2 + 16777216 * bv_unsigned b3 + (2^64 - 2^32) * (bv_unsigned b3 / 128).
Proof.
intros. rewrite sext_small, Z_to_bv_unsigned, signed_of_extract, le_bytes_to_word4 by reflexivity.
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
rewrite bv_swrap32_eq. change (bv_wrap 64 ?x) with (x mod 2^64).
Z.div_mod_to_equations. lia.
Qed.

Lemma Z_to_le_bytes_to_Z : forall bs : list byte, Z_to_le_bytes (length bs) (bytes_le_to_Z bs) = bs.
Proof.
induction bs as [|b bs IH]; [reflexivity|]. cbn [length Z_to_le_bytes bytes_le_to_Z].
pose proof (byte_range b) as Hb.
assert (HR : 0 <= bytes_le_to_Z bs). { rewrite bytes_le_to_Z_le_val. apply (proj1 (le_val_range _ (bytes_ok_map bs))). }
rewrite lor_shiftl8_add by lia.
f_equal.
- apply bv_eq. rewrite Z_to_bv_unsigned. change (bv_wrap 8 ?z) with (z mod 2^8)%Z. change (2^8) with 256.
replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
rewrite Z.mod_add by lia. apply Z.mod_small. lia.
- rewrite Z.shiftr_div_pow2 by lia. change (2^8) with 256.
replace (bv_unsigned b + 256 * bytes_le_to_Z bs) with (bv_unsigned b + bytes_le_to_Z bs * 256) by lia.
rewrite Z.div_add, Z.div_small by lia. cbn [Z.add]. exact IH.
Qed.

Lemma le4_of_mod32 : forall (v : word) (bs : list byte), length bs = 4%nat ->
bv_unsigned v mod 2^32 = le_val (map bv_unsigned bs) -> le4 v = bs.
Proof.
intros v bs Hl Hv. unfold le4.
rewrite <- (Z_to_le_bytes_mod 4 _ 32) by (cbn; lia). change (2 ^ 32) with (2^32) in *. rewrite Hv.
rewrite <- bytes_le_to_Z_le_val, <- Hl. apply Z_to_le_bytes_to_Z.
Qed.

Lemma le1_of_mod8 : forall (v : word) (b : byte), bv_unsigned v mod 2^8 = bv_unsigned b -> le1 v = [b].
Proof.
intros v b Hv. unfold le1. rewrite <- (Z_to_le_bytes_mod 1 _ 8) by (cbn; lia). change (2^8) with (2^8) in *. rewrite Hv.
cbn. f_equal. apply bv_eq. rewrite Z_to_bv_unsigned. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

Lemma le1_zxb : forall b : byte, le1 (Z_to_bv 64 (bv_unsigned b)) = [b].
Proof. intros b. apply le1_of_mod8. pose proof (byte_range b). rewrite unsigned_lit by lia. apply Z.mod_small. cbn. lia. Qed.

Lemma le4_lw : forall w : list byte, length w = 4%nat -> le4 (sext 64 (bv_extract 0 32 (le_bytes_to_word w))) = w.
Proof.
intros w Hl. destruct w as [|b0 [|b1 [|b2 [|b3 [|]]]]]; try (cbn in Hl; discriminate).
apply le4_of_mod32; [reflexivity|]. rewrite lw_unsigned4. cbn [map le_val].
pose proof (byte_range b0). pose proof (byte_range b1). pose proof (byte_range b2). pose proof (byte_range b3).
Z.div_mod_to_equations. lia.
Qed.

Lemma lor_add : forall hi lo k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor hi lo = hi + lo.
Proof.
intros hi lo k Hk Hlo Hhi.
assert (HL : Z.land hi lo = 0).
{ rewrite <- (Z.mod_small lo (2^k)) by lia. rewrite <- Z.land_ones by lia.
rewrite (Z.land_comm lo), Z.land_assoc, Z.land_ones, Hhi by lia. apply Z.land_0_l. }
pose proof (Z.add_lor_land hi lo). lia.
Qed.
Lemma lor_add' : forall lo hi k, 0 <= k -> 0 <= lo < 2^k -> hi mod 2^k = 0 -> Z.lor lo hi = lo + hi.
Proof. intros. rewrite Z.lor_comm, (lor_add hi lo k); lia. Qed.

Lemma land_single_bit : forall x k, 0 <= x -> 0 <= k ->
Z.land x (2^k) = if x mod 2^(k+1) <? 2^k then 0 else 2^k.
Proof.
intros x k Hx Hk.
assert (Hpk : 0 < 2^k < 2^(k+1)). { split; [apply Z.pow_pos_nonneg; lia| apply Z.pow_lt_mono_r; lia]. }
rewrite (Z.land_comm x), <- (land_mod_pow2_r (2^k) x (k+1)) by lia.
set (r := x mod 2^(k+1)).
assert (Hr : 0 <= r < 2^(k+1)) by (subst r; apply Z.mod_pos_bound; lia).
rewrite Z.pow_add_r in Hr by lia. change (2^1) with 2 in Hr.
destruct (Z.ltb_spec0 r (2^k)) as [Hl|Hl].
- rewrite Z.land_comm. apply zb_land_pow2_small; lia.
- replace r with (Z.lor (2^k) (r - 2^k)).
2:{ rewrite lor_add with (k := k); try lia. rewrite Z.mod_same; lia. }
rewrite Z.land_lor_distr_r, Z.land_diag, (Z.land_comm (2^k)), zb_land_pow2_small by lia. apply Z.lor_0_r.
Qed.

Lemma land_bit_2 : forall x, 0 <= x -> Z.land x 2 = if x mod 4 <? 2 then 0 else 2.
Proof. intros x Hx. exact (land_single_bit x 1 Hx ltac:(lia)). Qed.
Lemma land_bit_4 : forall x, 0 <= x -> Z.land x 4 = if x mod 8 <? 4 then 0 else 4.
Proof. intros x Hx. exact (land_single_bit x 2 Hx ltac:(lia)). Qed.
Lemma land_bit_8 : forall x, 0 <= x -> Z.land x 8 = if x mod 16 <? 8 then 0 else 8.
Proof. intros x Hx. exact (land_single_bit x 3 Hx ltac:(lia)). Qed.

Lemma land_1 : forall x, Z.land x 1 = x mod 2.
Proof. intros x. change 1 with (2^1 - 1) at 1. rewrite zb_land_mask by lia. reflexivity. Qed.
Lemma land_3 : forall x, Z.land x 3 = x mod 4.
Proof. intros x. change 3 with (2^2 - 1). rewrite zb_land_mask by lia. reflexivity. Qed.

Lemma firstn_S_nth : forall {X} (l : list X) p x, nth_error l p = Some x -> firstn (S p) l = firstn p l ++ [x].
Proof.
intros X l; induction l as [|a l IH]; intros [|p] x H; cbn in *; try discriminate.
- injection H as ->. reflexivity.
- rewrite (IH p x H). reflexivity.
Qed.

End Mq3.

From Stdlib Require Import ZArith NArith List Bool Lia Permutation.
From stdpp Require Import gmap.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCiC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCiC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QKyU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QKyU. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QPa2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QPa2. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QOb0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QOb0.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qt4u.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qt4u.Mq0.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q6sh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q6sh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QQwg.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QQwg. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qpj5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qpj5.Mq0.
Import ListNotations.
Open Scope Z_scope.
Local Open Scope amodel_scope.

Record ghost := mkG { g_chunks : list (Z * Z); g_spent : Z }.

Definition civ (c : Z * Z) : Z * Z := (fst c, fst c + snd c).

Fixpoint remove_first (c : Z * Z) (l : list (Z * Z)) : list (Z * Z) :=
match l with
| [] => []
| x :: l' => if (fst x =? fst c) && (snd x =? snd c) then l' else x :: remove_first c l'
end.

Definition gstep (g : ghost) (e : evA) (a : ansA) : ghost :=
match e, a with
| EvMapAnon len _, AOk b => mkG ((b, len) :: g_chunks g) (g_spent g + sec_cost len)
| EvMapFixed _ len, AOk _ => mkG (g_chunks g) (g_spent g + len)
| EvMunmap a sz, AOk _ => mkG (remove_first (a, sz) (g_chunks g)) (g_spent g)
| _, _ => g
end.

Definition kMaxReq : Z := 2^26.
Definition kMaxChunk : Z := 2^26 + 16384.

Definition kMaxCnt : Z := 32768.

Section WithLayout.
Variable L : ALay.
Variable BUDGET : Z.

Definition in_res (addr len : Z) : Prop :=
al_space_beg L <= addr /\ addr + len <= al_space_beg L + 2^37.
Definition in_parr (addr len : Z) : Prop :=
al_ptrarr L <= addr /\ addr + len <= al_ptrarr L + 8388608.

Definition gev (g : ghost) (e : evA) : Prop :=
match e with
| EvMapAnon len avoid =>
0 < len /\ len mod kPage = 0 /\ len <= kMaxChunk /\
incl avoid (al_avoid L ++ map civ (g_chunks g)) /\ incl (map civ (g_chunks g)) avoid /\
g_spent g + sec_cost len <= BUDGET /\ zlen (g_chunks g) + 1 <= kMaxCnt
| EvMapFixed addr len =>
0 < len /\ len mod kPage = 0 /\ addr mod kPage = 0 /\ (in_res addr len \/ in_parr addr len) /\
g_spent g + len <= BUDGET
| EvRemap pb m =>
0 < m /\ pb mod kPage = 0 /\ m mod kPage = 0 /\
exists c, In c (g_chunks g) /\ shadow_of (fst c) <= pb /\ pb + m <= shadow_of (fst c + snd c - 1) + 1
| EvMunmap a sz => In (a, sz) (g_chunks g) /\ 0 < sz
end.

Fixpoint teva {X} (aok : evA -> ansA -> Prop) (R : ghost -> X -> Prop) (g : ghost) (t : T X) : Prop :=
match t with
| SRet (ROk x) => R g x
| SRet RSpin => True
| SRet (RUnr _) => True
| SVis e k => gev g e /\ forall a, aok e a -> teva aok R (gstep g e a) (k a)
end.

Section Logic.
Variable aok : evA -> ansA -> Prop.

Lemma teva_ret {X} (R : ghost -> X -> Prop) g x : R g x -> teva aok R g (tret x).
Proof. intros H; exact H. Qed.
Lemma teva_spin {X} (R : ghost -> X -> Prop) g : teva aok R g (@tspin X).
Proof. exact I. Qed.
Lemma teva_unr {X} (R : ghost -> X -> Prop) g w : teva aok R g (@tunr X w).
Proof. exact I. Qed.

Lemma teva_mono {X} (R R' : ghost -> X -> Prop) g (t : T X) :
teva aok R g t -> (forall g' x, R g' x -> R' g' x) -> teva aok R' g t.
Proof.
revert g. induction t as [[x| |w]|e k IH]; intros g H HR; cbn in *; auto.
destruct H as [He Hk]. split; [exact He|]. intros a Ha. apply IH; auto.
Qed.

Lemma teva_bind {X Y} (R1 : ghost -> X -> Prop) (P1 : X -> Prop) (R : ghost -> Y -> Prop) g (t : T X) (f : X -> T Y) :
teva aok R1 g t -> tall aok (rok P1) t ->
(forall g' x, R1 g' x -> P1 x -> teva aok R g' (f x)) ->
teva aok R g (tbind t f).
Proof.
revert g. unfold tbind. induction t as [[x| |w]|e k IH]; intros g Ht Hp Hf; cbn in *; auto.
destruct Ht as [He Hk]. split; [exact He|]. intros a Ha. apply IH; auto.
Qed.

Lemma teva_bind_simple {X Y} (R1 : ghost -> X -> Prop) (R : ghost -> Y -> Prop) g (t : T X) (f : X -> T Y) :
teva aok R1 g t -> (forall g' x, R1 g' x -> teva aok R g' (f x)) -> teva aok R g (tbind t f).
Proof.
revert g. unfold tbind. induction t as [[x| |w]|e k IH]; intros g Ht Hf; cbn in *; auto.
destruct Ht as [He Hk]. split; [exact He|]. intros a Ha. apply IH; auto.
Qed.
End Logic.

Definition csum (s : AState) : Z :=
zsum (map (fun c => c_mapped_user (cls s c) + c_mapped_fa (cls s c)) (zseqn 1 31)).
Definition SP (s : AState) : Z := csum s + kPtrArrBlockBytes * (as_nres s / kPtrArrBlock) + as_spent s.

Definition gsync (s : AState) (g : ghost) : Prop :=
Permutation (g_chunks g) (map (fun e => (se_beg e, se_size e)) (as_reg s)) /\ g_spent g = SP s.

Definition PERCLS : Z := kFreeArrayOffset + kFreeArraySize.
Definition CAPS : Z := 31 * PERCLS + kPtrArrBlockBytes * 64.

Lemma zsum_map_update (f f' : Z -> Z) (c : Z) l :
List.NoDup l -> In c l -> (forall c', c' <> c -> f' c' = f c') ->
zsum (map f' l) = zsum (map f l) - f c + f' c.
Proof.
induction l as [|x l IH]; intros ND Hin Hf; [destruct Hin|].
inversion ND; subst. cbn [map]. rewrite !zsum_cons.
destruct (Z.eq_dec x c) as [->|Hne].
- assert (E : map f' l = map f l).
{ apply map_ext_in. intros y Hy. apply Hf. intros ->. exact (H1 Hy). }
rewrite E. lia.
- destruct Hin as [->|Hin]; [congruence|]. rewrite (Hf _ Hne), (IH H2 Hin Hf). lia.
Qed.

Lemma zseqn_nodup lo n : List.NoDup (zseqn lo n).
Proof.
unfold zseqn. apply Finite.Injective_map_NoDup; [| apply seq_NoDup]. intros a b H. lia.
Qed.

Lemma csum_only_cls c s s' : 1 <= c <= 31 -> only_cls c s s' ->
csum s' = csum s - (c_mapped_user (cls s c) + c_mapped_fa (cls s c)) + (c_mapped_user (cls s' c) + c_mapped_fa (cls s' c)).
Proof.
intros Hc (Hcl & _). unfold csum.
apply (zsum_map_update (fun c0 => c_mapped_user (cls s c0) + c_mapped_fa (cls s c0))
(fun c0 => c_mapped_user (cls s' c0) + c_mapped_fa (cls s' c0)) c (zseqn 1 31)).
- apply zseqn_nodup.
- apply zseqn_spec. lia.
- intros c' Hne. rewrite (Hcl _ Hne). reflexivity.
Qed.

Lemma csum_le_caps s : (forall c, cwf c (cls s c)) -> csum s <= 31 * PERCLS.
Proof.
intros W. unfold csum, PERCLS.
etransitivity; [apply (zsum_map_le _ (fun _ => kFreeArrayOffset + kFreeArraySize))|].
- intros c _. pose proof (cw_mu _ _ (W c)). pose proof (cw_fa _ _ (W c)). lia.
- rewrite zsum_map_const. unfold zlen, zseqn. rewrite length_map, length_seq. lia.
Qed.

Lemma SP_only_cls c s s' : 1 <= c <= 31 -> only_cls c s s' -> as_spent s' = as_spent s ->
SP s' = SP s - (c_mapped_user (cls s c) + c_mapped_fa (cls s c)) + (c_mapped_user (cls s' c) + c_mapped_fa (cls s' c)).
Proof.
intros Hc Ho Hsp. unfold SP. rewrite (csum_only_cls c s s' Hc Ho), Hsp. destruct Ho as (_&_&_&Hn&_). rewrite Hn. lia.
Qed.

Lemma SP_le s : (forall c, cwf c (cls s c)) -> 0 <= as_nres s <= kMaxNumChunks -> SP s <= CAPS + as_spent s.
Proof.
intros W Hn. unfold SP, CAPS. pose proof (csum_le_caps s W).
assert (as_nres s / kPtrArrBlock <= 64) by (apply Z.div_le_upper_bound; unfold kPtrArrBlock, kMaxNumChunks in *; lia).
pose proof (Z.div_pos (as_nres s) kPtrArrBlock ltac:(lia) ltac:(unfold kPtrArrBlock; lia)).
unfold kPtrArrBlockBytes in *. nia.
Qed.

Record lay_ok : Prop := mkLAY {
lo_sb  : al_space_beg L mod 65536 = 0;
lo_sb0 : 0 <= al_space_beg L;
lo_pa  : al_ptrarr L mod kPage = 0;
lo_pa0 : 0 <= al_ptrarr L
}.

Section Prim.
Variable aok : evA -> ansA -> Prop.
Hypothesis LOK : lay_ok.

Definition gpre (s : AState) (g : ghost) : Prop :=
(forall c, cwf c (cls s c)) /\ 0 <= as_nres s <= kMaxNumChunks /\ g_spent g = SP s.

Definition gkeep (s : AState) (g : ghost) (s' : AState) (g' : ghost) : Prop :=
g_chunks g' = g_chunks g /\ as_spent s' = as_spent s /\ as_reg s' = as_reg s /\ gpre s' g'.

Lemma gpre_only_cls c s s' g' : 1 <= c <= 31 -> gpre s (mkG [] 0) \/ True -> (forall c0, cwf c0 (cls s c0)) -> 0 <= as_nres s <= kMaxNumChunks ->
only_cls c s s' -> cwf c (cls s' c) -> as_spent s' = as_spent s -> g_spent g' = SP s' -> gpre s' g'.
Proof.
intros Hc _ W Hn Ho W' Hsp Hg. destruct Ho as (Hcl & _ & _ & Hnr & _). split; [|split; [rewrite Hnr; exact Hn| exact Hg]].
intros c0. destruct (Z.eq_dec c0 c) as [->|Hne]; [exact W'|]. rewrite (Hcl _ Hne). apply W.
Qed.

Local Ltac kconst := unfold kFreeArraySize, kFreeArrayMapSize, kUserMapSize, kFreeArrayOffset, kPage, PERCLS in *.

Lemma ensure_fa_teva g s c nf :
1 <= c <= 31 -> gpre s g -> 0 <= nf -> 4 * nf <= kFreeArraySize ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' r => gkeep s g (snd r) g') g (ensure_fa L s c nf).
Proof.
intros Hc (W & Hn & Hg) Hnf Hcap HB. unfold ensure_fa.
pose proof (W c) as Wc. pose proof (cw_fa _ _ Wc) as Wfa. pose proof (cw_fa_al _ _ Wc) as [k Hk]. pose proof (cw_mu _ _ Wc) as Wmu.
destruct (Z.leb_spec (4 * nf) (c_mapped_fa (cls s c))) as [Hle|Hgt].
{ apply teva_ret. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact W| split; [exact Hn| exact Hg]]. }
assert (Hru : round_up (4 * nf) kFreeArrayMapSize <= kFreeArraySize).
{ apply round_up_le_mul; kconst; [lia| exists 2048; reflexivity| lia]. }
destruct (Z.ltb_spec kFreeArraySize (round_up (4 * nf) kFreeArrayMapSize)); [lia|].
pose proof (round_up_ge (4 * nf) kFreeArrayMapSize ltac:(kconst; lia)) as Hge.
pose proof (round_up_mul (4 * nf) kFreeArrayMapSize ltac:(kconst; lia)) as [k' Hk'].
set (new_fa := round_up (4 * nf) kFreeArrayMapSize) in *.
assert (Hq : exists q, al_space_beg L = 65536 * q).
{ exists (al_space_beg L / 65536). pose proof (Z.div_mod (al_space_beg L) 65536 ltac:(lia)). pose proof (lo_sb LOK). lia. }
destruct Hq as [q Hq].
split.
-
cbn [gev]. pose proof (lo_sb0 LOK) as Hsb0.
split; [lia|]. split.
{ kconst. rewrite Hk', Hk. replace (k' * 262144 - k * 262144) with ((k' - k) * 64 * 4096) by lia. apply Z_mod_mult. }
split.
{ unfold fa_beg, reg_beg, kRegionSize, kFreeArrayOffset. rewrite Hk, Hq. kconst. change (2 ^ 32) with 4294967296.
replace (65536 * q + c * 4294967296 + 3758096384 + k * 262144) with ((16 * q + c * 1048576 + 917504 + k * 64) * 4096) by lia.
apply Z_mod_mult. }
split.
{ left. unfold in_res, fa_beg, reg_beg, kRegionSize, kFreeArrayOffset. kconst. change (2 ^ 32) with 4294967296. change (2 ^ 37) with 137438953472.
pose proof (cw_nf _ _ Wc). split. { assert (0 <= c * 4294967296) by nia. lia. } assert (c * 4294967296 <= 31 * 4294967296) by nia. lia. }
rewrite Hg.

assert (W' : forall c0, cwf c0 (cls (set_cls c (set_mapped_fa new_fa (cls s c)) s) c0)).
{ intros c0. destruct (Z.eq_dec c0 c) as [->|Hne]; [rewrite cls_set_cls_eq| rewrite cls_set_cls_ne by exact Hne; apply W].
pose proof (cw_cnt _ _ Wc). pose proof (cw_au _ _ Wc). pose proof (cw_nf _ _ Wc).
constructor; cbn; try lia; [apply (cw_mu_al _ _ Wc)| exists k'; exact Hk']. }
pose proof (SP_only_cls c s (set_cls c (set_mapped_fa new_fa (cls s c)) s) Hc (only_cls_set_cls c _ s) eq_refl) as E.
rewrite cls_set_cls_eq in E. cbn in E.
pose proof (SP_le (set_cls c (set_mapped_fa new_fa (cls s c)) s) W' Hn) as HSP'. cbn [as_spent set_cls] in HSP'.
change (as_spent (set_cls c (set_mapped_fa new_fa (cls s c)) s)) with (as_spent s) in HSP'.
lia.
- intros a _. destruct a as [|b]; cbn [fixed_ok gstep].
+ apply teva_ret. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact W| split; [exact Hn| exact Hg]].
+ apply teva_ret. cbn [snd]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
eapply (gpre_only_cls c s); auto.
* apply only_cls_set_cls.
* rewrite cls_set_cls_eq. pose proof (cw_cnt _ _ Wc). pose proof (cw_au _ _ Wc). pose proof (cw_nf _ _ Wc).
constructor; cbn; try lia; [apply (cw_mu_al _ _ Wc)| exists k'; exact Hk'].
* cbn [g_spent]. rewrite Hg, (SP_only_cls c s _ Hc (only_cls_set_cls c _ s) eq_refl), cls_set_cls_eq. cbn. lia.
Qed.

Lemma populate_teva g s c req :
1 <= c <= 31 -> gpre s g -> 1 <= req ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
c_alloc_user (cls s c) + req * class_size c <= kFreeArrayOffset ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' r => gkeep s g (snd r) g') g (populate L s c req).
Proof.
intros Hc Gp Hreq Hnf Hroom HB. pose proof Gp as (W & Hn & Hg). unfold populate.
pose proof (class_facts c Hc) as (Hsz & _ & _).
pose proof (W c) as Wc. pose proof (cw_au _ _ Wc) as Wau. pose proof (cw_mu _ _ Wc) as Wmu. pose proof (cw_nf _ _ Wc) as Wnf.
pose proof (cw_mu_al _ _ Wc) as [k Hk]. pose proof (cw_fa _ _ Wc) as Wfa. pose proof (cw_fa_al _ _ Wc) as Wfal. pose proof (cw_cnt _ _ Wc) as Wcnt.
assert (Hq : exists q, al_space_beg L = 65536 * q).
{ exists (al_space_beg L / 65536). pose proof (Z.div_mod (al_space_beg L) 65536 ltac:(lia)). pose proof (lo_sb LOK). lia. }
destruct Hq as [q Hq]. pose proof (lo_sb0 LOK) as Hsb0.
set (size := class_size c) in *. set (total := c_alloc_user (cls s c) + req * size).

set (R1 := fun (g1 : ghost) (r : bool * AState) => let '(ok, s1) := r in
gkeep s g s1 g1 /\ only_cls c s s1 /\ cwf c (cls s1 c) /\
c_alloc_user (cls s1 c) = c_alloc_user (cls s c) /\ c_num_freed (cls s1 c) = c_num_freed (cls s c) /\
(ok = true -> total <= c_mapped_user (cls s1 c))).
apply (teva_bind_simple aok R1).
{ destruct (Z.ltb_spec (c_mapped_user (cls s c)) total) as [Hlt|Hge].
- set (msz := round_up (total - c_mapped_user (cls s c)) kUserMapSize).
assert (Hshift : c_mapped_user (cls s c) + msz = round_up total kUserMapSize).
{ subst msz. apply round_up_shift; [kconst; lia| exists k; exact Hk]. }
assert (Hru : round_up total kUserMapSize <= kFreeArrayOffset).
{ apply round_up_le_mul; [kconst; lia| exists 14336; reflexivity| subst total size; lia]. }
pose proof (round_up_mul (total - c_mapped_user (cls s c)) kUserMapSize ltac:(kconst; lia)) as [k' Hk']. fold msz in Hk'.
pose proof (round_up_ge (total - c_mapped_user (cls s c)) kUserMapSize ltac:(kconst; lia)) as Hge'. fold msz in Hge'.
destruct (Z.ltb_spec kFreeArrayOffset (c_mapped_user (cls s c) + msz)); [lia|].
assert (W' : forall c0, cwf c0 (cls (set_cls c (set_mapped_user (c_mapped_user (cls s c) + msz) (cls s c)) s) c0)).
{ intros c0. destruct (Z.eq_dec c0 c) as [->|Hne]; [rewrite cls_set_cls_eq| rewrite cls_set_cls_ne by exact Hne; apply W].
constructor; cbn; try lia; [exists (k + k'); lia| exact Wfal]. }
split.
+ cbn [gev]. split; [lia|]. split; [rewrite Hk'; kconst; replace (k' * 262144) with (k' * 64 * 4096) by lia; apply Z_mod_mult|].
split.
{ unfold reg_beg, kRegionSize. rewrite Hk, Hq. kconst. change (2 ^ 32) with 4294967296.
replace (65536 * q + c * 4294967296 + k * 262144) with ((16 * q + c * 1048576 + k * 64) * 4096) by lia. apply Z_mod_mult. }
split.
{ left. unfold in_res, reg_beg, kRegionSize. kconst. change (2 ^ 32) with 4294967296. change (2 ^ 37) with 137438953472.
split. { assert (0 <= c * 4294967296) by nia. lia. } assert (c * 4294967296 <= 31 * 4294967296) by nia. lia. }
rewrite Hg.
pose proof (SP_only_cls c s (set_cls c (set_mapped_user (c_mapped_user (cls s c) + msz) (cls s c)) s) Hc (only_cls_set_cls c _ s) eq_refl) as E.
rewrite cls_set_cls_eq in E. cbn in E.
pose proof (SP_le (set_cls c (set_mapped_user (c_mapped_user (cls s c) + msz) (cls s c)) s) W' Hn) as HSP'.
change (as_spent (set_cls c _ s)) with (as_spent s) in HSP'. lia.
+ intros a _. destruct a as [|b]; cbn [fixed_ok gstep].
* apply teva_ret. subst R1. cbn. split; [split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact Gp]|].
split; [apply only_cls_refl|]. split; [exact Wc|]. repeat split; try lia. all: intros; discriminate.
* set (s1 := set_cls c (set_mapped_user (c_mapped_user (cls s c) + msz) (cls s c)) s) in *.
assert (Wc' : cwf c (cls s1 c)) by (specialize (W' c); exact W').
assert (E1 : cls s1 c = set_mapped_user (c_mapped_user (cls s c) + msz) (cls s c)) by (subst s1; apply cls_set_cls_eq).
assert (Gp' : gpre s1 (mkG (g_chunks g) (g_spent g + msz))).
{ apply (gpre_only_cls c s s1 _ Hc (or_intror I) W Hn (only_cls_set_cls c _ s) Wc' eq_refl).
cbn [g_spent]. rewrite Hg, (SP_only_cls c s s1 Hc (only_cls_set_cls c _ s) eq_refl), E1. cbn. lia. }
apply teva_ret. subst R1. cbn [snd].
split; [split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact Gp']|].
split; [apply only_cls_set_cls|]. split; [exact Wc'|]. rewrite E1. cbn. repeat split; try lia.
- apply teva_ret. subst R1. cbn. split; [split; [reflexivity|]; split; [reflexivity|]; split; [reflexivity| exact Gp]|].
split; [apply only_cls_refl|]. split; [exact Wc|]. repeat split; try lia. }

intros g1 [ok s1] H1. subst R1. cbn beta iota in H1.
destruct H1 as ((Gc & Gsp & Gr & Gp1) & Ho1 & W1 & Eau & Enf & Hok).
destruct ok; cbn [negb].
2: { apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr| exact Gp1]. }
specialize (Hok eq_refl).
pose proof (cw_au _ _ W1) as W1au. pose proof (cw_mu _ _ W1) as W1mu. pose proof (cw_nf _ _ W1) as W1nf.
set (newc := (c_mapped_user (cls s1 c) - c_alloc_user (cls s1 c)) / size).
assert (Hnewc : 0 <= newc) by (subst newc; apply Z.div_pos; lia).
assert (Htf : 4 * (c_num_freed (cls s1 c) + newc) <= kFreeArraySize).
{ assert (c_num_freed (cls s1 c) <= c_alloc_user (cls s1 c) / size) by (apply div_le_of_mul_le; [lia|]; rewrite Enf, Eau; lia).
pose proof (div_add_le (c_alloc_user (cls s1 c)) (c_mapped_user (cls s1 c) - c_alloc_user (cls s1 c)) size ltac:(lia)) as Hd.
replace (c_alloc_user (cls s1 c) + (c_mapped_user (cls s1 c) - c_alloc_user (cls s1 c))) with (c_mapped_user (cls s1 c)) in Hd by lia.
assert (c_mapped_user (cls s1 c) / size <= kFreeArrayOffset / 32).
{ etransitivity; [apply (Z.div_le_mono _ kFreeArrayOffset); lia|]. apply Z.div_le_compat_l; kconst; lia. }
subst newc. kconst. change (3758096384 / 32) with 117440512 in *. lia. }
eapply (teva_bind aok (fun g' r => gkeep s1 g1 (snd r) g')
(fun r => let '(ok, s') := r in only_cls c s1 s' /\
c_mapped_user (cls s' c) = c_mapped_user (cls s1 c) /\ c_alloc_user (cls s' c) = c_alloc_user (cls s1 c) /\
c_num_freed (cls s' c) = c_num_freed (cls s1 c) /\ c_count (cls s' c) = c_count (cls s1 c) /\
c_mapped_fa (cls s1 c) <= c_mapped_fa (cls s' c) <= kFreeArraySize /\ (kFreeArrayMapSize | c_mapped_fa (cls s' c)) /\
(ok = true -> 4 * (c_num_freed (cls s1 c) + newc) <= c_mapped_fa (cls s' c)))).
- apply ensure_fa_teva; auto; [lia| rewrite Gsp; exact HB].
- apply ensure_fa_spec; [exact W1| lia| exact Htf].
- intros g2 [ok2 s2] (Gc2 & Gsp2 & Gr2 & Gp2) (Ho2 & Emu2 & Eau2 & Enf2 & Ecnt2 & Hfa2 & Hfal2 & Hok2). cbn [snd] in *.
destruct ok2; cbn [negb].
+ apply teva_ret. cbn [snd]. destruct Gp2 as (W2 & Hn2 & Hg2).
split; [congruence|]. split; [cbn; congruence|]. split; [cbn; congruence|].
eapply (gpre_only_cls c s2); auto.
* apply only_cls_set_cls.
* rewrite cls_set_cls_eq. specialize (W2 c). pose proof (cw_fa _ _ W2). pose proof (cw_cnt _ _ W2). pose proof (cw_au _ _ W2). pose proof (cw_mu _ _ W2). pose proof (cw_nf _ _ W2).
assert (newc * size <= c_mapped_user (cls s1 c) - c_alloc_user (cls s1 c)) by (subst newc; rewrite Z.mul_comm; apply Z.mul_div_le; lia).
constructor; cbn; rewrite ?Eau2, ?Emu2, ?Enf2 in *; try lia; [first [apply (cw_mu_al _ _ W1) | apply (cw_mu_al _ _ W2)]| exact Hfal2].
* rewrite Hg2, (SP_only_cls c s2 _ Hc (only_cls_set_cls c _ s2) eq_refl), cls_set_cls_eq. cbn. lia.
+ apply teva_ret. cbn [snd]. split; [congruence|]. split; [congruence|]. split; [congruence| exact Gp2].
Qed.

Lemma get_from_allocator_teva g s c k :
1 <= c <= 31 -> gpre s g -> 1 <= k ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_num_freed (cls s c) < k -> c_alloc_user (cls s c) + k * class_size c <= kFreeArrayOffset) ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' r => gkeep s g (snd r) g') g (get_from_allocator L s c k).
Proof.
intros Hc Gp Hk Hnf Hroom HB. pose proof Gp as (W & Hn & Hg). unfold get_from_allocator.
pose proof (class_facts c Hc) as (Hsz & _ & _). pose proof (cw_nf _ _ (W c)) as Wnf.
eapply (teva_bind aok (fun g' r => gkeep s g (snd r) g') (fun r => populate_post s c (k - c_num_freed (cls s c)) r \/ r = (true, s))).
- destruct (Z.ltb_spec (c_num_freed (cls s c)) k) as [Hlt|Hge].
+ apply populate_teva; auto; [lia| specialize (Hroom Hlt); nia].
+ apply teva_ret. cbn [snd]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Gp].
- destruct (Z.ltb_spec (c_num_freed (cls s c)) k) as [Hlt|Hge].
+ eapply tall_mono; [apply (populate_spec L aok); auto; try lia; specialize (Hroom Hlt); nia|]. intros [x| |w]; cbn; auto.
+ apply tall_rok_ret. right. reflexivity.
- intros g1 [ok s1] (Gc & Gsp & Gr & Gp1) Hp. cbn [snd] in *.
destruct ok; cbn [negb].
2: { apply teva_ret. cbn [snd]. repeat split; auto; apply Gp1. }
destruct (Z.ltb_spec (c_num_freed (cls s1 c)) k); [apply teva_unr|].
apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr|].
destruct Gp1 as (W1 & Hn1 & Hg1).
assert (Wc1 : cwf c (cls s1 c)) by apply W1.
apply (gpre_only_cls c s1 _ _ Hc (or_intror I) W1 Hn1 (only_cls_set_cls c _ s1)).
+ rewrite cls_set_cls_eq. pose proof (cw_cnt _ _ Wc1). pose proof (cw_au _ _ Wc1). pose proof (cw_mu _ _ Wc1). pose proof (cw_fa _ _ Wc1). pose proof (cw_nf _ _ Wc1).
constructor; cbn; try lia; [apply (cw_mu_al _ _ Wc1)| apply (cw_fa_al _ _ Wc1)].
+ reflexivity.
+ rewrite Hg1, (SP_only_cls c s1 _ Hc (only_cls_set_cls c _ s1) eq_refl), cls_set_cls_eq. cbn. lia.
Qed.

Lemma refill_teva g s c :
1 <= c <= 31 -> gpre s g -> c_count (cls s c) = 0 ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_num_freed (cls s c) < 8 -> c_alloc_user (cls s c) + 8 * class_size c <= kFreeArrayOffset) ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' r => gkeep s g (snd r) g') g (refill L s c).
Proof.
intros Hc Gp Hcnt Hnf Hroom HB. pose proof Gp as (W & Hn & Hg). unfold refill.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev).
assert (Gp0 : gpre (set_inited s) g) by exact Gp.
eapply (teva_bind aok (fun g' r => gkeep (set_inited s) g (snd r) g') (gfa_post (set_inited s) c (max_count c / 2))).
- apply get_from_allocator_teva; rewrite ?cls_set_inited; auto; try lia. intros Hlt. specialize (Hroom ltac:(lia)). nia.
- apply (get_from_allocator_spec L aok); rewrite ?cls_set_inited; auto; try lia. intros Hlt. specialize (Hroom ltac:(lia)). nia.
- intros g1 [ok s1] (Gc & Gsp & Gr & Gp1) Hp. cbn [snd] in *. unfold gfa_post in Hp. rewrite !cls_set_inited in Hp.
destruct Hp as (Ho1 & W1c & _).
destruct ok; cbn [negb].
+ apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr|].
destruct Gp1 as (W1 & Hn1 & Hg1).
apply (gpre_only_cls c s1 _ _ Hc (or_intror I) W1 Hn1 (only_cls_upd_cls c _ s1)).
* rewrite cls_upd_cls_eq. pose proof (cw_cnt _ _ W1c). pose proof (cw_au _ _ W1c). pose proof (cw_mu _ _ W1c). pose proof (cw_fa _ _ W1c). pose proof (cw_nf _ _ W1c).
constructor; cbn; try lia; [apply (cw_mu_al _ _ W1c)| apply (cw_fa_al _ _ W1c)].
* reflexivity.
* rewrite Hg1, (SP_only_cls c s1 _ Hc (only_cls_upd_cls c _ s1) eq_refl), cls_upd_cls_eq. cbn. lia.
+ apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr| exact Gp1].
Qed.

Lemma cache_alloc_teva g s c :
1 <= c <= 31 -> gpre s g ->
class_size c * c_num_freed (cls s c) <= c_alloc_user (cls s c) ->
(c_count (cls s c) = 0 -> c_num_freed (cls s c) < 8 -> c_alloc_user (cls s c) + 8 * class_size c <= kFreeArrayOffset) ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' r => gkeep s g (snd r) g') g (cache_alloc L s c).
Proof.
intros Hc Gp Hnf Hroom HB. pose proof Gp as (W & Hn & Hg). unfold cache_alloc.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev).
eapply (teva_bind aok (fun g' r => gkeep s g (snd r) g') (fun r => refill_post s c r \/ (r = (true, s) /\ 0 < c_count (cls s c)))).
- destruct (Z.eqb_spec (c_count (cls s c)) 0) as [H0|Hn0].
+ apply refill_teva; auto.
+ apply teva_ret. cbn [snd]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Gp].
- destruct (Z.eqb_spec (c_count (cls s c)) 0) as [H0|Hn0].
+ eapply tall_mono; [apply (refill_spec L aok); auto|]. intros [x| |w]; cbn; auto.
+ apply tall_rok_ret. right. pose proof (cw_cnt _ _ (W c)). split; [reflexivity| lia].
- intros g1 [ok s1] (Gc & Gsp & Gr & Gp1) Hp. cbn [snd] in *.
destruct ok; cbn [negb].
2: { apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr| exact Gp1]. }
apply teva_ret. cbn [snd]. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr|].
destruct Gp1 as (W1 & Hn1 & Hg1). pose proof (W1 c) as W1c.
apply (gpre_only_cls c s1 _ _ Hc (or_intror I) W1 Hn1 (only_cls_upd_cls c _ s1)).
+ rewrite cls_upd_cls_eq. pose proof (cw_cnt _ _ W1c). pose proof (cw_au _ _ W1c). pose proof (cw_mu _ _ W1c). pose proof (cw_fa _ _ W1c). pose proof (cw_nf _ _ W1c).
assert (Hpos : 1 <= c_count (cls s1 c)).
{ destruct Hp as [Hp| [Hp Hpos]]; [| injection Hp as ->; lia]. unfold refill_post in Hp. destruct Hp as (_ & _ & _ & _ & _ & Hcnt). rewrite Hcnt. lia. }
constructor; cbn; try lia; [apply (cw_mu_al _ _ W1c)| apply (cw_fa_al _ _ W1c)].
+ reflexivity.
+ rewrite Hg1, (SP_only_cls c s1 _ Hc (only_cls_upd_cls c _ s1) eq_refl), cls_upd_cls_eq. cbn. lia.
Qed.

Lemma return_to_allocator_teva g s c k :
1 <= c <= 31 -> gpre s g -> 0 <= k ->
class_size c * (c_num_freed (cls s c) + k) <= c_alloc_user (cls s c) ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' s' => gkeep s g s' g') g (return_to_allocator L s c k).
Proof.
intros Hc Gp Hk Hle HB. pose proof Gp as (W & Hn & Hg). unfold return_to_allocator.
pose proof (class_facts c Hc) as (Hsz & _ & _). pose proof (W c) as Wc.
pose proof (cw_nf _ _ Wc) as Wnf. pose proof (cw_au _ _ Wc) as Wau. pose proof (cw_mu _ _ Wc) as Wmu.
assert (Htf : 4 * (c_num_freed (cls s c) + k) <= kFreeArraySize).
{ assert (c_num_freed (cls s c) + k <= c_alloc_user (cls s c) / class_size c) by (apply div_le_of_mul_le; lia).
assert (c_alloc_user (cls s c) / class_size c <= kFreeArrayOffset / 32).
{ etransitivity; [apply (Z.div_le_mono _ kFreeArrayOffset); lia|]. apply Z.div_le_compat_l; kconst; lia. }
kconst. change (3758096384 / 32) with 117440512 in *. lia. }
eapply (teva_bind aok (fun g' r => gkeep s g (snd r) g')).
- apply ensure_fa_teva; auto; lia.
- apply (ensure_fa_spec L aok); [exact Wc| lia| exact Htf].
- intros g1 [ok s1] (Gc & Gsp & Gr & Gp1) (Ho1 & Emu & Eau & Enf & Ecnt & Hfa & Hfal & Hok). cbn [snd] in *.
destruct ok; cbn [negb]; [|apply teva_spin].
apply teva_ret. split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr|].
destruct Gp1 as (W1 & Hn1 & Hg1). pose proof (W1 c) as W1c.
apply (gpre_only_cls c s1 _ _ Hc (or_intror I) W1 Hn1 (only_cls_upd_cls c _ s1)).
+ rewrite cls_upd_cls_eq. pose proof (cw_cnt _ _ W1c). pose proof (cw_au _ _ W1c). pose proof (cw_mu _ _ W1c). pose proof (cw_fa _ _ W1c). pose proof (cw_nf _ _ W1c).
specialize (Hok eq_refl). constructor; cbn; rewrite ?Emu, ?Eau, ?Ecnt in *; try lia; [first [apply (cw_mu_al _ _ Wc) | apply (cw_mu_al _ _ W1c)] | exact Hfal].
+ reflexivity.
+ rewrite Hg1, (SP_only_cls c s1 _ Hc (only_cls_upd_cls c _ s1) eq_refl), cls_upd_cls_eq. cbn. lia.
Qed.

Lemma cache_dealloc_teva g s c :
1 <= c <= 31 -> gpre s g ->
class_size c * (c_num_freed (cls s c) + c_count (cls s c)) + class_size c <= c_alloc_user (cls s c) ->
CAPS + as_spent s <= BUDGET ->
teva aok (fun g' s' => gkeep s g s' g') g (cache_dealloc L s c).
Proof.
intros Hc Gp Hle HB. pose proof Gp as (W & Hn & Hg). unfold cache_dealloc. rewrite !cls_set_inited.
pose proof (class_facts c Hc) as (Hsz & Hmc & Hev). pose proof (W c) as Wc.
pose proof (cw_nf _ _ Wc) as Wnf. pose proof (cw_au _ _ Wc) as Wau. pose proof (cw_mu _ _ Wc) as Wmu. pose proof (cw_cnt _ _ Wc) as Wcnt. pose proof (cw_fa _ _ Wc) as Wfa.
set (s0 := upd_cls c (set_count (c_count (cls s c) - max_count c / 2)) (set_inited s)).
eapply (teva_bind aok (fun g' s1 => gkeep s g s1 g') (fun s1 => only_cls c s s1 /\ cwf c (cls s1 c) /\ c_count (cls s1 c) + 1 <= max_count c)).
- destruct (Z.eqb_spec (c_count (cls s c)) (max_count c)) as [Heq|Hne].
+ assert (Gp0 : gpre s0 g).
{ apply (gpre_only_cls c s s0 g Hc (or_intror I) W Hn).
- subst s0. eapply only_cls_trans; [apply only_cls_set_inited| apply only_cls_upd_cls].
- subst s0. rewrite cls_upd_cls_eq, cls_set_inited. constructor; cbn; try lia; [apply (cw_mu_al _ _ Wc)| apply (cw_fa_al _ _ Wc)].
- reflexivity.
- subst s0. rewrite Hg. symmetry. rewrite (SP_only_cls c s (upd_cls c _ (set_inited s)) Hc); [rewrite cls_upd_cls_eq, cls_set_inited; cbn; lia| |reflexivity].
eapply only_cls_trans; [apply only_cls_set_inited| apply only_cls_upd_cls]. }
eapply teva_mono; [apply (return_to_allocator_teva g s0 c (max_count c / 2)); auto; try lia|].
* subst s0. rewrite cls_upd_cls_eq, cls_set_inited. cbn. lia.
* intros g' s1 (Gc & Gsp & Gr & Gp1). split; [exact Gc|]. split; [subst s0; exact Gsp|]. split; [subst s0; exact Gr| exact Gp1].
+ apply teva_ret. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity| exact Gp].
- destruct (Z.eqb_spec (c_count (cls s c)) (max_count c)) as [Heq|Hne].
+ eapply tall_mono.
* apply (return_to_allocator_spec L aok s0 c (max_count c / 2)); subst s0; rewrite ?cls_upd_cls_eq, ?cls_set_inited; cbn; auto; try lia.
constructor; cbn; try lia; [apply (cw_mu_al _ _ Wc)| apply (cw_fa_al _ _ Wc)].
* intros [s1| |w]; cbn; auto. unfold rta_post. subst s0. rewrite !cls_upd_cls_eq, !cls_set_inited. cbn.
intros (Ho1 & W1 & Enf & Ecnt & Eau & Emu). split.
{ eapply only_cls_trans; [apply only_cls_set_inited|]. eapply only_cls_trans; [apply only_cls_upd_cls| exact Ho1]. }
split; [exact W1|]. lia.
+ apply tall_rok_ret. rewrite !cls_set_inited. split; [apply only_cls_set_inited|]. split; [exact Wc| lia].
- intros g1 s1 (Gc & Gsp & Gr & Gp1) (Ho1 & W1c & Hcnt). apply teva_ret.
split; [exact Gc|]. split; [exact Gsp|]. split; [exact Gr|].
destruct Gp1 as (W1 & Hn1 & Hg1).
apply (gpre_only_cls c s1 _ _ Hc (or_intror I) W1 Hn1 (only_cls_upd_cls c _ s1)).
+ rewrite cls_upd_cls_eq. pose proof (cw_cnt _ _ W1c). pose proof (cw_au _ _ W1c). pose proof (cw_mu _ _ W1c). pose proof (cw_fa _ _ W1c). pose proof (cw_nf _ _ W1c).
constructor; cbn; try lia; [apply (cw_mu_al _ _ W1c)| apply (cw_fa_al _ _ W1c)].
+ reflexivity.
+ rewrite Hg1, (SP_only_cls c s1 _ Hc (only_cls_upd_cls c _ s1) eq_refl), cls_upd_cls_eq. cbn. lia.
Qed.
End Prim.

Definition cg (c : Z * Z) : Prop := 0 <= fst c /\ fst c mod kPage = 0 /\ 0 < snd c /\ snd c mod kPage = 0.
Definition gwf (g : ghost) : Prop := Forall cg (g_chunks g).
Definition regl (s : AState) : list (Z * Z) := map (fun e => (se_beg e, se_size e)) (as_reg s).

Lemma remove_first_perm x l : In x l -> Permutation (x :: remove_first x l) l.
Proof.
induction l as [|y l IH]; intros Hin; [destruct Hin|]. cbn [remove_first].
destruct (Z.eqb_spec (fst y) (fst x)) as [E1|N1]; [destruct (Z.eqb_spec (snd y) (snd x)) as [E2|N2]|]; cbn [andb].
- destruct x, y; cbn in *; subst. apply Permutation_refl.
- destruct Hin as [->|Hin]; [congruence|]. etransitivity; [apply perm_swap|]. apply perm_skip. exact (IH Hin).
- destruct Hin as [->|Hin]; [congruence|]. etransitivity; [apply perm_swap|]. apply perm_skip. exact (IH Hin).
Qed.

Lemma remove_first_incl x l : incl (remove_first x l) l.
Proof.
induction l as [|y l IH]; cbn; [apply incl_refl|].
destruct (_ && _); [apply incl_tl, incl_refl|]. intros z [->|Hz]; [left; reflexivity| right; exact (IH _ Hz)].
Qed.

Lemma map_civ_regl s : map civ (regl s) = map sec_iv (as_reg s).
Proof. unfold regl. rewrite map_map. reflexivity. Qed.

Lemma remap_range_some addr size pb m :
remap_range addr size = Some (pb, m) ->
0 < m /\ pb mod kPage = 0 /\ m mod kPage = 0 /\ shadow_of addr <= pb /\ pb + m <= shadow_of addr + size / 8.
Proof.
unfold remap_range. destruct (size / 8 <? kClearShadowMmapThreshold); [discriminate|].
destruct (Z.leb_spec (round_down (shadow_of addr + size / 8) kPage) (round_up (shadow_of addr) kPage)) as [Hle|Hgt]; [discriminate|].
intros H; injection H as <- <-.
pose proof (round_up_ge (shadow_of addr) kPage ltac:(unfold kPage; lia)).
pose proof (round_up_mul (shadow_of addr) kPage ltac:(unfold kPage; lia)) as [k Hk].
pose proof (round_down_mul (shadow_of addr + size / 8) kPage ltac:(unfold kPage; lia)) as [k' Hk'].
assert (round_down (shadow_of addr + size / 8) kPage <= shadow_of addr + size / 8).
{ unfold round_down, kPage. pose proof (Z.div_mod (shadow_of addr + size / 8) 4096 ltac:(lia)). pose proof (Z.mod_pos_bound (shadow_of addr + size / 8) 4096 ltac:(lia)). lia. }
rewrite Hk, Hk' in *. unfold kPage in *. split; [lia|]. split; [apply Z_mod_mult|].
split; [replace (k' * 4096 - k * 4096) with ((k' - k) * 4096) by lia; apply Z_mod_mult|]. lia.
Qed.

Section Sec.
Variable aok : evA -> ansA -> Prop.
Hypothesis LOK : lay_ok.
Hypothesis AOK : forall len avoid b, aok (EvMapAnon len avoid) (AOk b) -> b mod kPage = 0 /\ 0 < b.

Lemma clear_shadow_teva g addr size cb csz :
In (cb, csz) (g_chunks g) ->
cb mod 8 = 0 -> cb <= addr -> 0 <= size -> size mod 8 = 0 -> addr mod 8 = 0 -> addr + size <= cb + csz ->
teva aok (fun g' (_ : unit) => g' = g) g (clear_shadow addr size).
Proof.
intros Hin Hcb Hle Hsz Hsm Ham Hend. unfold clear_shadow.
destruct (remap_range addr size) as [[pb m]|] eqn:E; [|apply teva_ret; reflexivity].
apply remap_range_some in E as (Hm & Hpb & Hmm & Hlo & Hhi).
split.
- cbn [gev]. split; [exact Hm|]. split; [exact Hpb|]. split; [exact Hmm|].
exists (cb, csz). split; [exact Hin|]. cbn [fst snd]. unfold shadow_of in *. split.
+ assert (cb / 8 <= addr / 8) by (apply Z.div_le_mono; lia). lia.
+ assert (addr / 8 + size / 8 <= (cb + csz - 1) / 8 + 1); [|lia].
pose proof (Z.div_mod addr 8 ltac:(lia)) as Da. pose proof (Z.div_mod size 8 ltac:(lia)) as Ds. rewrite Ham in Da. rewrite Hsm in Ds.
assert ((addr + size - 1) / 8 <= (cb + csz - 1) / 8) by (apply Z.div_le_mono; lia).
assert (E1 : (addr + size - 1) / 8 = addr / 8 + size / 8 - 1).
{ replace (addr + size - 1) with ((addr / 8 + size / 8 - 1) * 8 + 7) by lia. rewrite Z.div_add_l by lia. change (7 / 8) with 0. lia. }
lia.
- intros a _. destruct a; cbn [gstep]; [apply teva_spin| apply teva_ret; reflexivity].
Qed.

Lemma not_primary_rz n : 0 <= n -> from_primary n = false -> rz_size n = 2048 /\ 64513 <= n.
Proof.
intros Hn Hp. pose proof (not_primary_ge n Hn Hp) as Hge. split; [|exact Hge].
unfold rz_size. destruct (Z.leb_spec n 48); [lia|]. destruct (Z.leb_spec n 96); [lia|]. destruct (Z.leb_spec n 448); [lia|].
destruct (Z.leb_spec n 3968); [lia|]. destruct (Z.leb_spec n 16128); [lia|]. destruct (Z.leb_spec n 32256); [lia|].
destruct (Z.leb_spec n 64512); lia.
Qed.

Lemma sec_map_size_facts n :
0 <= n -> n <= kMaxReq -> from_primary n = false ->
0 < sec_map_size n /\ sec_map_size n mod kPage = 0 /\ sec_map_size n <= kMaxChunk /\
kSecUserOff + round_down (used_size n) 8 + 8 <= sec_map_size n /\
0 <= round_down (used_size n) 8 /\ round_down (used_size n) 8 mod 8 = 0.
Proof.
intros Hn H39 Hp. pose proof (not_primary_rz n Hn Hp) as [Hrz Hge].
unfold sec_map_size, kSecUserOff.
assert (Hnd : n + rz_size n <= needed n <= n + 8 + rz_size n).
{ unfold needed. pose proof (round_up_ge (Z.max n 8) 8 ltac:(lia)). pose proof (round_up_lt (Z.max n 8) 8 ltac:(lia)). lia. }
pose proof (round_up_ge (needed n + rz_size n) kPage ltac:(unfold kPage; lia)) as R1.
pose proof (round_up_lt (needed n + rz_size n) kPage ltac:(unfold kPage; lia)) as R2.
pose proof (round_up_mul (needed n + rz_size n) kPage ltac:(unfold kPage; lia)) as [k Hk]. rewrite Hk in *.
assert (Hrd : used_size n - 8 < round_down (used_size n) 8 <= used_size n).
{ split; [apply round_down_gt; lia| apply round_down_le; unfold used_size; lia]. }
pose proof (round_down_mul (used_size n) 8 ltac:(lia)) as [m Hm]. rewrite Hm in *.
unfold used_size, kPage in *. split; [lia|]. split; [replace (k * 4096 + 4096) with ((k + 1) * 4096) by lia; apply Z_mod_mult|].
split; [unfold kMaxChunk, kMaxReq in *; change (2 ^ 26) with 67108864 in *; lia|].
split; [lia|]. split; [lia| apply Z_mod_mult].
Qed.

Lemma SP_set_nres_block s : 0 <= as_nres s ->
SP (set_nres (as_nres s + kPtrArrBlock) s) = SP s + kPtrArrBlockBytes.
Proof.
intros H. unfold SP. cbn [as_nres as_spent set_nres].
change (csum (set_nres (as_nres s + kPtrArrBlock) s)) with (csum s).
unfold kPtrArrBlock, kPtrArrBlockBytes. replace (as_nres s + 16384) with (as_nres s + 1 * 16384) by lia.
rewrite Z.div_add by lia. lia.
Qed.

Lemma SP_add_spent_set_reg v r s : SP (add_spent v (set_reg r s)) = SP s + v.
Proof. unfold SP. cbn [as_nres as_spent add_spent set_reg]. change (csum (add_spent v (set_reg r s))) with (csum s). lia. Qed.

Lemma SP_set_reg r s : SP (set_reg r s) = SP s.
Proof. reflexivity. Qed.

Lemma large_alloc_teva g s n :
0 <= n -> n <= kMaxReq -> from_primary n = false ->
(forall c, cwf c (cls s c)) -> 0 <= as_nres s <= kMaxNumChunks -> (kPtrArrBlock | as_nres s) ->
gsync s g -> gwf g ->
CAPS + as_spent s + sec_cost (sec_map_size n) <= BUDGET -> zlen (as_reg s) + 1 <= kMaxCnt ->
teva aok (fun g' r => let '(o, s') := r in
gsync s' g' /\ gwf g' /\ (forall c, cls s' c = cls s c) /\ as_tq s' = as_tq s /\ as_gq s' = as_gq s /\
match o with
| None => s' = s /\ g' = g
| Some mb => as_spent s' = as_spent s + sec_cost (sec_map_size n) /\ In (mb, sec_map_size n) (g_chunks g') /\ cg (mb, sec_map_size n)
end) g (large_alloc L s n).
Proof.
intros Hn H39 Hp W Hnr [q Hq] [GP GS] GW HB Hcnt. unfold large_alloc.
pose proof (sec_map_size_facts n Hn H39 Hp) as (M1 & M2 & M3 & _ & _ & _).
assert (Hlen : zlen (g_chunks g) = zlen (as_reg s)) by (unfold zlen; rewrite (Permutation_length GP); unfold regl; rewrite length_map; reflexivity).
set (msz := sec_map_size n) in *.
pose proof (SP_le s W Hnr) as HSP.
split.
- cbn [gev]. split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
split.
{ unfold avoid_of. rewrite <- map_civ_regl. intros x Hx. apply in_app_iff in Hx as [Hx|Hx]; apply in_app_iff; [left; exact Hx| right].
apply in_map_iff in Hx as (y & <- & Hy). apply in_map. eapply Permutation_in; [apply Permutation_sym; exact GP| exact Hy]. }
split.
{ unfold avoid_of. rewrite <- map_civ_regl. intros x Hx. apply in_app_iff. right.
apply in_map_iff in Hx as (y & <- & Hy). apply in_map. eapply Permutation_in; [exact GP| exact Hy]. }
rewrite GS. lia.
- intros a Ha. destruct a as [|mb].
{ cbn [gstep]. apply teva_ret. split; [split; assumption|]. split; [exact GW|]. repeat split; reflexivity. }
pose proof (AOK _ _ _ Ha) as [Hal Hpos].
cbn [gstep].
destruct (Z.leb_spec kMaxNumChunks (Z.of_nat (length (as_reg s)))) as [|Hlt]; [exact I|].
set (g1 := mkG ((mb, msz) :: g_chunks g) (g_spent g + sec_cost msz)).
apply (teva_bind_simple aok (fun g' s1 => g_chunks g' = (mb, msz) :: g_chunks g /\ g_spent g' = SP s1 + sec_cost msz /\
as_spent s1 = as_spent s /\ as_reg s1 = as_reg s /\ (forall c, cls s1 c = cls s c) /\ as_tq s1 = as_tq s /\ as_gq s1 = as_gq s)).
+ destruct (Z.eqb_spec (Z.of_nat (length (as_reg s))) (as_nres s)) as [Heq|Hne].
* split.
{ cbn [gev g_spent g1]. unfold kPtrArrBlockBytes. split; [lia|]. split; [reflexivity|].
split. { rewrite Hq. pose proof (lo_pa LOK) as P. unfold kPtrArrBlock, kPage in *.
rewrite Z.add_mod, P by lia. replace (8 * (q * 16384)) with ((q * 32) * 4096) by lia. rewrite Z_mod_mult. reflexivity. }
split. { right. unfold in_parr. unfold kMaxNumChunks, kPtrArrBlock in *. split; [lia|]. nia. }
rewrite GS. unfold SP in *. unfold CAPS, kPtrArrBlockBytes, kPtrArrBlock, kMaxNumChunks in *.
pose proof (csum_le_caps s W).
assert (as_nres s / 16384 <= 63) by (apply Z.div_le_upper_bound; [lia|]; nia).
lia. }
intros a2 _. destruct a2; cbn [gstep]; [apply teva_unr|].
apply teva_ret. cbn [g_chunks g_spent g1 as_spent as_reg set_nres as_tq as_gq].
split; [reflexivity|]. split; [rewrite SP_set_nres_block by lia; rewrite GS; lia|]. repeat split; reflexivity.
* apply teva_ret. subst g1. cbn. rewrite GS. repeat split; reflexivity.
+ intros g' s1 (C1 & S1 & A1 & R1 & L1 & T1 & Q1). apply teva_ret.
split.
{ split.
- cbn [as_reg set_reg add_spent]. rewrite C1, R1, map_app. cbn [map].
etransitivity; [| apply Permutation_cons_append]. apply perm_skip. exact GP.
- rewrite SP_add_spent_set_reg. exact S1. }
split; [unfold gwf; rewrite C1; constructor; [| exact GW]; unfold cg; cbn; repeat split; auto; lia|].
split; [intros c; cbn; unfold cls in *; cbn; apply L1|]. split; [exact T1|]. split; [exact Q1|].
split; [cbn; rewrite A1; reflexivity|]. split; [rewrite C1; left; reflexivity|]. unfold cg; cbn; repeat split; auto; lia.
Qed.

Lemma large_dealloc_teva g s a :
gsync s g -> gwf g -> In a (map se_beg (as_reg s)) ->
teva aok (fun g' s' => gsync s' g' /\ gwf g' /\ as_spent s' = as_spent s) g (large_dealloc s a).
Proof.
intros [GP GS] GW Hin. unfold large_dealloc.
pose proof (find_sec_spec a (as_reg s) 0) as F.
destruct (find_sec a (as_reg s) 0) as [[i e]|]; [|exfalso; exact (F Hin)].
destruct F as (_ & Hnth & Hbeg). rewrite Nat.sub_0_r in Hnth.
set (x := (se_beg e, se_size e)).
assert (Hx : In x (g_chunks g)).
{ eapply Permutation_in; [apply Permutation_sym; exact GP|]. unfold regl. apply in_map_iff. exists e. split; [reflexivity|]. eapply nth_error_In; exact Hnth. }
pose proof GW as GW'. unfold gwf in GW'. rewrite List.Forall_forall in GW'. pose proof (GW' _ Hx) as (C1 & C2 & C3 & C4). cbn [fst snd x] in C1, C2, C3, C4.
apply (teva_bind_simple aok (fun g' _ => g' = g)).
- apply (clear_shadow_teva g (se_beg e) (se_size e) (se_beg e) (se_size e)); [exact Hx| | | | | |]; unfold kPage in *; lia.
- intros g' [] ->. split.
+ cbn [gev]. split; [exact Hx| exact C3].
+ intros ans _. destruct ans; cbn [gstep]; [apply teva_spin|]. apply teva_ret.
split; [|split; [| reflexivity]].
* split; [| rewrite SP_set_reg; exact GS]. cbn [g_chunks as_reg set_reg].
apply (Permutation_cons_inv (a := x)). etransitivity; [apply remove_first_perm; exact Hx|].
etransitivity; [exact GP|]. unfold regl. cbn [as_reg].
change (x :: map (fun e0 => (se_beg e0, se_size e0)) (swap_remove i (as_reg s))) with (map (fun e0 => (se_beg e0, se_size e0)) (e :: swap_remove i (as_reg s))).
apply Permutation_map. apply Permutation_sym. apply swap_remove_perm. exact Hnth.
* unfold gwf. cbn [g_chunks]. apply (incl_Forall (l1 := g_chunks g)); [apply remove_first_incl| exact GW].
Qed.
End Sec.

Section Ops.
Variable aok : evA -> ansA -> Prop.
Hypothesis LOK : lay_ok.
Hypothesis AOK : forall len avoid b, aok (EvMapAnon len avoid) (AOk b) -> b mod kPage = 0 /\ 0 < b.

Definition GS (s : AState) (g : ghost) : Prop := gsync s g /\ gwf g.

Definition mcost (n : Z) : Z := if from_primary n then 0 else sec_cost (sec_map_size n).

Lemma GS_gpre X E B s g : ainvx X E B s -> GS s g -> gpre s g.
Proof.
intros AI [[_ Hsp] _]. split; [apply (ai_cls _ _ _ _ AI)|]. split; [| exact Hsp].
pose proof (ai_nres _ _ _ _ AI) as (_ & H & _). exact H.
Qed.

Lemma gkeep_GS s g s' g' : GS s g -> gkeep s g s' g' -> GS s' g' /\ as_spent s' = as_spent s.
Proof.
intros [[GP GSp] GW] (Hc & Hsp & Hr & (_ & _ & Hg')). split; [|exact Hsp]. split; [split; [|exact Hg']|].
- rewrite Hc. unfold regl in *. rewrite Hr. exact GP.
- unfold gwf. rewrite Hc. exact GW.
Qed.

Lemma GS_frame s s' g : as_reg s' = as_reg s -> SP s' = SP s -> GS s g -> GS s' g.
Proof. intros Hr Hsp [[GP GSp] GW]. split; [split; [unfold regl; rewrite Hr; exact GP| rewrite Hsp; exact GSp]| exact GW]. Qed.

Theorem asan_malloc_teva X g s n :
ainv X s -> 0 <= n -> n <= kMaxReq ->
(from_primary n = true -> class_size (class_of n) * (tot X [] 0 s (class_of n) + 17) <= kFreeArrayOffset) ->
GS s g -> CAPS + as_spent s + mcost n <= BUDGET -> zlen (as_reg s) + 1 <= kMaxCnt ->
teva aok (fun g' r => GS (snd r) g' /\
as_spent (snd r) <= as_spent s + match fst r with None => 0 | Some _ => mcost n end) g (asan_malloc L s n).
Proof.
intros [AI QB] Hn H39 Hroom G HB Hcnt. unfold asan_malloc, mcost in *.
destruct (too_big n); [exact I|].
destruct (from_primary n) eqn:Hp.
- specialize (Hroom eq_refl). set (c := class_of n) in *.
pose proof (class_of_facts n Hn Hp) as (Hc & Hum & Hneed). fold c in Hc, Hum, Hneed.
assert (Hc31 : 1 <= c <= 31) by lia.
pose proof (class_facts c Hc31) as (Hsz & Hmc & Hev).
pose proof (ai_cons _ _ _ _ AI c Hc31) as Hcons. pose proof (ai_cls _ _ _ _ AI c) as W.
pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_nf _ _ W) as Wnf.
pose proof (tot_nonneg X [] 0 s c ltac:(lia)) as Htot.
assert (Hm1 : 0 <= class_size c * c_count (cls s c)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hm2 : 0 <= class_size c * tot X [] 0 s c) by (apply Z.mul_nonneg_nonneg; lia).
unfold acc in Hcons.
apply (teva_bind_simple aok (fun g' r => gkeep s g (snd r) g')).
{ apply (cache_alloc_teva aok LOK g s c Hc31 (GS_gpre _ _ _ _ _ AI G)); [lia| intros H0 H8; nia| lia]. }
intros g1 [ok s1] K. cbn [snd] in K. pose proof (gkeep_GS _ _ _ _ G K) as [G1 S1].
destruct ok; cbn [negb]; apply teva_ret; cbn [snd].
+ split; [| cbn; rewrite S1; lia]. apply (GS_frame s1); [reflexivity| reflexivity| exact G1].
+ split; [exact G1| cbn; rewrite S1; lia].
- pose proof (ai_nres _ _ _ _ AI) as (N1 & N2 & N3). destruct G as [G1 G2].
apply (teva_bind_simple aok _ _ _ _ _ (large_alloc_teva aok LOK AOK g s n Hn H39 Hp (ai_cls _ _ _ _ AI) N2 N3 G1 G2 HB Hcnt)).
intros g1 [o s1] (Y1 & Y2 & Y3 & Y4 & Y5 & Y6).
destruct o as [mb|].
+ destruct Y6 as (Sp1 & Hin & (C1 & C2 & C3 & C4)). cbn [fst snd] in C1, C2, C3, C4.
pose proof (sec_map_size_facts n Hn H39 Hp) as (M1 & M2 & M3 & M4 & M5 & M6).
apply (teva_bind_simple aok (fun g' _ => g' = g1)).
{ apply (clear_shadow_teva aok g1 (mb + kSecUserOff) (round_down (used_size n) 8) mb (sec_map_size n) Hin);
unfold kSecUserOff, kPage in *; try lia. }
intros g' [] ->. apply teva_ret. cbn [fst snd]. rewrite ?Hp. split; [split; assumption| lia].
+ destruct Y6 as [-> ->]. apply teva_ret. cbn [fst snd]. split; [split; assumption| lia].
Qed.

Let Q (s : AState) : ghost -> AState -> Prop := fun g' s' => GS s' g' /\ as_spent s' = as_spent s.

Lemma recycle_chunk_teva X p E B g s :
ainvx X (p :: E) B s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (recycle_chunk L s p).
Proof.
intros AI G HB. unfold recycle_chunk.
pose proof (ai_pwf _ _ _ _ AI) as PW. unfold allptrs in PW. rewrite List.Forall_forall in PW.
assert (Hp : In p (X ++ (p :: E) ++ qchunks (as_tq s) ++ qchunks (as_gq s))) by (apply in_or_app; right; left; reflexivity).
specialize (PW _ Hp).
destruct p as [id n|a n]; cbn in PW.
- destruct PW as (Hid & Hn & Hprim).
pose proof (class_of_facts n Hn Hprim) as (Hc & _ & _). set (c := class_of n) in *.
assert (Hc31 : 1 <= c <= 31) by lia. pose proof (class_facts c Hc31) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI c Hc31) as Hcons.
assert (Htot1 : 1 <= tot X (APrim id n :: E) B s c).
{ unfold tot, allptrs. repeat rewrite cntc_app. rewrite cntc_cons. cbn [is_cls]. fold c. rewrite Z.eqb_refl.
pose proof (cntc_nonneg c X). pose proof (cntc_nonneg c E). pose proof (cntc_nonneg c (qchunks (as_tq s))). pose proof (cntc_nonneg c (qchunks (as_gq s))).
pose proof (nbat_nonneg (as_tq s)). pose proof (nbat_nonneg (as_gq s)). pose proof (ai_B _ _ _ _ AI).
destruct (c =? kBatchClass); lia. }
assert (Hm : class_size c * 1 <= class_size c * tot X (APrim id n :: E) B s c) by (apply Z.mul_le_mono_nonneg_l; lia).
eapply teva_mono; [apply (cache_dealloc_teva aok LOK g s c Hc31 (GS_gpre _ _ _ _ _ AI G)); [unfold acc in Hcons; lia| exact HB]|].
intros g' s' K. exact (gkeep_GS _ _ _ _ G K).
- destruct PW as (Hn & Hsec).
assert (Hin : In (a, n) (reg_pairs (as_reg s))).
{ eapply Permutation_in; [apply Permutation_sym; apply (ai_reg _ _ _ _ AI)|]. apply in_secs_allptrs. exact Hp. }
destruct G as [G1 G2]. eapply teva_mono; [apply (large_dealloc_teva aok g s a G1 G2)|].
+ unfold reg_pairs in Hin. apply in_map_iff in Hin as (e & He & Hine). apply in_map_iff. exists e. injection He as H1 H2. auto.
+ intros g' s' (A1 & A2 & A3). split; [split; assumption| exact A3].
Qed.

Lemma recycle_chunks_teva X ps : forall E B g s,
ainvx X (ps ++ E) B s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (recycle_chunks L s ps).
Proof.
induction ps as [|p ps IH]; intros E B g s AI G HB; cbn [recycle_chunks app] in *.
- apply teva_ret. split; [exact G| reflexivity].
- eapply (teva_bind aok); [apply (recycle_chunk_teva X p (ps ++ E) B g s AI G HB)| apply (recycle_chunk_inv L aok X p (ps ++ E) B s AI)|].
intros g1 s1 [G1 S1] [AI1 _]. eapply teva_mono; [apply (IH E B g1 s1 AI1 G1); rewrite S1; exact HB|].
intros g2 s2 [G2 S2]. split; [exact G2| rewrite S2; exact S1].
Qed.

Lemma do_recycle_teva X bs : forall g s,
ainvx X (flat_map b_chunks bs) (zlen bs) s -> Forall (bwf 0) bs -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (do_recycle L s bs).
Proof.
induction bs as [|b bs IH]; intros g s AI F G HB; cbn [do_recycle flat_map] in *.
- apply teva_ret. split; [exact G| reflexivity].
- apply Forall_cons_iff in F as [Wb F].
eapply (teva_bind aok); [apply (recycle_chunks_teva X (b_chunks b) (flat_map b_chunks bs) (zlen (b :: bs)) g s AI G HB)
| apply (recycle_chunks_inv L aok X (b_chunks b) (flat_map b_chunks bs) (zlen (b :: bs)) s AI)|].
intros g1 s1 [G1 S1] [AI1 [T1 Q1]].
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI1 _ H24) as Hcons. pose proof (ai_cls _ _ _ _ AI1 kBatchClass) as W.
assert (Htot1 : 1 <= tot X (flat_map b_chunks bs) (zlen (b :: bs)) s1 kBatchClass).
{ unfold tot. rewrite Z.eqb_refl, zlen_cons. pose proof (cntc_nonneg kBatchClass (allptrs X (flat_map b_chunks bs) s1)).
pose proof (nbat_nonneg (as_tq s1)). pose proof (nbat_nonneg (as_gq s1)). pose proof (zlen_nonneg bs). lia. }
assert (Hm : class_size kBatchClass * 1 <= class_size kBatchClass * tot X (flat_map b_chunks bs) (zlen (b :: bs)) s1 kBatchClass)
by (apply Z.mul_le_mono_nonneg_l; lia).
eapply (teva_bind aok (fun g' s' => gkeep s1 g1 s' g') (fun s2 => ainvx X (flat_map b_chunks bs) (zlen bs) s2)).
+ apply (cache_dealloc_teva aok LOK g1 s1 kBatchClass H24 (GS_gpre _ _ _ _ _ AI1 G1)); [unfold acc in Hcons; lia| rewrite S1; exact HB].
+ eapply tall_mono; [apply (cache_dealloc_spec L aok s1 kBatchClass); [exact H24| exact W| unfold acc in Hcons; lia]|].
intros [s2| |w]; cbn; [|auto|auto]. intros (Ho & W2 & Hacc & Eau & Emu).
pose proof Ho as Ho'. destruct Ho as (Hcl & Hnx & Hr & Hnr & Ht & Hg).
eapply (ainvx_reest X (flat_map b_chunks bs) (zlen (b :: bs)) s1 _ _ _ _ kBatchClass (-1) []);
[exact AI1| exact H24| exact Hcl| exact W2| lia| exact Hnx| exact Hr| exact Hnr| ..].
* rewrite Ht. apply (ai_tq _ _ _ _ AI1).
* rewrite Hg. apply (ai_gq _ _ _ _ AI1).
* apply zlen_nonneg.
* rewrite (allptrs_only_cls _ _ kBatchClass s1 s2 Ho'). apply Permutation_refl.
* reflexivity.
* intros c' Hc'. rewrite (tot_only_cls _ _ (zlen bs) kBatchClass s1 s2 Ho'). unfold tot. rewrite zlen_cons.
destruct (c' =? kBatchClass); lia.
+ intros g2 s2 K AI2. pose proof (gkeep_GS _ _ _ _ G1 K) as [G2 S2].
eapply teva_mono; [apply (IH g2 s2 AI2 F G2); rewrite S2, S1; exact HB|].
intros g3 s3 [G3 S3]. split; [exact G3| rewrite S3, S2; exact S1].
Qed.

Lemma recycle_teva X g s :
ainvx X [] 0 s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (recycle L s).
Proof.
intros AI G HB. destruct (recycle_shape L X s AI) as (g2 & tmp & -> & AI1 & F0 & _).
eapply teva_mono; [apply (do_recycle_teva X tmp g (set_gq g2 s) AI1 F0); [apply (GS_frame s); [reflexivity| reflexivity| exact G]| exact HB]|].
intros g' s' [G' S']. split; [exact G'| exact S'].
Qed.

Lemma drain_teva X g s :
ainvx X [] 0 s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (drain L s).
Proof.
intros AI G HB. unfold drain. cbn [q_bytes].
pose proof (transfer_inv X 0 s AI) as AI1. rewrite transfer_eq in AI1.
set (s1 := set_gq _ (set_tq q0 s)) in *.
assert (G1 : GS s1 g) by (apply (GS_frame s); [reflexivity| reflexivity| exact G]).
destruct (Z.ltb_spec kQMaxSize (q_bytes (as_gq s) + q_bytes (as_tq s))) as [Hgt|Hle].
- eapply teva_mono; [apply (recycle_teva X g s1 AI1 G1 HB)|]. intros g' s' [G' S']. split; [exact G'| exact S'].
- apply teva_ret. split; [exact G1| reflexivity].
Qed.

Lemma new_batch_teva X p B g s :
ainvx X [p] B s -> sec24_room s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (new_batch L s p (aptr_used p)).
Proof.
intros AI Hroom G HB. unfold new_batch.
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI _ H24) as Hcons. pose proof (ai_cls _ _ _ _ AI kBatchClass) as W.
pose proof (cw_cnt _ _ W) as Wcnt. pose proof (cw_nf _ _ W) as Wnf. pose proof (ai_B _ _ _ _ AI) as HB0.
pose proof (tot_nonneg X [p] B s kBatchClass HB0) as Htot.
assert (Hm1 : 0 <= class_size kBatchClass * c_count (cls s kBatchClass)) by (apply Z.mul_nonneg_nonneg; lia).
assert (Hm2 : 0 <= class_size kBatchClass * tot X [p] B s kBatchClass) by (apply Z.mul_nonneg_nonneg; lia).
unfold acc in Hcons.
apply (teva_bind_simple aok (fun g' r => gkeep s g (snd r) g')).
{ apply (cache_alloc_teva aok LOK g s kBatchClass H24 (GS_gpre _ _ _ _ _ AI G)); [lia| exact Hroom| exact HB]. }
intros g1 [ok s1] K. cbn [snd] in K. pose proof (gkeep_GS _ _ _ _ G K) as [G1 S1].
destruct ok; cbn [negb]; [|apply teva_spin].
apply teva_ret. split; [|exact S1]. apply (GS_frame s1); [reflexivity| reflexivity| exact G1].
Qed.

Lemma enqueue_teva X p B g s :
ainvx X [p] B s -> sec24_room s -> GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (Q s) g (enqueue L s p).
Proof.
intros AI Hroom G HB. unfold enqueue.
destruct (split_last (q_list (as_tq s))) as [[front b]|]; [|apply (new_batch_teva X p B); assumption].
destruct (b_count b =? kBatchCount); [apply (new_batch_teva X p B); assumption|].
apply teva_ret. split; [|reflexivity]. apply (GS_frame s); [reflexivity| reflexivity| exact G].
Qed.

Theorem asan_free_teva X X' p g s :
ainv X s -> Permutation X (p :: X') ->
class_size kBatchClass * (tot X [] 0 s kBatchClass + 17) <= kFreeArrayOffset ->
GS s g -> CAPS + as_spent s <= BUDGET ->
teva aok (fun g' s' => GS s' g' /\ as_spent s' = as_spent s) g (asan_free L s p).
Proof.
intros [AI [QT QG]] HP Hroom G HB. unfold asan_free.
assert (AI0 : ainvx X' [p] 0 s).
{ eapply ainvx_perm; [|exact AI]. rewrite app_nil_r. etransitivity; [exact HP|]. apply Permutation_cons_append. }
assert (Hroom' : sec24_room s).
{ unfold sec24_room. intros H0 H8.
pose proof kBatchClass_range as H24. pose proof (class_facts _ H24) as (Hsz & _ & _).
pose proof (ai_cons _ _ _ _ AI _ H24) as Hcons. unfold acc in Hcons. rewrite H0 in Hcons.
pose proof (tot_nonneg X [] 0 s kBatchClass ltac:(lia)).
assert (0 <= class_size kBatchClass * tot X [] 0 s kBatchClass) by (apply Z.mul_nonneg_nonneg; lia).
nia. }
eapply (teva_bind aok (Q s) (fun s1 => ainvx X' [] 0 s1 /\ as_gq s1 = as_gq s)).
{ destruct (Z.ltb_spec kQMaxSize (aptr_used p)).
- apply (recycle_chunk_teva X' p [] 0 g s AI0 G HB).
- apply (enqueue_teva X' p 0 g s AI0 Hroom' G HB). }
{ destruct (Z.ltb_spec kQMaxSize (aptr_used p)).
- eapply tall_mono; [apply (recycle_chunk_inv L aok X' p [] 0 s AI0)|].
intros [s1| |w]; cbn; auto. intros [AI1 [T1 G1]]. auto.
- eapply tall_mono; [apply (enqueue_inv L aok X' p 0 s AI0 Hroom')|].
intros [s1| |w]; cbn; auto. intros (AI1 & G1 & _). auto. }
intros g1 s1 [G1 S1] [AI1 Gq1].
destruct (Z.ltb_spec kQMaxCache (q_bytes (as_tq s1))) as [Hgt|Hle].
- eapply teva_mono; [apply (drain_teva X' g1 s1 AI1 G1); rewrite S1; exact HB|].
intros g2 s2 [G2 S2]. split; [exact G2| rewrite S2; exact S1].
- apply teva_ret. split; [exact G1| exact S1].
Qed.
End Ops.

Lemma aok_anon s0 len avoid b : QQwg.aok s0 (EvMapAnon len avoid) (AOk b) -> b mod kPage = 0 /\ 0 < b.
Proof. cbn. tauto. Qed.

Lemma GS_init : GS astate0 (mkG [] 0).
Proof.
split; [split; [apply Permutation_refl|]| constructor].
unfold SP, csum. cbn -[zsum map zseqn Z.mul Z.add Z.div].
rewrite (zsum_map_const _ 0 (zseqn 1 31)) at 1 || idtac.
assert (E : zsum (map (fun c => c_mapped_user (cls astate0 c) + c_mapped_fa (cls astate0 c)) (zseqn 1 31)) = 0).
{ etransitivity; [apply (f_equal zsum); apply map_ext; intros c; rewrite cls_astate0; reflexivity|].
rewrite <- (map_ext _ _ (fun _ => eq_refl)) || idtac. pose proof (zsum_map_const (fun _ : Z => 0) 0 (zseqn 1 31)) as H || idtac.
induction (zseqn 1 31) as [|x l IH]; [reflexivity|]. cbn [map]. rewrite zsum_cons, IH. reflexivity. }
rewrite E. reflexivity.
Qed.

End WithLayout.
