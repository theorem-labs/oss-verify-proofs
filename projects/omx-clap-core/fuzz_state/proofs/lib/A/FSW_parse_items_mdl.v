(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* fs program part, READER lane: the pure MODEL lemmas of parse_items' member loop (A 0x84a04), for the walk
   lib/A/FSW_parse_items.v and its composition lane. No machine state, no engine, no callee spec: every lemma here is
   about the released models (lib/Spec PjTree / PjGrammar / PjRoundTrip, lib/Prog WriterValue / WriterSpec /
   ReaderRes), lib/A/FSH_Gen.v's plain_byte / quiet / HEAD, lib/A/FSH_Fn_reader.v's accounting functions (rd_ev,
   rd_live, rd_sizes_ok, rd_sum, rd_heads, rd_hblocks, grow_tr, plain_run, run_at; all outside its Section c),
   lib/A/Prog/FSDocStrs.v's document predicates and lib/A/FSW_parse_items.v's pi_mgo. rule 24: no function proved.

   THE FOUR GROUPS (names and statement shapes fixed by the composition lane's interface):
     (T1) the trace of an object, member by member: pim_ttrace_obj, pim_tgo_app, pim_tgo_cons, pim_capf (the cap after
          a prefix of members), pim_capf_app, pim_gcap_inv, pim_capf_inv, pim_gcap_lt, pim_grow_tr (grow_spec's event
          list IS the model's grow_ev), pim_cap2, pim_held_grow, pim_grow_size (the bound grow_spec and pj_slots_at
          need, from the trace's own sizes: MALLOC_MAX = 2 ^ 28, Reusable/YG00.v:39).
     (T2) additivity and bounds of the accounting functions: pim_rd_ev_app / _nn, pim_rd_live_app / _nn,
          pim_sizes_app, pim_held_live, pim_D_live, pim_rd_sum_app, pim_rd_heads_app, pim_rd_hblocks_app,
          pim_quiet_split, pim_rd_ev_alloc.
     (T3) the text at in->p: pim_rest_skip, pim_rest_byte, pim_mgo_cons, pim_spieces_plain, pim_ech_plain, pim_wsep,
          pim_wsep_ws, pim_key_run (a plain key at in->p is parse_string's plain_run, and run_at reads it back).
     (T4) the document predicates of one member: pim_vals_cons, pim_strs_cons, pim_wf_cons, pim_depth_cons.
   Every statement is the interface's as given; none needed an extra premise.
   pim_wf_cons's tail half rebuilds pj_wf of the remaining object through wf_read on its own writer text: pj_wf has no
   tail constructor, so the proof goes wf_good -> good / depth of the tail -> PjRoundTrip.rt_value (the same route as
   PjRoundTrip.jr_value_wdoc).
   COPIED: nothing. The small list facts (the pimh_ lemmas) are proved here so that the file does not depend on Stdlib
   lemma names that moved between releases; no lemma of another walk family's lib/A file (the AF, AE, AD and ZZ files)
   is loaded (the implicit-instance guard of FSH_Gen.v:29).
   CLOSURE (Print Assumptions over the 35 interface lemmas, which use every pimh_ lemma; throwaway, log
   build-20261029T092351Z on a build machine): every one is Closed under the global context. *)
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Reusable Require Import
YK11 YK0s YK15 YK18 YP09 YK04 YA0i YA0n YG00 YG0a YG01 YG0f YG0v YG0n YG0d YCbq YI00 YI04 YI16 YK06 YM05.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Gen.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Spec Require PjTree PjGrammar PjRoundTrip.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.Prog Require WriterSpec WriterValue ReaderRes.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require Import FSH_Fn_reader.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A.Prog Require FSDocStrs.
From OSSVerify.Proofs.omx_clap_core.fuzz_state.lib.A Require FSW_parse_items.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Open Scope Z_scope.
(* SINK GUARD (a Theorem Labs lane 02:29Z): a SUCCESS here (the build errors naming this line) means a WRONG sink instance resolved. *)
Fail Definition probe_SK : Reusable.YI16.sink_head := _.
Fail Definition probe_SH : Reusable.YI14.sink_syms := _.

(* ================= small list facts ================= *)
Lemma pimh_skipn_skipn : forall (A : Type) (b a : nat) (l : list A), skipn a (skipn b l) = skipn (a + b) l.
Proof.
intros A b. induction b as [|b IH]; intros a l.
- rewrite Nat.add_0_r. reflexivity.
- rewrite Nat.add_succ_r. destruct l as [|x l].
  + destruct a; reflexivity.
  + cbn [skipn]. exact (IH a l).
Qed.
Lemma pimh_skipn_map : forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
  skipn n (map f l) = map f (skipn n l).
Proof.
intros A B f n. induction n as [|n IH]; intros [|x l]; cbn [skipn map]; try reflexivity. exact (IH l).
Qed.
Lemma pimh_firstn_map : forall (A B : Type) (f : A -> B) (n : nat) (l : list A),
  firstn n (map f l) = map f (firstn n l).
Proof.
intros A B f n. induction n as [|n IH]; intros [|x l]; cbn [firstn map]; try reflexivity. rewrite IH. reflexivity.
Qed.
Lemma pimh_skipn_app : forall (A : Type) (X r : list A), skipn (length X) (X ++ r) = r.
Proof. intros A X r. induction X as [|x X IH]; [reflexivity|exact IH]. Qed.
Lemma pimh_firstn_app : forall (A : Type) (X r : list A), firstn (length X) (X ++ r) = X.
Proof. intros A X r. induction X as [|x X IH]; [reflexivity|]. cbn [length app firstn]. rewrite IH. reflexivity. Qed.
Lemma pimh_nth_skipn : forall (A : Type) (k : nat) (l : list A) (j : nat),
  nth_error (skipn k l) j = nth_error l (k + j).
Proof.
intros A k. induction k as [|k IH]; intros l j; [reflexivity|].
destruct l as [|x l]; cbn [skipn].
- destruct j; reflexivity.
- exact (IH l j).
Qed.
Lemma pimh_z2n_c : forall (c : Z) (x : nat), 0 <= c -> Z.to_nat (c * Z.of_nat x) = (Z.to_nat c * x)%nat.
Proof. intros c x Hc. rewrite Z2Nat.inj_mul by lia. rewrite Nat2Z.id. reflexivity. Qed.

(* ================= (T1) the trace of an object, member by member ================= *)
(* the cap after the members l, from index n and cap cap: the cap argument tgo_obj passes on *)
Fixpoint pim_capf (n cap : nat) (l : list (list Z * PjTree.jv)) : nat :=
  match l with [] => cap | _ :: r => pim_capf (S n) (PjRoundTrip.gcap n cap) r end.

Lemma pim_ttrace_obj : forall ms, PjRoundTrip.ttrace (PjTree.JObj ms) = PjRoundTrip.tgo_obj 0 0 ms.
Proof. exact PjRoundTrip.tt_obj. Qed.

Lemma pim_tgo_app : forall l1 l2 n cap, PjRoundTrip.tgo_obj n cap (l1 ++ l2) =
  PjRoundTrip.tgo_obj n cap l1 ++ PjRoundTrip.tgo_obj (n + length l1) (pim_capf n cap l1) l2.
Proof.
induction l1 as [|[kk u] r IH]; intros l2 n cap.
- cbn [app length PjRoundTrip.tgo_obj pim_capf]. rewrite Nat.add_0_r. reflexivity.
- cbn [app length PjRoundTrip.tgo_obj pim_capf]. rewrite IH, Nat.add_succ_r.
  rewrite <- !app_assoc. cbn [app]. rewrite <- !app_assoc. reflexivity.
Qed.

Lemma pim_tgo_cons : forall kk u r n cap, PjRoundTrip.tgo_obj n cap ((kk, u) :: r) =
  PjRoundTrip.grow_ev true n cap ++ PjGrammar.EAlloc (S (length (flat_map PjRoundTrip.ech kk)))
  :: PjRoundTrip.ttrace u ++ PjRoundTrip.tgo_obj (S n) (PjRoundTrip.gcap n cap) r.
Proof. intros kk u r n cap. reflexivity. Qed.

Lemma pim_capf_app : forall l1 l2 n cap, pim_capf n cap (l1 ++ l2) = pim_capf (n + length l1) (pim_capf n cap l1) l2.
Proof.
induction l1 as [|m r IH]; intros l2 n cap.
- cbn [app length pim_capf]. rewrite Nat.add_0_r. reflexivity.
- cbn [app length pim_capf]. rewrite IH, Nat.add_succ_r. reflexivity.
Qed.

Lemma pim_gcap_inv : forall n cap, (n <= cap)%nat -> (S n <= PjRoundTrip.gcap n cap)%nat.
Proof.
intros n cap H. unfold PjRoundTrip.gcap. destruct (Nat.ltb n cap) eqn:E; cbv beta iota.
- apply Nat.ltb_lt in E. lia.
- apply Nat.ltb_ge in E. destruct (Nat.eqb cap 0) eqn:E0; cbv beta iota.
  + apply Nat.eqb_eq in E0. lia.
  + apply Nat.eqb_neq in E0. lia.
Qed.

Lemma pim_capf_inv : forall l n cap, (n <= cap)%nat -> (n + length l <= pim_capf n cap l)%nat.
Proof.
induction l as [|m r IH]; intros n cap H; cbn [pim_capf length].
- lia.
- specialize (IH (S n) (PjRoundTrip.gcap n cap) (pim_gcap_inv n cap H)). lia.
Qed.

Lemma pim_gcap_lt : forall n cap, (n < cap)%nat -> PjRoundTrip.gcap n cap = cap.
Proof. intros n cap H. unfold PjRoundTrip.gcap. rewrite (proj2 (Nat.ltb_lt n cap) H). reflexivity. Qed.

Lemma pim_cap2 : forall n cap, (n <= cap)%nat -> ~ (n < cap)%nat ->
  ReaderRes.cap2 (Z.of_nat cap) = Z.of_nat (PjRoundTrip.gcap n cap).
Proof.
intros n cap H1 H2. assert (En : n = cap) by lia. subst n.
unfold ReaderRes.cap2, PjRoundTrip.gcap. rewrite (proj2 (Nat.ltb_ge cap cap) (Nat.le_refl cap)).
destruct cap as [|c].
- reflexivity.
- rewrite (proj2 (Z.eqb_neq (Z.of_nat (S c)) 0)) by lia. cbn [Nat.eqb]. lia.
Qed.

Lemma pim_grow_tr : forall n cap, (n <= cap)%nat ->
  grow_tr 6 (Z.of_nat n) (Z.of_nat cap) = PjRoundTrip.grow_ev true n cap.
Proof.
intros n cap H. unfold grow_tr, PjRoundTrip.grow_ev. destruct (Nat.ltb n cap) eqn:E.
- apply Nat.ltb_lt in E. rewrite (proj2 (Z.eqb_neq (Z.of_nat n) (Z.of_nat cap))) by lia. reflexivity.
- apply Nat.ltb_ge in E. assert (En : n = cap) by lia. subst n.
  rewrite (pim_cap2 cap cap (Nat.le_refl cap) (Nat.lt_irrefl cap)).
  rewrite !Z.eqb_refl. rewrite !pimh_z2n_c by lia. reflexivity.
Qed.

Lemma pim_held_grow : forall n cap, (n <= cap)%nat -> PjGrammar.held (PjRoundTrip.grow_ev true n cap) =
  64 * (Z.of_nat (PjRoundTrip.gcap n cap) - Z.of_nat cap).
Proof.
intros n cap H. unfold PjRoundTrip.grow_ev. destruct (Nat.ltb n cap) eqn:E.
- apply Nat.ltb_lt in E. rewrite (pim_gcap_lt n cap E). cbn [PjGrammar.held]. lia.
- cbn [PjGrammar.held PjGrammar.held_ev]. lia.
Qed.

Lemma pim_grow_size : forall n cap, (n <= cap)%nat -> ~ (n < cap)%nat -> rd_sizes_ok (PjRoundTrip.grow_ev true n cap) ->
  56 * Z.of_nat (PjRoundTrip.gcap n cap) + HEAD < MALLOC_MAX /\ Z.of_nat (PjRoundTrip.gcap n cap) <= 2 ^ 54.
Proof.
intros n cap H1 H2 Hs. unfold rd_sizes_ok, PjRoundTrip.grow_ev in Hs.
rewrite (proj2 (Nat.ltb_ge n cap)) in Hs by lia. cbv beta iota in Hs.
apply Forall_cons_iff in Hs as [Hs _]. cbn [PjGrammar.esize] in Hs.
unfold HEAD, MALLOC_MAX in *. split; lia.
Qed.

(* ================= (T2) additivity and bounds of the accounting functions ================= *)
Lemma pim_rd_ev_app : forall a b, rd_ev (a ++ b) = rd_ev a + rd_ev b.
Proof.
intros a b. induction a as [|e a IH]; [reflexivity|].
cbn [app]. unfold rd_ev in *. cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma pim_rd_live_app : forall a b, rd_live (a ++ b) = rd_live a + rd_live b.
Proof.
intros a b. induction a as [|e a IH]; [reflexivity|].
cbn [app]. unfold rd_live in *. cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma pim_rd_ev_nn : forall a, 0 <= rd_ev a.
Proof.
induction a as [|e a IH]; [unfold rd_ev; cbn [fold_right]; lia|].
unfold rd_ev in *. cbn [fold_right].
destruct e as [n|m n|n|n]; cbv beta iota; [|destruct (Nat.eqb m 0); cbv beta iota| |];
  unfold EV_fuzz_malloc, EV_fuzz_realloc, EV_fuzz_free in *; lia.
Qed.

Lemma pim_rd_live_nn : forall a, 0 <= rd_live a.
Proof.
induction a as [|e a IH]; [unfold rd_live; cbn [fold_right]; lia|].
unfold rd_live in *. cbn [fold_right]. unfold HEAD in *. lia.
Qed.

Lemma pim_sizes_app : forall a b, rd_sizes_ok (a ++ b) <-> rd_sizes_ok a /\ rd_sizes_ok b.
Proof. intros a b. unfold rd_sizes_ok. apply Forall_app. Qed.

Lemma pim_held_live : forall tr, PjGrammar.held tr + HEAD * Z.of_nat (length tr) <= rd_live tr.
Proof.
induction tr as [|e tr IH].
- unfold rd_live, HEAD. cbn [PjGrammar.held length fold_right]. lia.
- cbn [PjGrammar.held length]. unfold rd_live in *. cbn [fold_right]. unfold HEAD in *.
  destruct e as [n|m n|n|n]; cbn [PjGrammar.held_ev PjGrammar.esize]; lia.
Qed.

Lemma pim_D_live : forall (D : list (Z * Z)) tr, rd_sum D = PjGrammar.held tr -> (length D <= length tr)%nat ->
  rd_sum D + HEAD * Z.of_nat (length D) <= rd_live tr.
Proof. intros D tr H1 H2. pose proof (pim_held_live tr) as H. unfold HEAD in *. lia. Qed.

Lemma pim_rd_sum_app : forall a b, rd_sum (a ++ b) = rd_sum a + rd_sum b.
Proof.
intros a b. induction a as [|x a IH]; [reflexivity|].
cbn [app]. unfold rd_sum in *. cbn [fold_right]. rewrite IH. lia.
Qed.

Lemma pim_rd_heads_app : forall a b, rd_heads (a ++ b) = rd_heads a ++ rd_heads b.
Proof. intros a b. unfold rd_heads. apply map_app. Qed.

Lemma pim_rd_hblocks_app : forall a b, rd_hblocks (a ++ b) = rd_hblocks a ++ rd_hblocks b.
Proof. intros a b. unfold rd_hblocks. apply map_app. Qed.

Lemma pim_quiet_split : forall cnt fail a b, 0 <= a -> 0 <= b -> quiet cnt fail (a + b) ->
  quiet cnt fail a /\ quiet (cnt + a) fail b.
Proof.
intros cnt fail a b Ha Hb H. unfold quiet in *. destruct H as (H1 & H2 & H3).
split; (split; [exact H1 | split; lia]).
Qed.

Lemma pim_rd_ev_alloc : forall n, rd_ev [PjGrammar.EAlloc n] = EV_fuzz_malloc.
Proof. intros n. reflexivity. Qed.

(* ================= (T3) the text at in->p ================= *)
(* the bytes left m bytes further on are the bytes left, less their first m *)
Lemma pimh_rest_add : forall tb text p (m : nat), text <= p ->
  ReaderRes.rest_at tb text (p + Z.of_nat m) = skipn m (ReaderRes.rest_at tb text p).
Proof.
intros tb text p m H. unfold ReaderRes.rest_at, ReaderRes.zb.
rewrite pimh_skipn_map, pimh_skipn_skipn.
replace (Z.to_nat (p + Z.of_nat m - text)) with (m + Z.to_nat (p - text))%nat by lia.
reflexivity.
Qed.

(* byte j of the bytes left is the text byte at p + j *)
Lemma pimh_rest_nth : forall tb text p j c, text <= p -> nth_error (ReaderRes.rest_at tb text p) j = Some c ->
  exists b : byte, nth_error tb (Z.to_nat (p + Z.of_nat j - text)) = Some b /\ bv_unsigned b = c.
Proof.
intros tb text p j c Hp E. unfold ReaderRes.rest_at, ReaderRes.zb in E.
rewrite nth_error_map, pimh_nth_skipn in E.
destruct (nth_error tb (Z.to_nat (p - text) + j)) as [b|] eqn:Eb; [|discriminate E].
cbn [option_map] in E. injection E as <-. exists b. split; [|reflexivity].
replace (Z.to_nat (p + Z.of_nat j - text)) with (Z.to_nat (p - text) + j)%nat by lia. exact Eb.
Qed.

Lemma pim_rest_skip : forall tb text p X rest, text <= p -> ReaderRes.rest_at tb text p = X ++ rest ->
  ReaderRes.rest_at tb text (p + Z.of_nat (length X)) = rest.
Proof.
intros tb text p X rest H E. rewrite (pimh_rest_add tb text p (length X) H), E. apply pimh_skipn_app.
Qed.

Lemma pim_rest_byte : forall tb text p b rest, text <= p -> ReaderRes.rest_at tb text p = b :: rest ->
  nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 b) /\ 0 <= b < 256.
Proof.
intros tb text p b rest H E.
assert (E0 : nth_error (ReaderRes.rest_at tb text p) 0 = Some b) by (rewrite E; reflexivity).
destruct (pimh_rest_nth tb text p 0 b H E0) as (c & Ec & <-).
replace (p + Z.of_nat 0 - text) with (p - text) in Ec by lia.
rewrite Ec, Z_to_bv_bv_unsigned. split; [reflexivity|apply YK11.u8_range].
Qed.

Lemma pim_mgo_cons : forall pr dd i kk x r, concat (FSW_parse_items.pi_mgo pr dd i ((kk, x) :: r)) =
  (if Nat.eqb i 0 then [] else [44]) ++ concat (WriterValue.wind pr (dd + 1)) ++
  concat (WriterSpec.spieces kk) ++ WriterValue.wsep pr ++
  concat (WriterValue.wvpieces x pr (dd + 1)) ++ concat (FSW_parse_items.pi_mgo pr dd (S i) r).
Proof.
intros pr dd i kk x r. cbn [FSW_parse_items.pi_mgo]. unfold WriterValue.wcomma.
rewrite !concat_app, (FSW_parse_items.pi_concat_single (WriterValue.wsep pr)).
destruct (Nat.eqb i 0); reflexivity.
Qed.

Lemma pim_ech_plain : forall kk, plain_bytes kk -> flat_map PjRoundTrip.ech kk = kk.
Proof.
induction kk as [|c kk IH]; intros H; [reflexivity|].
unfold plain_bytes in H. apply Forall_cons_iff in H as [(H32 & H34 & H92) H].
cbn [flat_map]. rewrite (IH H). unfold PjRoundTrip.ech, WriterSpec.special.
rewrite (proj2 (Z.eqb_neq c 34) H34), (proj2 (Z.eqb_neq c 92) H92), (proj2 (Z.ltb_ge c 32) H32).
reflexivity.
Qed.

Lemma pim_spieces_plain : forall kk, plain_bytes kk -> concat (WriterSpec.spieces kk) = 34 :: kk ++ [34].
Proof. intros kk H. rewrite PjRoundTrip.wstr_eq, (pim_ech_plain kk H). reflexivity. Qed.

Lemma pim_wsep : forall pr, WriterValue.wsep pr = 58 :: (if pr then [32] else []).
Proof. intros pr. destruct pr; reflexivity. Qed.

Lemma pim_wsep_ws : forall pr : bool, Forall (fun c => PjGrammar.ws c = true) (if pr then [32] else []).
Proof. intros pr. destruct pr; cbv beta iota; [constructor; [exact (eq_refl true)|constructor]|constructor]. Qed.

Lemma pim_key_run : forall tb text len p kk rest, text <= p ->
  Z.of_nat (length (ReaderRes.rest_at tb text p)) = text + len - p ->
  ReaderRes.rest_at tb text p = 34 :: kk ++ 34 :: rest -> plain_bytes kk ->
  plain_run tb text len p (Z.of_nat (length kk)) /\ run_at tb text p (Z.of_nat (length kk)) = kk /\
  nth_error tb (Z.to_nat (p - text)) = Some (Z_to_bv 8 34) /\ p < text + len.
Proof.
intros tb text len p kk rest Hp Hlen E Hk.
assert (Hl : Z.of_nat (length (ReaderRes.rest_at tb text p)) = 2 + Z.of_nat (length kk) + Z.of_nat (length rest)).
{ rewrite E. cbn [length]. rewrite length_app. cbn [length]. lia. }
assert (E1 : ReaderRes.rest_at tb text (p + 1) = kk ++ 34 :: rest).
{ replace (p + 1) with (p + Z.of_nat (length [34])) by reflexivity.
  apply (pim_rest_skip tb text p [34] (kk ++ 34 :: rest) Hp). rewrite E. reflexivity. }
assert (E2 : ReaderRes.rest_at tb text (p + 1 + Z.of_nat (length kk)) = 34 :: rest).
{ apply (pim_rest_skip tb text (p + 1) kk (34 :: rest)); [lia|exact E1]. }
destruct (pim_rest_byte tb text p 34 (kk ++ 34 :: rest) Hp E) as [H0 _].
destruct (pim_rest_byte tb text (p + 1 + Z.of_nat (length kk)) 34 rest ltac:(lia) E2) as [HQ _].
assert (Hrun : run_at tb text p (Z.of_nat (length kk)) = kk).
{ pose proof E1 as E1'. unfold ReaderRes.rest_at, ReaderRes.zb in E1'. unfold run_at, ReaderRes.zb.
  rewrite Nat2Z.id, <- pimh_firstn_map, E1'. apply pimh_firstn_app. }
split; [|split; [exact Hrun|split; [exact H0|lia]]].
unfold plain_run. split; [lia|]. split; [lia|]. split; [exact HQ|].
intros i Hi.
destruct (nth_error kk (Z.to_nat i)) as [c|] eqn:Ec.
2: { apply nth_error_None in Ec. lia. }
assert (Ec' : nth_error (ReaderRes.rest_at tb text (p + 1)) (Z.to_nat i) = Some c).
{ rewrite E1, nth_error_app1 by lia. exact Ec. }
destruct (pimh_rest_nth tb text (p + 1) (Z.to_nat i) c ltac:(lia) Ec') as (b & Eb & Ebc).
exists b. split.
- replace (p + 1 + i - text) with (p + 1 + Z.of_nat (Z.to_nat i) - text) by lia. exact Eb.
- rewrite Ebc. unfold plain_bytes in Hk. rewrite Forall_forall in Hk. apply Hk. eapply nth_error_In. exact Ec.
Qed.

(* ================= (T4) the document predicates, member by member ================= *)
Lemma pimh_vals_cons : forall kk x r, FSDocStrs.jv_vals (PjTree.JObj ((kk, x) :: r)) =
  (x :: FSDocStrs.jv_vals x) ++ FSDocStrs.jv_vals (PjTree.JObj r).
Proof. intros kk x r. reflexivity. Qed.

Lemma pimh_strs_cons : forall kk x r, FSDocStrs.jv_strs (PjTree.JObj ((kk, x) :: r)) =
  kk :: FSDocStrs.jv_strs x ++ FSDocStrs.jv_strs (PjTree.JObj r).
Proof. intros kk x r. reflexivity. Qed.

Lemma pimh_depth_obj_cons : forall kk x r,
  PjTree.depth (PjTree.JObj ((kk, x) :: r)) = Nat.max (S (PjTree.depth x)) (PjTree.depth (PjTree.JObj r)).
Proof.
intros kk x r.
change (PjTree.depth (PjTree.JObj ((kk, x) :: r))) with
  (S (Nat.max (PjTree.depth x) (list_max (map (fun '(_, v) => PjTree.depth v) r)))).
change (PjTree.depth (PjTree.JObj r)) with (S (list_max (map (fun '(_, v) => PjTree.depth v) r))).
lia.
Qed.

Lemma pim_vals_cons : forall kk x r, FSDocStrs.fs_doc_values (PjTree.JObj ((kk, x) :: r)) ->
  (forall y, In y (x :: FSDocStrs.jv_vals x) -> FSDocStrs.str_or_obj y) /\
  FSDocStrs.fs_doc_values (PjTree.JObj r).
Proof.
intros kk x r H. unfold FSDocStrs.fs_doc_values in *. rewrite pimh_vals_cons in H. split.
- intros y Hy. apply H. right. apply in_or_app. left. exact Hy.
- intros y [<-|Hy]; [exact I|]. apply H. right. apply in_or_app. right. exact Hy.
Qed.

Lemma pim_strs_cons : forall kk x r, FSDocStrs.fs_doc_strings (PjTree.JObj ((kk, x) :: r)) ->
  plain_bytes kk /\ FSDocStrs.fs_doc_strings x /\ FSDocStrs.fs_doc_strings (PjTree.JObj r).
Proof.
intros kk x r H. unfold FSDocStrs.fs_doc_strings in *. rewrite pimh_strs_cons in H. split; [|split].
- apply H. left. reflexivity.
- intros s Hs. apply H. right. apply in_or_app. left. exact Hs.
- intros s Hs. apply H. right. apply in_or_app. right. exact Hs.
Qed.

Lemma pim_wf_cons : forall kk x r, PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj ((kk, x) :: r)) ->
  PjRoundTrip.pj_wf ReaderRes.jr_strtod x /\ PjRoundTrip.pj_wf ReaderRes.jr_strtod (PjTree.JObj r).
Proof.
intros kk x r H. split.
- exact (PjRoundTrip.wf_member _ _ kk x H (or_introl eq_refl)).
- destruct (PjRoundTrip.wf_good _ _ H) as [Hg Hd].
  apply PjRoundTrip.good_obj in Hg. apply Forall_cons_iff in Hg as [_ Hg].
  apply (proj2 (PjRoundTrip.good_obj _ r)) in Hg.
  rewrite pimh_depth_obj_cons in Hd.
  assert (Hd' : (PjTree.depth (PjTree.JObj r) + 0 <= PjGrammar.MAXD)%nat) by lia.
  assert (Hdoc : WriterValue.wdoc (PjTree.JObj r) false =
                 concat (WriterValue.wvpieces (PjTree.JObj r) false 0) ++ []).
  { unfold WriterValue.wdoc, WriterValue.wdpieces. rewrite concat_app. reflexivity. }
  apply (PjRoundTrip.wf_read _ (WriterValue.wdoc (PjTree.JObj r) false)).
  unfold PjGrammar.json_read, PjGrammar.jr_run, PjGrammar.jr_value. rewrite Hdoc.
  rewrite (PjRoundTrip.rt_value _ (PjTree.JObj r) Hg false 0 0%nat Hd' []
    (S (2 * length (concat (WriterValue.wvpieces (PjTree.JObj r) false 0) ++ []))) I ltac:(lia)).
  reflexivity.
Qed.

Lemma pim_depth_cons : forall kk x r d, (PjTree.depth (PjTree.JObj ((kk, x) :: r)) <= S d)%nat ->
  (PjTree.depth x <= d)%nat /\ (PjTree.depth (PjTree.JObj r) <= S d)%nat.
Proof. intros kk x r d H. rewrite pimh_depth_obj_cons in H. lia. Qed.
