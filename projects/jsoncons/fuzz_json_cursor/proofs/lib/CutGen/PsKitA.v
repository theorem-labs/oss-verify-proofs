(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib Require Import PropExec AxSymExec3 AxSymExec3B AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound LibSym SegRun SegPlan SegPlanAuto.
From OSSVerify.Proofs.jsoncons.fuzz_json_cursor.lib.CutCert Require Import CutCert CutOps.
Import ListNotations. Import AX2. Import AX2B. Import AX2S.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope Z_scope.

Module PPVA.
Section S.
Variable segs : list Segment.
Definition form_range_c (kn : list kentry) (c : Z) (ts : list (Z * expr)) (cert : list (nat * Z)) : option (Z * Z) :=
  let '(tsS, (LO, HI)) := CX.comb (sum_facts kn kn) cert [] 0 0 in
  match lin_range (CX.erange2 kn) c (lsub_e ts tsS) with Some (a, b) => Some (a + LO, b + HI) | None => None end.
Lemma form_range_c_sound : forall E (M : word -> option byte) kn c ts cert A B, know_ok segs E M kn -> form_range_c kn c ts cert = Some (A, B) -> A <= c + tden E ts <= B.
Proof.
  intros E M kn c ts cert A B Hkn H. unfold form_range_c in H.
  destruct (CX.comb (sum_facts kn kn) cert [] 0 0) as [tsS [LO HI]] eqn:Hc.
  pose proof (CX.comb_sound E _ (sum_facts_sound segs E M kn kn Hkn Hkn) cert [] 0 0 tsS LO HI ltac:(cbn [tden]; lia) Hc) as Hb.
  destruct (lin_range (CX.erange2 kn) c (lsub_e ts tsS)) as [[a b]|] eqn:Hlr; [|discriminate]. injection H as <- <-.
  pose proof (lin_range_sound E (CX.erange2 kn) (fun x l h Hx => CX.erange2_sound segs E M kn x l h Hkn Hx) _ _ _ _ Hlr) as Hr.
  rewrite lsub_e_sound in Hr. lia.
Qed.

Definition certs (n : nat) : list (list (nat * Z)) :=
  let idx := seq 0 n in
  flat_map (fun i => [[(i, 1)]; [(i, -1)]]) idx
  ++ flat_map (fun i => flat_map (fun j => if Nat.ltb i j then [[(i, 1); (j, 1)]; [(i, 1); (j, -1)]; [(i, -1); (j, 1)]; [(i, -1); (j, -1)]] else []) idx) idx.
Definition range_c (kn : list kentry) (c : Z) (ts : list (Z * expr)) : option (Z * Z) :=
  fold_right (fun cert acc => CX.meet (form_range_c kn c ts cert) acc) (CX.form_range kn c ts) (certs (length (sum_facts kn kn))).
Lemma range_c_sound : forall E (M : word -> option byte) kn c ts A B, know_ok segs E M kn -> range_c kn c ts = Some (A, B) -> A <= c + tden E ts <= B.
Proof.
  intros E M kn c ts A B Hkn. unfold range_c. generalize (certs (length (sum_facts kn kn))). intros l. revert A B.
  induction l as [|cert r IH]; intros A B H; cbn [fold_right] in H.
  - exact (CX.form_range_sound segs E M kn c ts A B Hkn H).
  - revert H. apply CX.meet_sound; [intros a b Ha; exact (form_range_c_sound E M kn c ts cert a b Hkn Ha) | intros a b Ha; exact (IH a b Ha)].
Qed.
Definition provec (kn : list kentry) (K : kentry) : bool :=
  match K with
  | KRange e lo hi => match range_c kn (fst (lin_of e)) (snd (lin_of e)) with
                      | Some (A, B) => (Z.leb 0 A && Z.ltb B two64 && Z.leb lo A && Z.leb B hi)%bool
                      | None => false end
  | _ => false
  end.
Lemma provec_sound : forall E (M : word -> option byte) kn K, know_ok segs E M kn -> provec kn K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K Hkn H. destruct K as [| | | | |e lo hi| | | |]; try discriminate. cbn [provec] in H.
  destruct (range_c kn (fst (lin_of e)) (snd (lin_of e))) as [[A B]|] eqn:Hr; [|discriminate].
  apply andb_prop in H as [H H4]. apply andb_prop in H as [H H3]. apply andb_prop in H as [H1 H2]. apply Z.leb_le in H1, H3, H4. apply Z.ltb_lt in H2. unfold two64 in H2.
  pose proof (range_c_sound E M kn _ _ A B Hkn Hr) as HL.
  pose proof (lin_of_sound E e) as [q Hq]. unfold lden, uE in Hq. pose proof (u64_range (edenot E e)) as Hu. unfold two64 in Hu.
  assert (q = 0) by nia. subst q. cbn [kentry_ok]. lia.
Qed.

Definition prove2 (kn : list kentry) (K : kentry) : bool := if APC.fact_ok kn K then true else if CX.fact2_ok kn K then true else provec kn K.
Lemma prove2_sound : forall E (M : word -> option byte) kn K, know_ok segs E M kn -> prove2 kn K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K Hkn H. unfold prove2 in H. destruct (APC.fact_ok kn K) eqn:H1; [exact (APS.fact_ok_sound segs E M kn K Hkn H1)|].
  destruct (CX.fact2_ok kn K) eqn:H2; [exact (CX.fact2_ok_sound segs E M kn K Hkn H2) | exact (provec_sound E M kn K Hkn H)].
Qed.

Definition zfact (kn : list kentry) (K : kentry) : list kentry :=
  match K with
  | KRange (EMd M_MUL (ELit (-1)) X) 0 hi => if (Z.ltb hi 9223372036854775808 && prove2 kn (KRange X 0 4611686018427387904))%bool then [KRange X 0 0] else []
  | _ => []
  end.
Definition zfacts (kn : list kentry) : list kentry := flat_map (zfact kn) kn.
Lemma zfacts_sound : forall E (M : word -> option byte) kn, know_ok segs E M kn -> know_ok segs E M (zfacts kn).
Proof.
  intros E M kn Hkn. unfold know_ok, zfacts. apply Forall_forall. intros Y HY. apply in_flat_map in HY as (K & HK & HY).
  pose proof (proj1 (Forall_forall _ _) Hkn K HK) as HKok.
  destruct K as [| | | | |e lo hi| | | |]; try destruct HY. cbn [zfact] in HY.
  destruct e as [| | | |m a X| | |]; try destruct HY. destruct m; try destruct HY. destruct a as [z| | | | | | |]; try destruct HY.
  destruct z as [|p|p]; try destruct HY. destruct p; try destruct HY. destruct lo; try destruct HY.
  destruct (Z.ltb hi 9223372036854775808 && prove2 kn (KRange X 0 4611686018427387904))%bool eqn:Hb; [|destruct HY].
  destruct HY as [<-|[]]. apply andb_prop in Hb as [H1 H2]. apply Z.ltb_lt in H1.
  pose proof (prove2_sound E M kn _ Hkn H2) as HX. cbn [kentry_ok] in HX, HKok |- *. cbn [edenot] in HKok.
  rewrite u_mul64 in HKok. cbn [edenot] in HKok. rewrite u_lit64 in HKok. unfold two64 in HKok. rewrite Zmult_mod_idemp_l in HKok.
  set (x := bv_unsigned (edenot E X)) in *.
  destruct (Z.eq_dec x 0) as [->|Hn]; [lia|]. exfalso.
  assert (Hm : (-1 * x) mod 2 ^ 64 = 2 ^ 64 - x) by (symmetry; apply (Z.mod_unique (-1 * x) (2 ^ 64) (-1)); lia). lia.
Qed.

Definition lfact (kn : list kentry) (K : kentry) : list kentry :=
  match K with
  | KRange (EAlu ALU_SLTU x y) 1 1 => match CX.ltu_fact kn x y true with Some F => [F] | None => [] end
  | KRange (EAlu ALU_SLTU x y) 0 0 => match CX.ltu_fact kn y x false with Some F => [F] | None => [] end
  | _ => []
  end.
Definition lfacts (kn : list kentry) : list kentry := flat_map (lfact kn) kn.
Lemma lfacts_sound : forall E (M : word -> option byte) kn, know_ok segs E M kn -> know_ok segs E M (lfacts kn).
Proof.
  intros E M kn Hkn. unfold know_ok, lfacts. apply Forall_forall. intros Y HY. apply in_flat_map in HY as (K & HK & HY).
  destruct K as [| | | | |e lo hi| | | |]; try destruct HY. cbn [lfact] in HY.
  destruct e as [| |op x y| | | | |]; try destruct HY. destruct op; try destruct HY.
  destruct lo as [|p|p]; try destruct HY.
  - destruct hi; try destruct HY. destruct (CX.ltu_fact kn y x false) as [F|] eqn:HF; [|destruct HY]. destruct HY as [<-|[]]. exact (CX.ltu_fact_sound segs E M kn y x false F Hkn HF).
  - destruct p; try destruct HY. destruct hi as [|q|q]; try destruct HY. destruct q; try destruct HY.
    destruct (CX.ltu_fact kn x y true) as [F|] eqn:HF; [|destruct HY]. destruct HY as [<-|[]]. exact (CX.ltu_fact_sound segs E M kn x y true F Hkn HF).
Qed.
Definition ext (kn : list kentry) : list kentry := let k1 := lfacts kn ++ kn in zfacts k1 ++ k1.
Lemma ext_sound : forall E (M : word -> option byte) kn, know_ok segs E M kn -> know_ok segs E M (ext kn).
Proof.
  intros E M kn Hkn. unfold ext. assert (H1 : know_ok segs E M (lfacts kn ++ kn)) by (unfold know_ok in *; apply Forall_app; split; [exact (lfacts_sound E M kn Hkn) | exact Hkn]).
  unfold know_ok in *. apply Forall_app. split; [exact (zfacts_sound E M _ H1) | exact H1].
Qed.
Definition prove3 (kn : list kentry) (K : kentry) : bool := if prove2 kn K then true else prove2 (ext kn) K.
Lemma prove3_sound : forall E (M : word -> option byte) kn K, know_ok segs E M kn -> prove3 kn K = true -> kentry_ok segs E M K.
Proof.
  intros E M kn K Hkn H. unfold prove3 in H. destruct (prove2 kn K) eqn:H1; [exact (prove2_sound E M kn K Hkn H1)|].
  exact (prove2_sound E M (ext kn) K (ext_sound E M kn Hkn) H).
Qed.
End S.
End PPVA.
