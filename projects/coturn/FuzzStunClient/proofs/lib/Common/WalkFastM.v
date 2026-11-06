(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common Require Import PropExec CatExec SeqExec StepTac StoreOk.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Inductive slay : Type := SLay (a : word) (bs : list byte).

Fixpoint sch_den (m : word -> option byte) (l : list slay) : word -> option byte :=
  match l with
  | [] => m
  | SLay a bs :: tl => wbytes (sch_den m tl) a bs
  end.

Lemma store_ok_sch : forall segs n (m : word -> option byte) (l : list slay) (a : word),
  store_ok segs m a n = true -> store_ok segs (sch_den m l) a n = true.
Proof.
  intros segs n m l a H. induction l as [|[a' bs] tl IH]; cbn [sch_den]; [exact H|].
  eapply store_ok_mono; [apply wbytes_grows | exact IH].
Qed.

(* [comment removed for export] *)
Ltac sch_reify ch :=
  lazymatch ch with
  | wbytes ?m ?a ?bs => let tl := sch_reify m in constr:(SLay a bs :: tl)
  | _ => constr:(@nil slay)
  end.
Ltac sch_base ch :=
  lazymatch ch with
  | wbytes ?m _ _ => sch_base m
  | _ => ch
  end.

Ltac store_ok_peel_fast1 :=
  lazymatch goal with
  | |- store_ok ?segs ?ch ?a ?n = true =>
      lazymatch ch with
      | wbytes (wbytes _ _ _) _ _ =>
          let l := sch_reify ch in
          let m := sch_base ch in
          (* [comment removed for export] *)
          change (store_ok segs (sch_den m l) a n = true);
          apply store_ok_sch
      end
  end.

(* [comment removed for export] *)
Ltac store_ok_peel_fast :=
  try store_ok_peel_fast1;
  repeat first
    [ eapply store_ok_mono; [apply wbytes_grows|]
    | eapply store_ok_mono; [apply write_to_mem_grows|]
    | eapply store_ok_mono; [apply apply_zeros_grows|]
    | eapply store_ok_mono; [apply apply_writes_grows|] ].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Open Scope Z_scope.

(* [comment removed for export] *)
Inductive wlay : Type := WLay (za : Z) (rel : bool) (k : Z) (n : nat) (bs : list byte).

Fixpoint wch_den (m : word -> option byte) (l : list wlay) : word -> option byte :=
  match l with
  | [] => m
  | WLay za _ _ _ bs :: tl => wbytes (wch_den m tl) (Z_to_bv 64 za) bs
  end.

Definition wadr (b : Z) (rel : bool) (k : Z) : Z := if rel then b + k else k.

Fixpoint wch_facts (b : Z) (l : list wlay) : Prop :=
  match l with
  | [] => True
  | WLay za rel k n bs :: tl => (za = wadr b rel k /\ length bs = n) /\ wch_facts b tl
  end.

Definition wf_M64 : Z := 18446744073709551616.

(* [comment removed for export] *)
Definition wmin (lo : Z) (rel : bool) (k : Z) : Z := if rel then lo + k else k.
Definition wmax (hi : Z) (rel : bool) (k : Z) : Z := if rel then hi + k else k.

(* [comment removed for export] *)
Definition wrng (lo hi : Z) (rel : bool) (k n : Z) : bool :=
  (0 <=? wmin lo rel k) && (wmax hi rel k <? wf_M64) && (wmax hi rel k + n <=? wf_M64).

(* [comment removed for export] *)
Definition wdisj (lo hi : Z) (rr : bool) (k n : Z) (rl : bool) (k' n' : Z) : bool :=
  if Bool.eqb rr rl
  then (k + n <=? k') || (k' + n' <=? k)
  else (wmax hi rr k + n <=? wmin lo rl k') || (wmax hi rl k' + n' <=? wmin lo rr k).

Fixpoint wch_chk (lo hi : Z) (l : list wlay) (rr : bool) (k n : Z) : bool :=
  match l with
  | [] => true
  | WLay _ rl k' n' _ :: tl =>
      wrng lo hi rl k' (Z.of_nat n') && wdisj lo hi rr k n rl k' (Z.of_nat n') && wch_chk lo hi tl rr k n
  end.

Lemma wrng_spec : forall lo hi rel k n b, lo <= b <= hi -> 0 <= n -> wrng lo hi rel k n = true ->
  0 <= wadr b rel k /\ wadr b rel k < 2^64 /\ wadr b rel k + n <= 2^64.
Proof.
  intros lo hi rel k n b Hb Hn H. unfold wrng, wf_M64, wmin, wmax in H. unfold wadr.
  apply andb_true_iff in H. destruct H as [H H3]. apply andb_true_iff in H. destruct H as [H1 H2].
  apply Z.leb_le in H1. apply Z.ltb_lt in H2. apply Z.leb_le in H3.
  change (2^64) with 18446744073709551616. destruct rel; lia.
Qed.

Lemma wdisj_spec : forall lo hi rr k n rl k' n' b, lo <= b <= hi -> wdisj lo hi rr k n rl k' n' = true ->
  wadr b rr k + n <= wadr b rl k' \/ wadr b rl k' + n' <= wadr b rr k.
Proof.
  intros lo hi rr k n rl k' n' b Hb H. unfold wdisj, wmin, wmax in H. unfold wadr.
  destruct rr, rl; cbn [Bool.eqb] in H; apply orb_true_iff in H; destruct H as [H|H]; apply Z.leb_le in H; lia.
Qed.

Lemma rdn_wch_skip : forall segs (b lo hi : Z) (l : list wlay) (m : word -> option byte) (za : Z) (rr : bool) (k : Z) (n : nat),
  lo <= b <= hi -> za = wadr b rr k ->
  wrng lo hi rr k (Z.of_nat n) = true ->
  wch_facts b l -> wch_chk lo hi l rr k (Z.of_nat n) = true ->
  rdn segs (wch_den m l) (Z_to_bv 64 za) n = rdn segs m (Z_to_bv 64 za) n.
Proof.
  intros segs b lo hi l m za rr k n Hb Hza Hr. subst za.
  destruct (wrng_spec lo hi rr k (Z.of_nat n) b Hb ltac:(lia) Hr) as (A1 & A2 & A3).
  induction l as [|[za' rl k' n' bs] tl IH]; cbn [wch_den wch_facts wch_chk]; intros HF HC; [reflexivity|].
  destruct HF as [[Hza' Hlen] HF]. subst za'.
  apply andb_true_iff in HC. destruct HC as [HC HC3]. apply andb_true_iff in HC. destruct HC as [HC1 HC2].
  destruct (wrng_spec lo hi rl k' (Z.of_nat n') b Hb ltac:(lia) HC1) as (B1 & B2 & B3).
  pose proof (wdisj_spec lo hi rr k (Z.of_nat n) rl k' (Z.of_nat n') b Hb HC2) as D.
  rewrite rdn_wbytes_out.
  - apply IH; assumption.
  - rewrite !u_Z2bv by assumption. rewrite Hlen. exact D.
  - rewrite u_Z2bv by assumption. exact A3.
  - rewrite u_Z2bv by assumption. rewrite Hlen. exact B3.
Qed.

(* [comment removed for export] *)

Ltac wf_is_Zlit z :=
  lazymatch z with
  | Z0 => idtac
  | Zpos ?p => wf_is_poslit p
  | Zneg ?p => wf_is_poslit p
  end
with wf_is_poslit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => wf_is_poslit q
  | xI ?q => wf_is_poslit q
  end.

(* [comment removed for export] *)
Ltac wf_zoff za :=
  let islit := match goal with
               | _ => let _ := match goal with _ => wf_is_Zlit za end in constr:(true)
               | _ => constr:(false)
               end in
  lazymatch islit with
  | true => constr:((0, za))
  | false =>
      lazymatch za with
      | (?x + ?c) =>
          let cl := match goal with
                    | _ => let _ := match goal with _ => wf_is_Zlit c end in constr:(true)
                    | _ => constr:(false)
                    end in
          lazymatch cl with
          | true => let r := wf_zoff x in
                    lazymatch r with (?b, ?k) => let k' := eval cbv in (k + c) in constr:((b, k')) end
          | false => constr:((za, 0))
          end
      | (?x - ?c) =>
          let cl := match goal with
                    | _ => let _ := match goal with _ => wf_is_Zlit c end in constr:(true)
                    | _ => constr:(false)
                    end in
          lazymatch cl with
          | true => let r := wf_zoff x in
                    lazymatch r with (?b, ?k) => let k' := eval cbv in (k - c) in constr:((b, k')) end
          | false => constr:((za, 0))
          end
      | _ => constr:((za, 0))
      end
  end.

(* [comment removed for export] *)
Ltac wf_is_natlit n :=
  lazymatch n with
  | O => idtac
  | S ?m => wf_is_natlit m
  end.
Ltac wf_len bs :=
  lazymatch bs with
  | word_to_le_bytes ?n _ => let _ := match goal with _ => wf_is_natlit n end in n
  | repeat _ ?n => let _ := match goal with _ => wf_is_natlit n end in n
  | nil => constr:(O)
  | _ :: ?tl => let m := wf_len tl in constr:(S m)
  | _ =>
      (* [comment removed for export] *)
      lazymatch bs with
      | ?f ?n => let _ := match goal with _ => wf_is_natlit n end in
                 let _ := match goal with _ => is_const f end in
                 let b' := eval cbv delta [f] beta in bs in
                 lazymatch b' with repeat _ n => n end
      end
  end.

(* [comment removed for export] *)
Ltac wch_find_base ch :=
  lazymatch ch with
  | wbytes ?m (Z_to_bv 64 ?za') _ =>
      let r := wf_zoff za' in
      lazymatch r with
      | (Z0, _) => wch_find_base m
      | (?b', _) => b'
      end
  | _ => constr:(Z0)
  end.

(* [comment removed for export] *)
Ltac wch_reify ch b lo hi rr k n :=
  match ch with
  | wbytes ?m (Z_to_bv 64 ?za') ?bs =>
      let r := wf_zoff za' in
      lazymatch r with
      | (?b', ?k') =>
          let rl := lazymatch b' with
                    | Z0 => constr:(false)
                    | _ => let _ := match goal with _ => constr_eq b' b end in constr:(true)
                    end in
          let n' := wf_len bs in
          let _ := match goal with _ => wf_is_Zlit k' end in
          let ok := eval vm_compute in (wdisj lo hi rr k (Z.of_nat n) rl k' (Z.of_nat n')) in
          lazymatch ok with
          | true => let tl := wch_reify m b lo hi rr k n in constr:(WLay za' rl k' n' bs :: tl)
          end
      end
  | _ => constr:(@nil wlay)
  end.

Ltac wch_base ch l :=
  lazymatch l with
  | nil => ch
  | _ :: ?tl => lazymatch ch with wbytes ?m _ _ => wch_base m tl end
  end.

Ltac wch_facts_tac :=
  unfold wadr; repeat split; first [ reflexivity | apply length_N_to_le_bytes | apply repeat_length | lia ].

(* [comment removed for export] *)
Ltac rdn_peel_fast1 :=
  lazymatch goal with
  | |- rdn ?segs ?ch (Z_to_bv 64 ?za) ?n = _ =>
      lazymatch ch with wbytes (wbytes _ _ _) _ _ => idtac end;
      wf_is_natlit n;   (* [comment removed for export] *)
      let r := wf_zoff za in
      lazymatch r with
      | (?br, ?k) =>
          let b := lazymatch br with Z0 => wch_find_base ch | _ => br end in
          let rr := lazymatch br with Z0 => constr:(false) | _ => constr:(true) end in
          let lo := lazymatch b with Z0 => constr:(0) | _ => constr:(4294967296) end in
          let hi := lazymatch b with Z0 => constr:(0) | _ => constr:(9223372036854775808) end in
          wf_is_Zlit k;
          let l := wch_reify ch b lo hi rr k n in
          lazymatch l with nil => fail | _ :: nil => fail | _ => idtac end;
          let m := wch_base ch l in
          let Hb := fresh "wfHb" in
          assert (Hb : lo <= b <= hi)
            by (first [ solve [ repeat match goal with H : _ \/ _ |- _ => clear H end; lia ] | lia ]);
          let Hza := fresh "wfHza" in
          assert (Hza : za = wadr b rr k) by (unfold wadr; first [ reflexivity | lia ]);
          let HF := fresh "wfHF" in
          assert (HF : wch_facts b l) by wch_facts_tac;
          change ch with (wch_den m l);
          rewrite (rdn_wch_skip segs b lo hi l m za rr k n Hb Hza (@eq_refl bool true) HF (@eq_refl bool true));
          clear Hb Hza HF
      end
  end.
