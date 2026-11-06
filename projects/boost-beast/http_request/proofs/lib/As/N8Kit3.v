(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.boost_beast.http_request.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import Tac Arr CellsX TacX.
From OSSVerify.Proofs.boost_beast.http_request.lib.As Require Import ASegs AsShadow AsConst AsIface AsCXXHeap AsWalk AsStack0 N8Kit N8Kit2.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac lia_goal_ok :=
  lazymatch goal with
  | |- (_ <= _)%Z => idtac | |- (_ < _)%Z => idtac | |- (_ >= _)%Z => idtac | |- (_ > _)%Z => idtac
  | |- (_ <= _)%nat => idtac | |- (_ < _)%nat => idtac | |- (_ >= _)%nat => idtac | |- (_ > _)%nat => idtac
  | |- (_ <= _)%N => idtac | |- (_ < _)%N => idtac
  | |- @eq _ _ _ => idtac | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- _ -> _ => idtac
  | |- _ <-> _ => idtac | |- False => idtac | |- True => idtac | |- Z.divide _ _ => idtac
  | |- forall _, _ => idtac
  | |- placed _ _ _ => idtac
  | |- _ => fail
  end.
(* [comment removed for export] *)
Ltac lia_exfalso := exfalso; first [ lia_t1 | progress side_split; lia_t1 | lia_t2 | lia_t3 ].
Ltac few_placed :=
  match goal with
  | _ : placed _ _ _, _ : placed _ _ _, _ : placed _ _ _, _ : placed _ _ _ |- _ => fail
  | _ => idtac
  end.
Ltac lia ::=
  unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *;
  first [ lazymatch goal with
          | |- aapp _ _ => aapp_win
          | |- _ /\ _ => split; lia
          end
        | first [ lia_goal_ok | lia_exfalso ];
          first [ lia_t1
                | progress side_split; lia_t1
                | lia_t2
                | lia_t3
                | progress side_split; first [lia_t2 | lia_t3]
                | progress aapp_facts;
                  first [ lia_t1 | progress side_split; lia_t1 | lia_t2 | lia_t3 | progress side_split; first [lia_t2 | lia_t3]
                        | few_placed; progress side_split_all; first [lia_t1 | lia_t3] ]
                | few_placed; progress side_split_all; first [lia_t1 | lia_t3] ] ].

(* [comment removed for export] *)
Definition hideL (P : Prop) : Prop := P.
Ltac hydeL H := lazymatch type of H with ?T => change T with (hideL T) in H end.
Ltac unhideL := unfold hideL in *.

(* [comment removed for export] *)
Section K3.
  Context {HCEIL : HeapCeil}.
  Lemma aapp_num3 : forall A n, aapp A n -> 0 <= n ->
    ((6811648 <= A /\ A + n <= 2147446784 /\ 2148302336 <= sh A /\ sh A + nsh n <= 2415881728)
     \/ (17594333495296 <= A /\ 2201439137792 <= sh A))
    /\ (0 < A /\ 6811648 <= A /\ A + n <= aceil /\ 2148302336 <= sh A /\ sh A + nsh n <= sh aceil
        /\ 17594064011264 <= sh aceil <= 17594332446720 /\ 140735332483072 <= aceil <= 140737479966720 /\ aceil <= hceil).
  Proof.
    intros A n H Hn. pose proof (aapp_num2 A n H Hn) as [D (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9 & C10 & C11)].
    split; [exact D|]. repeat split; first [assumption | lia_t3].
  Qed.
  Lemma aapp_num0' : forall A n, aapp A n ->
    ((6811648 <= A /\ A + n <= 2147446784 /\ 2148302336 <= sh A) \/ (17594333495296 <= A /\ 2201439137792 <= sh A))
    /\ (0 < A /\ 6811648 <= A /\ A + n <= aceil /\ 2148302336 <= sh A
        /\ 17594064011264 <= sh aceil <= 17594332446720 /\ 140735332483072 <= aceil <= 140737479966720 /\ aceil <= hceil).
  Proof.
    intros A n H. pose proof (aapp_num0 A n H) as [D (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8 & C9)].
    split; [exact D|]. repeat split; first [assumption | lia_t3].
  Qed.
End K3.

(* [comment removed for export] *)
Ltac nsh_lits K :=
  repeat match type of K with
  | context [nsh ?a] => is_Zlit a; let v := eval cbv in (nsh a) in change (nsh a) with v in K
  end.

Ltac aapp_fact H ::=
  lazymatch type of H with
  | aapp ?A0 ?n0 =>
    let A1 := eval cbn [blk_addr blk_size fst snd] in A0 in
    let A := eval unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in A1 in
    let n1 := eval cbn [blk_addr blk_size fst snd] in n0 in
    let n := eval unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in n1 in
    lazymatch goal with
    | _ : aapp_seen A n |- _ => idtac
    | _ =>
      let K := fresh "APP" in let K2 := fresh "APQ" in let M := fresh "APPs" in
      first
        [ pose proof (aapp_num3 _ _ H ltac:(cbn [blk_addr blk_size fst snd]; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *;
                                         rewrite ?fsz_1, ?fsz_4;
                                         first [ lia_t1
                                               | apply (Z.le_trans 0 64); [lia_t1| apply fsz_pos; lia_t1]
                                               | unfold fsz, fshn in *;
                                                 repeat match goal with |- context [2 ^ ?k] =>
                                                   lazymatch goal with _ : 0 <= 2 ^ k |- _ => fail | _ => pose proof (Z.pow_nonneg 2 k ltac:(lia_t1)) end end;
                                                 lia_t1 ])) as K
        | pose proof (aapp_num0' _ _ H) as K ];
      cbn [blk_addr blk_size fst snd] in K; unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in K;
      rewrite ?fsz_1, ?fsz_4 in K; nsh_lits K;
      destruct K as [K K2];
      lazymatch type of K with ?P => change P with (placed A n P) in K end;
      pose proof (I : aapp_seen A n) as M
    end
  end.

(* [comment removed for export] *)
From Ltac2 Require Import Ltac2.
From OSSVerify.Proofs.boost_beast.http_request.lib.Lib Require Import LiaTuning.

(* [comment removed for export] *)
Ltac2 n8_is_op (f : constr) : bool :=
  List.exist (fun c => Constr.equal f c)
    ['@Z.add; '@Z.sub; '@Z.mul; '@Z.opp; '@Z.le; '@Z.lt; '@Z.ge; '@Z.gt; '@Z.max; '@Z.min; '@Z.div; '@Z.modulo;
     '@Z.pow; '@Z.shiftr; '@Z.shiftl; '@Z.land; '@Z.lor; '@Z.of_nat; '@Z.to_nat; '@Z.of_N; '@Z.abs; '@Z.succ; '@Z.pred;
     '@Nat.add; '@Nat.sub; '@Nat.mul; '@le; '@lt; '@ge; '@gt; '@N.le; '@N.lt; '@Zpos; '@Zneg; '@xI; '@xO;
     '@and; '@or; '@not; '@iff; '@eq].
Ltac2 rec n8_atoms (t : constr) (acc : constr list) : constr list :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App f args =>
      if n8_is_op f then List.fold_left (fun a x => n8_atoms x a) acc (Array.to_list args)
      else (if List.exist (fun c => Constr.equal c t) acc then acc else t :: acc)
  | Constr.Unsafe.Prod b c => n8_atoms c (n8_atoms (Constr.Binder.type b) acc)
  | Constr.Unsafe.Cast c _ _ => n8_atoms c acc
  | Constr.Unsafe.Var _ => if List.exist (fun c => Constr.equal c t) acc then acc else t :: acc
  | _ => acc   (* [comment removed for export] *)
  end.
Ltac2 n8_shares (vs : constr list) (l : constr list) : bool := List.exist (fun x => List.exist (fun y => Constr.equal x y) l) vs.

Ltac2 n8_relevant_prune (rounds : int) : unit :=
  let g := Control.goal () in
  let hs := Control.hyps () in
  let facts := List.map_filter (fun h => let (id, body, ty) := h in
                 match body with
                 | Some _ => None
                 | None => if LiaTuning.zt_plain_arith ty then Some (id, n8_atoms ty []) else None
                 end) hs in
  let rec loop (n : int) (vs : constr list) :=
    if Int.le n 0 then vs else
    loop (Int.sub n 1)
         (List.fold_left (fun acc f => let (id, ats) := f in
                            if n8_shares ats vs then List.append ats acc else acc) vs facts) in
  let keep := loop rounds (n8_atoms g []) in
  let drop := List.map_filter (fun f => let (id, ats) := f in if n8_shares ats keep then None else Some id) facts in
  match drop with [] => () | _ :: _ => Std.clear drop end.

Ltac lia_t0 := ltac2:(Control.enter (fun () => n8_relevant_prune 1)); lia_t1.

Ltac lia ::=
  unfold AFS_SIZE, AFS_HDR, AFS_FLAGS in *;
  first [ lazymatch goal with
          | |- aapp _ _ => aapp_win
          | |- _ /\ _ => split; lia
          end
        | first [ lia_goal_ok | lia_exfalso ];
          first [ lia_t1
                | progress side_split; lia_t1
                | lia_t2
                | lia_t3
                | progress side_split; first [lia_t2 | lia_t3]
                | progress aapp_facts;
                  first [ lia_t1 | progress side_split; lia_t1 | lia_t2 | lia_t3 | progress side_split; first [lia_t2 | lia_t3]
                        | few_placed; progress side_split_all; first [lia_t1 | lia_t3] ]
                | few_placed; progress side_split_all; first [lia_t1 | lia_t3] ] ].

(* [comment removed for export] *)
Ltac flia ::= first [ assumption | slim; first [lia_t1 | progress side_split; lia_t1 | lia_t2] ].
