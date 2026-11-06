(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common Require Import PropExec CatExec CatSim StepTac Hoare StoreOk MemSplit RefMemcpyLib FPSteps.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.CliDriver Require Import Amb SymExec2 SymExec2Sound SymRun SymDrive SymDriveX RefPrintfLib.
From OSSVerify.Proofs.leptonica.grayquant_fuzzer.lib.Common.Leptonica Require Import WalksLib LeptStructs GrayLib.
Import ListNotations. Import SX2. Import SX2S.
Open Scope bv_scope.
Unset Lia Cache.
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_regs_list : list reg := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%bv.
(* [comment removed for export] *)
Definition ex_envL (prev : list word) (regs : bvmap 5 word) (bases : list Z) : env :=
  Env (vals_ev (prev ++ map (getr regs) ex_regs_list ++ map (Z_to_bv 64) bases)) (blobs_ev []).
Abbreviation ex_env regs bases := (ex_envL [] regs bases).
(* [comment removed for export] *)
Definition ex_sr0 : list expr :=
  [ELit 0; EVar 1; EVar 2; EVar 3; EVar 4; EVar 5; EVar 6; EVar 7; EVar 8; EVar 9; EVar 10; EVar 11; EVar 12; EVar 13; EVar 14; EVar 15;
   EVar 16; EVar 17; EVar 18; EVar 19; EVar 20; EVar 21; EVar 22; EVar 23; EVar 24; EVar 25; EVar 26; EVar 27; EVar 28; EVar 29; EVar 30; EVar 31].
Definition ex_set (sr : list expr) (n : nat) (e : expr) : list expr := sr_upd sr n e.
(* [comment removed for export] *)
Definition ex_r1 : reg := 1%bv.   Definition ex_r2 : reg := 2%bv.   Definition ex_r3 : reg := 3%bv.   Definition ex_r4 : reg := 4%bv.   Definition ex_r8 : reg := 8%bv.
Definition ex_r9 : reg := 9%bv. Definition ex_r10 : reg := 10%bv. Definition ex_r11 : reg := 11%bv. Definition ex_r12 : reg := 12%bv. Definition ex_r13 : reg := 13%bv.
(* [comment removed for export] *)
Definition ex_keep (P : Prop) : Prop := P.
(* [comment removed for export] *)
Definition ex_done (P : Prop) : Prop := P.

Lemma ex_ptr_val : forall (b c : Z), alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 c) = Z_to_bv 64 (b + c).
Proof. exact alu_add_Z. Qed.

Definition ex_srJ (jb : nat) : list expr := ELit 0 :: map (fun k => EVar (jb + k)) (seq 1 31).

(* [comment removed for export] *)
Lemma ex_regs_ok_junk : forall (prev : list word) regs bases (jb : nat), length prev = jb ->
  regs_ok (ex_envL prev regs bases) (ex_srJ jb) regs.
Proof.
  intros prev regs bases jb Hjb r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. reflexivity.
  - pose proof (ridx_range r) as Hlt. rewrite <- (ridx_roundtrip r) at 1. rewrite <- (ridx_roundtrip r) in Hr0.
    set (n := ridx r) in *. clearbody n.
    assert (Hn0 : n <> 0%nat) by (intros ->; vm_compute in Hr0; discriminate Hr0).
    unfold ex_srJ. replace n with (S (n - 1)) at 2 by lia. cbn [nth].
    rewrite (nth_indep _ (ELit 0) (EVar (jb + S (n - 1)))) by (rewrite length_map, length_seq; lia).
    rewrite (map_nth (fun k => EVar (jb + k)) (seq 1 31) (S (n - 1)) (n - 1)). rewrite seq_nth by lia.
    replace (1 + (n - 1))%nat with n by lia. cbn [edenot ev ex_envL]. unfold vals_ev.
    rewrite app_nth2 by lia. replace (jb + n - length prev)%nat with n by lia.
    rewrite app_nth1 by (rewrite length_map; cbn [length ex_regs_list]; lia).
    rewrite (nth_indep _ (Z_to_bv 64 0) (getr regs 0%bv)) by (rewrite length_map; cbn [length ex_regs_list]; lia).
    rewrite (map_nth (getr regs) ex_regs_list 0%bv n). f_equal.
    do 32 (destruct n as [|n]; [first [exfalso; apply Hn0; reflexivity | apply bv_eq; reflexivity]|]). exfalso. lia.
Qed.

Lemma ex_reg_ne0 : forall r : reg, bv_unsigned r <> 0%Z -> r <> 0%bv.
Proof. intros r H X. apply H. rewrite X. reflexivity. Qed.

(* [comment removed for export] *)
Lemma ex_regs_ok_reexpr : forall E sr regs (r : reg) (e : expr),
  regs_ok E sr regs -> r <> 0%bv -> getr regs r = edenot E e -> regs_ok E (sr_upd sr (ridx r) e) regs.
Proof.
  intros E sr regs r e HR Hr He r'. unfold sr_get. destruct (bv_eqb r' 0) eqn:Hr0.
  - specialize (HR r'). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
  - rewrite nth_sr_upd. destruct (Nat.eqb (ridx r') (ridx r)) eqn:Hi.
    + apply Nat.eqb_eq in Hi. apply ridx_inj in Hi. subst r'. exact He.
    + specialize (HR r'). unfold sr_get in HR. rewrite Hr0 in HR. exact HR.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ex_word_idx vals w :=
  match vals with
  | w :: _ => constr:(O)
  | _ :: ?tl => let i := ex_word_idx tl w in constr:(S i)
  end.
Ltac ex_classify vals t jbk :=
  match t with
  | _ => let b := eval vm_compute in (Z.eqb t t) in lazymatch b with true => constr:(ELit t) end
  | (?b + ?c)%Z => let cb := eval vm_compute in (Z.eqb c c) in
                   lazymatch cb with true => let i := ex_word_idx vals (Z_to_bv 64 b) in constr:(EAlu ALU_ADD (EVar i) (ELit c)) end
  | (?b - ?c)%Z => let cb := eval vm_compute in (Z.eqb c c) in
                   lazymatch cb with true => let i := ex_word_idx vals (Z_to_bv 64 b) in let c' := eval vm_compute in (- c)%Z in
                                             constr:(EAlu ALU_ADD (EVar i) (ELit c')) end
  | _ => let i := ex_word_idx vals (Z_to_bv 64 t) in constr:(EVar i)
  | _ => constr:(EVar jbk)
  end.

(* [comment removed for export] *)
Ltac ex_classify_pf regs vals t jbk H HR :=
  (* [comment removed for export] *)
  lazymatch type of H with
  | getr regs ?r = Z_to_bv 64 _ =>
    let HR' := fresh "HRx" in
    first
    [ (* [comment removed for export] *)
      let b := eval vm_compute in (Z.eqb t t) in
      lazymatch b with true =>
        pose proof (ex_regs_ok_reexpr _ _ regs r (ELit t) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) H) as HR' end
    | (* [comment removed for export] *)
      lazymatch t with
      | (?b + ?c)%Z => let cb := eval vm_compute in (Z.eqb c c) in
          lazymatch cb with true => let i := ex_word_idx vals (Z_to_bv 64 b) in
            pose proof (ex_regs_ok_reexpr _ _ regs r (EAlu ALU_ADD (EVar i) (ELit c)) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate)
                          ltac:(etransitivity; [exact H|]; symmetry; change (alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 c) = Z_to_bv 64 (b + c)); apply ex_ptr_val)) as HR' end
      end
    | (* [comment removed for export] *)
      lazymatch t with
      | (?b - ?c)%Z => let cb := eval vm_compute in (Z.eqb c c) in
          lazymatch cb with true => let i := ex_word_idx vals (Z_to_bv 64 b) in let c' := eval vm_compute in (- c)%Z in
            pose proof (ex_regs_ok_reexpr _ _ regs r (EAlu ALU_ADD (EVar i) (ELit c')) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate)
                          ltac:(etransitivity; [exact H|]; symmetry; change (alu64 ALU_ADD (Z_to_bv 64 b) (Z_to_bv 64 c') = Z_to_bv 64 (b - c)); rewrite ex_ptr_val; f_equal; lia)) as HR' end
      end
    | (* [comment removed for export] *)
      let i := ex_word_idx vals (Z_to_bv 64 t) in
      pose proof (ex_regs_ok_reexpr _ _ regs r (EVar i) HR ltac:(apply ex_reg_ne0; vm_compute; discriminate) H) as HR' ];
    clear HR; rename HR' into HR
  end.
Ltac ex_collect regs vals jb HR :=
  repeat match goal with
  | H : getr regs ?r = Z_to_bv 64 ?t |- _ =>
      let n := eval vm_compute in (Z.to_nat (bv_unsigned r)) in
      let jbk := eval vm_compute in (jb + n)%nat in
      first [ ex_classify_pf regs vals t jbk H HR | idtac ];
      change (getr regs r = Z_to_bv 64 t) with (ex_done (getr regs r = Z_to_bv 64 t)) in H
  end;
  unfold ex_done in *.

(* [comment removed for export] *)
Ltac ex_unfoldE :=
  repeat match goal with E := ex_envL _ _ _ |- _ => progress (unfold E) end;
  repeat match goal with P := _ : list word |- _ => progress (unfold P) end.

(* [comment removed for export] *)
Ltac ex_regs_ok1 regs :=
  first [ reflexivity
        | (repeat match goal with |- context [ridx ?x] => let v := eval vm_compute in (ridx x) in change (ridx x) with v end;
           ex_unfoldE; cbn [nth edenot ev ex_envL vals_ev map app ex_regs_list];
           first [ reflexivity
                 | assumption
                 | match goal with H : getr regs _ = Z_to_bv 64 _ |- _ =>
                     etransitivity; [exact H|]; first [ reflexivity | symmetry; rewrite ex_ptr_val; f_equal; lia ] end ]) ].

Ltac ex_regs_ok regs :=
  let r := fresh "r" in let Hr0 := fresh "Hr0" in let n := fresh "n" in let Hlt := fresh "Hlt" in
  intro r; unfold sr_get; destruct (bv_eqb r 0) eqn:Hr0;
  [ assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia); subst r; reflexivity
  | pose proof (ridx_range r) as Hlt; rewrite <- (ridx_roundtrip r); rewrite <- (ridx_roundtrip r) in Hr0;
    set (n := ridx r) in *; clearbody n;
    do 32 (destruct n as [|n]; [ first [ discriminate Hr0 | ex_regs_ok1 regs ] |]);
    exfalso; lia ].

(* [comment removed for export] *)
Ltac ex_entryL prev regs bases HR :=
  let prev' := eval hnf in prev in
  let vals := eval cbv beta iota delta [app map ex_regs_list] in (prev' ++ map (getr regs) ex_regs_list ++ map (Z_to_bv 64) bases) in
  let jb := eval vm_compute in (length prev') in
  pose proof (ex_regs_ok_junk prev regs bases jb ltac:(vm_cast_no_check (eq_refl jb))) as HR;
  ex_collect regs vals jb HR;
  lazymatch type of HR with regs_ok ?E ?sr ?R => let sr' := eval vm_compute in sr in change (regs_ok E sr' R) in HR end.
Ltac ex_entry regs bases HR := ex_entryL (@nil word) regs bases HR.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_apart (p n q k : Z) : Prop := (p + n <= q \/ q + k <= p)%Z.
Lemma ex_apart_intro : forall p n q k : Z, (p + n <= q \/ q + k <= p)%Z -> ex_apart p n q k.
Proof. intros p n q k H. exact H. Qed.

Section Know.
Context {fx : FPState}.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma ex_kwr : forall E m (e : expr) (b off n lo : Z) (N : nat),
  edenot E e = Z_to_bv 64 b -> store_ok segs m (Z_to_bv 64 lo) N = true ->
  (0 <= lo)%Z -> (lo + Z.of_nat N <= 2 ^ 64)%Z -> (0 <= b < 2 ^ 64)%Z -> (lo <= b + off)%Z -> (0 < n)%Z -> (b + off + n <= lo + Z.of_nat N)%Z ->
  kentry_ok segs E m (KWr (SA e off) n).
Proof.
  intros E m e b off n lo N He HS Hlo HN Hb H1 Hn H2. cbn [kentry_ok]. unfold flat, estart. cbn [a_base a_off]. rewrite He, u_Z2bv by lia.
  split; [lia|]. intros d k Hd Hk. destruct k as [|k]; [reflexivity|].
  apply (store_ok_sub segs m (Z_to_bv 64 lo) _ N (S k)); rewrite ?u_Z2bv by lia; try lia. exact HS.
Qed.

(* [comment removed for export] *)
Lemma ex_kword_Z : forall E m (e v : expr) (b off z : Z) (w : nat),
  edenot E e = Z_to_bv 64 b -> edenot E v = Z_to_bv 64 z -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= b < 2 ^ 64)%Z -> (0 <= b + off)%Z -> (b + off + Z.of_nat w <= 2 ^ 64)%Z -> (0 <= z < 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (b + off)) w = Some (Z_to_le_bytes w z) ->
  kentry_ok segs E m (KWord (SA e off) w v).
Proof.
  intros E m e v b off z w He Hv Hw1 Hw Hb H1 H2 Hz Hr.
  apply (kword_intro segs E m e (Z_to_bv 64 b) off w v (Z_to_bv 64 z) He Hv Hw1 Hw); rewrite u_Z2bv by lia; [lia | lia |].
  rewrite (w2b_Z w z Hz). exact Hr.
Qed.

(* [comment removed for export] *)
Lemma ex_kword_w : forall E m (e v : expr) (b off : Z) (x : word) (w : nat),
  edenot E e = Z_to_bv 64 b -> edenot E v = x -> (1 <= w)%nat -> (w <= 8)%nat ->
  (0 <= b < 2 ^ 64)%Z -> (0 <= b + off)%Z -> (b + off + Z.of_nat w <= 2 ^ 64)%Z ->
  rdn segs m (Z_to_bv 64 (b + off)) w = Some (word_to_le_bytes w x) ->
  kentry_ok segs E m (KWord (SA e off) w v).
Proof.
  intros E m e v b off x w He Hv Hw1 Hw Hb H1 H2 Hr.
  apply (kword_intro segs E m e (Z_to_bv 64 b) off w v x He Hv Hw1 Hw); rewrite u_Z2bv by lia; [lia | lia | exact Hr].
Qed.

Lemma ex_krange : forall E m (e : expr) (b lo hi : Z),
  edenot E e = Z_to_bv 64 b -> (0 <= b < 2 ^ 64)%Z -> (lo <= b <= hi)%Z -> kentry_ok segs E m (KRange e lo hi).
Proof. intros E m e b lo hi He Hb H. apply krange_intro. rewrite He, u_Z2bv by lia. exact H. Qed.

Lemma ex_kalign : forall E m (e : expr) (b k : Z),
  edenot E e = Z_to_bv 64 b -> (0 <= b < 2 ^ 64)%Z -> (0 < k)%Z -> (b mod k = 0)%Z -> kentry_ok segs E m (KAlign e k).
Proof. intros E m e b k He Hb Hk H. apply kalign_intro; [exact Hk|]. rewrite He, u_Z2bv by lia. exact H. Qed.

Lemma ex_kdisj : forall E m (e1 e2 : expr) (b1 b2 o1 n1 o2 n2 : Z),
  edenot E e1 = Z_to_bv 64 b1 -> edenot E e2 = Z_to_bv 64 b2 -> (0 <= b1 < 2 ^ 64)%Z -> (0 <= b2 < 2 ^ 64)%Z ->
  (b1 + o1 + n1 <= b2 + o2 \/ b2 + o2 + n2 <= b1 + o1)%Z -> kentry_ok segs E m (KDisj (SA e1 o1) n1 (SA e2 o2) n2).
Proof.
  intros E m e1 e2 b1 b2 o1 n1 o2 n2 H1 H2 R1 R2 D. cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite H1, H2, !u_Z2bv by lia. exact D.
Qed.

(* [comment removed for export] *)
Lemma ex_kdisj_apart : forall E m (e1 e2 : expr) (b1 b2 o1 n1 o2 n2 : Z),
  edenot E e1 = Z_to_bv 64 b1 -> edenot E e2 = Z_to_bv 64 b2 -> (0 <= b1 < 2 ^ 64)%Z -> (0 <= b2 < 2 ^ 64)%Z ->
  ex_apart (b1 + o1) n1 (b2 + o2) n2 -> kentry_ok segs E m (KDisj (SA e1 o1) n1 (SA e2 o2) n2).
Proof. intros E m e1 e2 b1 b2 o1 n1 o2 n2 H1 H2 R1 R2 D. apply (ex_kdisj E m e1 e2 b1 b2 o1 n1 o2 n2 H1 H2 R1 R2). exact D. Qed.
End Know.

(* [comment removed for export] *)
Ltac ex_eden regs :=
  first [ reflexivity
        | apply WalksLib.zbv_self
        | match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => exact H end
        | (ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
           first [ reflexivity | match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => exact H end ]) ].

(* [comment removed for export] *)
Ltac ex_natlia := first [ lia | (rewrite ?Z2Nat.id by lia; lia) | (cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia) ].

(* [comment removed for export] *)
Ltac ex_know1 regs :=
  lazymatch goal with
  | |- kentry_ok _ _ _ (KRange _ _ _) => eapply ex_krange; [ex_eden regs | lia | lia]
  | |- kentry_ok _ _ _ (KAlign _ _) => eapply ex_kalign; [ex_eden regs | lia | lia | first [assumption | lia | idtac]]
  | |- kentry_ok _ _ _ (KImg _ _) => apply kimg_intro; [lia | lia | first [assumption | let i := fresh "i" in let Hi := fresh "Hi" in intros i Hi; match goal with H : forall j, _ -> _ (Z_to_bv 64 j) = None |- _ => apply H; lia end | idtac]]
  | |- kentry_ok _ _ _ (KWr _ _) =>
      match goal with H : store_ok _ _ (Z_to_bv 64 _) _ = true |- _ =>
        eapply ex_kwr; [ex_eden regs | exact H | lia | ex_natlia | lia | lia | lia | ex_natlia] end
  | |- kentry_ok _ _ _ (KWord _ _ _) =>
      first [ match goal with H : rdn _ _ (Z_to_bv 64 _) _ = Some (Z_to_le_bytes _ _) |- _ =>
                eapply ex_kword_Z; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | lia
                                   | first [exact H | rewrite Z.add_0_r; exact H | match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => match type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a with a' by lia; exact H end end] ] end
            | match goal with H : rdn _ _ (Z_to_bv 64 _) _ = Some (word_to_le_bytes _ _) |- _ =>
                eapply ex_kword_w; [ex_eden regs | ex_eden regs | lia | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
                                   | first [exact H | rewrite Z.add_0_r; exact H | match goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => match type of H with rdn _ _ (Z_to_bv 64 ?a') _ = _ => replace a with a' by lia; exact H end end] ] end ]
  | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
      first [ (eapply ex_kdisj_apart; [ex_eden regs | ex_eden regs | lia | lia | assumption])
            | (eapply ex_kdisj; [ex_eden regs | ex_eden regs | lia | lia | lia]) ]
  | |- _ => idtac
  end.

Ltac ex_know regs := repeat (apply Forall_cons || apply Forall_nil); try (ex_know1 regs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ex_pow2 := repeat match goal with |- context [(2 ^ ?e)%Z] => lazymatch e with context [Z.of_nat] => let v := eval vm_compute in (2 ^ e)%Z in change (2 ^ e)%Z with v end end.
(* [comment removed for export] *)
Lemma ex_sx32 : forall z : Z, (0 <= z < 2 ^ 31)%Z -> ext_val true 0 4 (Z_to_bv 64 z) = Z_to_bv 64 z.
Proof. intros z Hz. apply ext_val_sx_id; [lia|]. rewrite u_Z2bv by lia. change (8 * Z.of_nat 4 - 1)%Z with 31%Z. lia. Qed.
Ltac ex_br :=
  repeat (rewrite ex_sx32 by lia);
  repeat first [ rewrite ext_val_sx_id by (first [ lia | (rewrite ?u_Z2bv by lia; ex_pow2; lia) ])
               | rewrite ext_val_zx_id by (rewrite ?u_Z2bv by lia; ex_pow2; lia) ];
  cbn [branch_taken]; unfold bv_eqb, bv_ltu, bv_lts;
  rewrite ?bv_signed_Zs by lia; rewrite ?u_Z2bv by lia;
  first [ apply Z.eqb_eq | apply Z.eqb_neq | apply Z.ltb_lt | apply Z.ltb_ge
        | (apply negb_true_iff; first [apply Z.eqb_neq | apply Z.ltb_ge])
        | (apply negb_false_iff; first [apply Z.eqb_eq | apply Z.ltb_lt]) ];
  lia.

(* [comment removed for export] *)
Ltac ex_sc regs :=
  ex_unfoldE; unfold sc_denot, flat, estart, elenZ, adenot;
  cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  rewrite ?ex_ptr_val, ?zbv_addi;
  first [ lia | (rewrite ?u_Z2bv by lia; lia) | ex_br | idtac ].

(* [comment removed for export] *)
Ltac ex_nx E :=
  let E' := eval hnf in E in
  lazymatch E' with
  | Env (vals_ev ?vals) _ => let n := eval vm_compute in (length vals) in n
  end.

(* [comment removed for export] *)
Ltac ex_run fuel stops scr HR HK R' HR' Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch goal with
      | |- context [mkst regs (Z_to_bv 64 ?pc) base ?rom] =>
          let nx := ex_nx E in
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in let Hlf := fresh "Hlf" in let Hex := fresh "Hex" in
              assert (Hex : sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr')) by (vm_cast_no_check (eq_refl (ss', scs, scr')));
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; ex_sc regs
              | destruct (run_sound segs fuel stops scr pc sr kn nx ss' scs scr' E base rom regs
                          Hex HR HK Hsc) as (R' & HR' & Hlf & Hms);
                clear Hsc Hlf Hex ]
          end
      end
    end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ex_wbytes_eq : forall (m1 m2 : word -> option byte) (a1 a2 : word) (b1 b2 : list byte),
  m1 = m2 -> a1 = a2 -> b1 = b2 -> wbytes m1 a1 b1 = wbytes m2 a2 b2.
Proof. intros; subst; reflexivity. Qed.

Lemma ex_msteps_mem : forall {fx : FPState} segs ms R pc (M M' : word -> option byte) rom,
  msteps segs ms (mkst R pc M rom) -> M' = M -> msteps segs ms (mkst R pc M' rom).
Proof. intros; subst; assumption. Qed.

(* [comment removed for export] *)
Lemma ex_sllw_small : forall a k : Z, (0 <= a)%Z -> (0 <= k < 32)%Z -> (a * 2 ^ k < 2 ^ 31)%Z ->
  v_sllw (Z_to_bv 64 a) (Z_to_bv 64 k) = Z_to_bv 64 (a * 2 ^ k).
Proof.
  intros a k Ha Hk Hs. unfold v_sllw.
  assert (a < 2 ^ 64)%Z by (assert (1 <= 2 ^ k)%Z by (apply Z.pow_le_mono_r with (b := 0%Z); lia); nia).
  rewrite !u_Z2bv by lia. rewrite Z.mod_small by lia. rewrite Z.shiftl_mul_pow2 by lia.
  f_equal. apply bv_swrap_small. change (bv_half_modulus 32) with (2 ^ 31)%Z. nia.
Qed.
Ltac ex_vnorm :=
  rewrite ?ex_ptr_val, ?alu_add, ?alu_sub, ?alu_and, ?alu_or, ?alu_xor, ?alu_sll, ?alu_srl, ?alu_sra, ?alu_slt, ?alu_sltu,
          ?w_addw, ?w_subw, ?w_sllw, ?w_srlw, ?w_sraw.

(* [comment removed for export] *)
Ltac ex_val regs :=
  ex_unfoldE; cbn [edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  rewrite ?ex_ptr_val;
  first [ reflexivity | assumption | symmetry; assumption | (f_equal; lia)
        | (repeat match goal with H : getr regs _ = _ |- _ => rewrite H end; ex_vnorm;
           first [ reflexivity | f_equal; lia | (rewrite ?ex_sllw_small by lia; first [reflexivity | f_equal; lia]) | idtac ]) ].
Ltac ex_reg regs HR' :=
  lazymatch goal with
  | |- getr _ ?k = _ =>
      rewrite (reg_val _ _ _ k HR');
      match goal with |- context [sr_get ?sr k] => let e := eval vm_compute in (sr_get sr k) in change (sr_get sr k) with e end;
      ex_val regs
  end.

(* [comment removed for export] *)
Ltac ex_addr_eq regs :=
  ex_unfoldE; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  rewrite ?ex_ptr_val, ?zbv_addi; first [ reflexivity | f_equal; lia ].
Ltac ex_bytes_eq regs :=
  first [ reflexivity
        | (f_equal; ex_val regs)
        | (rewrite <- w2b_Z by lia; f_equal; ex_val regs) ].
Ltac ex_mem_eq regs :=
  cbn [mem_denot s_log e_addr e_width e_val];
  repeat (apply ex_wbytes_eq; [ | ex_addr_eq regs | ex_bytes_eq regs ]);
  reflexivity.
Ltac ex_mem regs Hms :=
  eapply ex_msteps_mem; [exact Hms | ex_mem_eq regs].

(* [comment removed for export] *)
Definition ex_same (sr sr' : list expr) (L : list reg) : bool :=
  forallb (fun k => existsb (fun x : reg => Nat.eqb (ridx x) k) L || expr_eqb (nth k sr (ELit 0)) (nth k sr' (ELit 0))) (seq 1 31).
Lemma ex_agree_refl : forall E sr sr' regs R' (L : list reg),
  regs_ok E sr regs -> regs_ok E sr' R' -> ex_same sr sr' L = true -> regs_agree (fun r => In r L) regs R'.
Proof.
  intros E sr sr' regs R' L HR HR' HS r Hr. rewrite (reg_val _ _ _ r HR'), (reg_val _ _ _ r HR). f_equal.
  unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|].
  unfold ex_same in HS. rewrite forallb_forall in HS.
  assert (Hk : In (ridx r) (seq 1 31)).
  { apply in_seq. pose proof (ridx_range r). assert (ridx r <> 0)%nat; [|lia].
    intro E0. unfold bv_eqb in Hr0. apply Z.eqb_neq in Hr0. apply Hr0. unfold ridx in E0.
    pose proof (bv_unsigned_in_range _ r) as [R0 _]. change (bv_unsigned (0 : reg)) with 0%Z. lia. }
  specialize (HS _ Hk). apply orb_true_iff in HS. destruct HS as [HS|HS].
  - exfalso. apply Hr. apply existsb_exists in HS. destruct HS as (x & Hx & Ex). apply Nat.eqb_eq in Ex. apply ridx_inj in Ex. subst x. exact Hx.
  - symmetry. apply expr_eqb_eq. exact HS.
Qed.
Ltac ex_agree HR HR' := apply (ex_agree_refl _ _ _ _ _ _ HR HR'); vm_compute; reflexivity.

(* [comment removed for export] *)
Ltac ex_agree_cases HR HR' :=
  let r := fresh "r" in let Hr := fresh "Hr" in let Hr0 := fresh "Hr0" in let n := fresh "n" in let Hlt := fresh "Hlt" in
  intros r Hr; rewrite (reg_val _ _ _ r HR'), (reg_val _ _ _ r HR); f_equal;
  unfold sr_get; destruct (bv_eqb r 0) eqn:Hr0; [reflexivity|];
  pose proof (ridx_range r) as Hlt; rewrite <- (ridx_roundtrip r) in Hr |- *;
  set (n := ridx r) in *; clearbody n;
  do 32 (destruct n as [|n];
         [ first [ vm_compute; reflexivity
                 | exfalso; apply Hr; cbn [In]; repeat (first [ left; apply bv_eq; reflexivity | right ]) ] |]);
  exfalso; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section Session.
Context {fx : FPState}.
Variable segs : list Segment.

Lemma ex_cont_sound : forall fuel stops scr pc sr log kn nx ss' scs scr' E m rom R ms0,
  sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (ss', scs, scr') ->
  regs_ok E sr R -> log_flat E log -> know_ok segs E m kn -> scs_denot segs m E scs ->
  msteps segs ms0 (mkst R (Z_to_bv 64 pc) (mem_denot E m log) rom) ->
  exists R', regs_ok E (s_regs ss') R' /\ log_flat E (s_log ss')
             /\ msteps segs ms0 (mkst R' (Z_to_bv 64 (s_pc ss')) (mem_denot E m (s_log ss')) rom).
Proof.
  intros fuel stops scr pc sr log kn nx ss' scs scr' E m rom R ms0 Hex HR Hlf HK Hsc Hms.
  destruct (sym_exec_ex segs fuel true stops scr (SS pc sr log kn nx) [] ss' scs scr' E m rom
              (mkst R (Z_to_bv 64 pc) (mem_denot E m log) rom) Hex Hsc) as (R' & HR' & Hlf' & Hms').
  { exists R. cbn [s_pc s_log s_regs s_know]. split; [reflexivity|]. split; [exact HR|]. split; [exact Hlf | exact HK]. }
  exists R'. split; [exact HR'|]. split; [exact Hlf'|]. eapply msteps_trans; [exact Hms | exact Hms'].
Qed.

Lemma ex_msteps_snoc : forall ms0 ms ms', msteps segs ms0 ms -> ms_svc_pending ms = None ->
  RiscvSemantics.step segs ms = MachineOk ms' -> msteps segs ms0 ms'.
Proof. intros ms0 ms ms' H Hs Hst. eapply msteps_trans; [exact H | apply msteps_one; assumption]. Qed.
End Session.

(* [comment removed for export] *)
Ltac ex_open HR HK Hms Hlf :=
  lazymatch type of HR with
  | regs_ok ?E _ ?regs =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base _ =>
      lazymatch goal with
      | |- context [@mkst ?fx regs (Z_to_bv 64 ?pc) base ?rom] =>
          assert (Hms : msteps segs (@mkst fx regs (Z_to_bv 64 pc) base rom) (@mkst fx regs (Z_to_bv 64 pc) (mem_denot E base []) rom)) by (apply mst_refl);
          assert (Hlf : log_flat E []) by exact I
      end
    end
  end.

(* [comment removed for export] *)
Ltac ex_cont fuel stops scr HR Hlf HK Hms :=
  lazymatch type of HR with
  | regs_ok ?E ?sr ?R =>
    lazymatch type of HK with
    | know_ok ?segs _ ?base ?kn =>
      lazymatch type of Hms with
      | msteps _ ?ms0 (@mkst ?fxk R (Z_to_bv 64 ?pc) (mem_denot _ _ ?log) ?rom) =>
          let nx := ex_nx E in
          let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr log kn nx) []) in
          lazymatch r with
          | (?ss', ?scs, ?scr') =>
              let Hsc := fresh "Hsc" in let R' := fresh "R" in let HR' := fresh "HR" in let Hlf' := fresh "Hlf" in let Hms' := fresh "Hms" in
              let Hex := fresh "Hex" in
              assert (Hex : sym_exec segs fuel true stops scr (SS pc sr log kn nx) [] = (ss', scs, scr')) by (vm_cast_no_check (eq_refl (ss', scs, scr')));
              assert (Hsc : scs_denot segs base E scs);
              [ split_scs; lazymatch E with ex_envL _ ?r0 _ => ex_sc r0 end
              | destruct (@ex_cont_sound fxk segs fuel stops scr pc sr log kn nx ss' scs scr' E base rom R ms0
                            Hex HR Hlf HK Hsc Hms) as (R' & HR' & Hlf' & Hms');
                clear Hex Hsc Hlf Hms; (let HRo := fresh "HRo" in rename HR into HRo); rename HR' into HR; rename Hlf' into Hlf; rename Hms' into Hms;
                lazymatch ss' with
                | SS ?pc' ?sr' ?log' _ _ =>
                    change (regs_ok E sr' R') in HR; change (log_flat E log') in Hlf;
                    change (msteps segs ms0 (@mkst fxk R' (Z_to_bv 64 pc') (mem_denot E base log') rom)) in Hms
                end ]
          end
      end
    end
  end.

(* [comment removed for export] *)
Ltac ex_gc HR :=
  repeat match goal with H : regs_ok _ _ _ |- _ => lazymatch H with HR => fail | _ => clear H end end;
  repeat match goal with R : bvmap 5 word |- _ => clear R end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Section FBridge.
Variable segs : list Segment.

(* [comment removed for export] *)
Lemma ex_fsd_sound : forall (fx : FPState) E m rom R pc sr log ms0 w rs1 rs2 (imm : bv 12) (v : nat),
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 pc) (mem_denot E m log) rom) -> regs_ok E sr R -> log_flat E log ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FStore FMT_D rs1 rs2 imm, 4%Z) ->
  ev E v = reg_get (@fp_regs fx) rs2 ->
  flat E (to_saddr (sr_get sr rs1) (bv_signed imm)) 8 ->
  store_ok segs m (adenot E (to_saddr (sr_get sr rs1) (bv_signed imm))) 8 = true ->
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 (pc + 4)) (mem_denot E m (SE (to_saddr (sr_get sr rs1) (bv_signed imm)) 8 (EVar v) :: log)) rom)
  /\ log_flat E (SE (to_saddr (sr_get sr rs1) (bv_signed imm)) 8 (EVar v) :: log).
Proof.
  intros fx E m rom R pc sr log ms0 w rs1 rs2 imm v Hms HR Hlf Hf He Hd Hv Hfl Hok. split.
  - eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
    rewrite (fp_step_fsd fx segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rs1 rs2 imm
               (adenot E (to_saddr (sr_get sr rs1) (bv_signed imm))) Hf He Hd).
    + rewrite zbv_addi. cbn [mem_denot edenot]. rewrite Hv. reflexivity.
    + rewrite to_saddr_denot, <- (reg_val _ _ _ rs1 HR). reflexivity.
    + eapply store_ok_mono; [apply mem_denot_grows | exact Hok].
  - cbn [log_flat]. split; [lia|]. split; [exact Hfl | exact Hlf].
Qed.

(* [comment removed for export] *)
Lemma ex_fld_sound : forall (fx : FPState) E m rom R pc sr log kn ms0 w rd rs (imm : bv 12) rb rk (v : expr) scs hints hints',
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 pc) (mem_denot E m log) rom) -> regs_ok E sr R -> log_flat E log -> know_ok segs E m kn ->
  fetch_word segs (Z_to_bv 64 pc) = Some w -> is_ecall w = false -> decode_any w = Some (FLoad FMT_D rd rs imm, 4%Z) ->
  to_saddr (sr_get sr rs) (bv_signed imm) = SA rb rk ->
  log_lookup kn log rb rk 8 false hints [] = LHit v scs hints' ->
  scs_denot segs m E scs -> flat E (SA rb rk) 8 ->
  exists bs, length bs = 8%nat /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v /\
    msteps segs ms0 (@mkst (mkFP (bvmap_set rd (bv_extract 0 64 (le_bytes_to_word bs)) (@fp_regs fx)) (@fp_csr fx)) R (Z_to_bv 64 (pc + 4)) (mem_denot E m log) rom).
Proof.
  intros fx E m rom R pc sr log kn ms0 w rd rs imm rb rk v scs hints hints' Hms HR Hlf HK Hf He Hd Hsa Hlk Hsc Hfl.
  pose proof (log_lookup_sound segs E m kn log rb rk 8 false hints [] HK Hlf ltac:(lia) ltac:(lia)) as L.
  rewrite Hlk in L. destruct (L Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  exists bs. split; [exact Hlen|]. split; [exact Hval|].
  eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
  rewrite (fp_step_fld fx segs R (Z_to_bv 64 pc) (mem_denot E m log) rom w rd rs imm (adenot E (SA rb rk)) bs Hf He Hd).
  - rewrite zbv_addi. reflexivity.
  - rewrite <- Hsa, to_saddr_denot, <- (reg_val _ _ _ rs HR). reflexivity.
  - exact Hrd.
Qed.

(* [comment removed for export] *)
Lemma ex_fpure_sound : forall (fx fx' : FPState) rom R pc (M : word -> option byte) ms0,
  msteps segs ms0 (@mkst fx R (Z_to_bv 64 pc) M rom) ->
  RiscvSemantics.step segs (@mkst fx R (Z_to_bv 64 pc) M rom) = MachineOk (@mkst fx' R (v_addi (Z_to_bv 64 pc) 4) M rom) ->
  msteps segs ms0 (@mkst fx' R (Z_to_bv 64 (pc + 4)) M rom).
Proof.
  intros fx fx' rom R pc M ms0 Hms Hst. eapply (ex_msteps_snoc segs); [exact Hms | reflexivity |].
  rewrite Hst, zbv_addi. reflexivity.
Qed.
End FBridge.

(* [comment removed for export] *)
Ltac ex_fetch segs pc F D :=
  let f := eval vm_compute in (fetch_word segs (Z_to_bv 64 pc)) in
  lazymatch f with
  | Some ?w =>
      assert (F : fetch_word segs (Z_to_bv 64 pc) = Some w) by (vm_cast_no_check (eq_refl (Some w)));
      let d := eval vm_compute in (decode_any w) in
      assert (D : decode_any w = d) by (vm_cast_no_check (eq_refl d))
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_in_regions (regions : list (expr * Z * Z)) (log : list sentry) : bool :=
  forallb (fun e => match e with
                    | SE (SA b off) w _ =>
                        existsb (fun r => match r with (rb, lo, hi) => expr_eqb b rb && (lo <=? off)%Z && (off + Z.of_nat w <=? hi)%Z end) regions
                    end) log.

Lemma ex_changed : forall E base log regions, log_flat E log -> ex_in_regions regions log = true ->
  forall a : word, mem_denot E base log a <> base a ->
  Exists (fun r => match r with (rb, lo, hi) => (bv_unsigned (edenot E rb) + lo <= bv_unsigned a < bv_unsigned (edenot E rb) + hi)%Z end) regions.
Proof.
  intros E base log regions. induction log as [|[[b off] w v] rest IH]; intros Hlf Hreg a Hne; [exfalso; apply Hne; reflexivity|].
  cbn [log_flat] in Hlf. destruct Hlf as (Hw8 & Hfl & Hlf'). cbn [ex_in_regions forallb] in Hreg. apply andb_true_iff in Hreg as [Hr1 Hr2].
  cbn [mem_denot] in Hne.
  pose proof (flat_u E (SA b off) (Z.of_nat w) Hfl) as Hu. unfold flat, estart in Hfl, Hu. cbn [a_base a_off] in Hfl, Hu.
  destruct Hfl as (F1 & F2 & F3 & F4).
  destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned (edenot E b) + off)) as [Hlo|Hlo];
    [| destruct (Z_lt_ge_dec (bv_unsigned a) (bv_unsigned (edenot E b) + off + Z.of_nat w)) as [Hhi|Hhi]].
  - apply IH; [exact Hlf' | exact Hr2 |]. intro X. apply Hne. rewrite <- X.
    apply wbytes_outside; rewrite length_N_to_le_bytes, Hu; [lia | left; lia].
  - apply existsb_exists in Hr1. destruct Hr1 as ([[rb lo] hi] & Hin & Hb).
    apply andb_true_iff in Hb as [Hb Hb3]. apply andb_true_iff in Hb as [Hb1 Hb2].
    apply expr_eqb_eq in Hb1. subst rb. apply Z.leb_le in Hb2, Hb3.
    apply Exists_exists. exists (b, lo, hi). split; [exact Hin | lia].
  - apply IH; [exact Hlf' | exact Hr2 |]. intro X. apply Hne. rewrite <- X.
    apply wbytes_outside; rewrite length_N_to_le_bytes, Hu; [lia | right; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac ex_flat regs :=
  ex_unfoldE; unfold flat, estart; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
  repeat match goal with H : getr regs _ = Z_to_bv 64 _ |- _ => rewrite H end;
  rewrite ?ex_ptr_val; rewrite ?u_Z2bv by lia; lia.

(* [comment removed for export] *)
Ltac ex_fsd vv HR Hlf Hms SOK :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst ?fxk ?R (Z_to_bv 64 ?pc) (mem_denot ?E ?m ?log) ?rom) =>
    lazymatch type of HR with
    | regs_ok _ ?sr _ =>
      lazymatch E with
      | ex_envL _ ?r0 _ =>
        let F := fresh "F" in let D := fresh "D" in let Hms' := fresh "Hms" in let Hlf' := fresh "Hlf" in
        ex_fetch segs pc F D;
        edestruct (ex_fsd_sound segs fxk E m rom R pc sr log ms0) with (v := vv) as [Hms' Hlf'];
        [ exact Hms | exact HR | exact Hlf | exact F | reflexivity | exact D
        | cbn [ev ex_envL vals_ev map app ex_regs_list nth Nat.add]; first [reflexivity | apply zbv_self]
        | vm_compute to_saddr; ex_flat r0
        | vm_compute to_saddr; unfold adenot; cbn [a_base a_off edenot ev ex_envL vals_ev map app ex_regs_list nth Nat.add];
          repeat match goal with H : getr r0 _ = Z_to_bv 64 _ |- _ => rewrite H end; rewrite ?ex_ptr_val, ?zbv_addi;
          eapply store_ok_sub; [ | exact SOK | | ]; rewrite ?u_Z2bv by lia; ex_natlia
        | clear F D Hms Hlf; rename Hms' into Hms; rename Hlf' into Hlf ]
      end
    end
  end.

(* [comment removed for export] *)
Ltac ex_fld HR Hlf HK Hms bs Hbs Hv :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst ?fxk ?R (Z_to_bv 64 ?pc) (mem_denot ?E ?m ?log) ?rom) =>
    lazymatch type of HR with
    | regs_ok _ ?sr _ =>
      lazymatch type of HK with
      | know_ok _ _ _ ?kn =>
        lazymatch E with
        | ex_envL _ ?r0 _ =>
          let F := fresh "F" in let D := fresh "D" in let Hms' := fresh "Hms" in
          ex_fetch segs pc F D;
          lazymatch type of D with
          | decode_any _ = Some (FLoad FMT_D ?rd ?rs ?imm, _) =>
              let sa := eval vm_compute in (to_saddr (sr_get sr rs) (bv_signed imm)) in
              lazymatch sa with
              | SA ?rb ?rk =>
                  let lk := eval vm_compute in (log_lookup kn log rb rk 8 false [] []) in
                  lazymatch lk with
                  | LHit ?v ?scs ?hints' =>
                      destruct (ex_fld_sound segs fxk E m rom R pc sr log kn ms0 _ rd rs imm rb rk v scs [] hints' Hms HR Hlf HK F (eq_refl _) D)
                        as (bs & Hbs & Hv & Hms');
                      [ vm_cast_no_check (eq_refl sa) | vm_cast_no_check (eq_refl lk) | split_scs; ex_sc r0 | ex_flat r0
                      | clear F D Hms; rename Hms' into Hms ]
                  end
              end
          end
        end
      end
    end
  end.

(* [comment removed for export] *)
Ltac ex_fpure Hms fx' tac :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst ?fxk ?R (Z_to_bv 64 ?pc) ?M ?rom) =>
      let F := fresh "F" in let D := fresh "D" in let ST := fresh "ST" in let Hms' := fresh "Hms" in
      ex_fetch segs pc F D;
      assert (ST : RiscvSemantics.step segs (@mkst fxk R (Z_to_bv 64 pc) M rom) = MachineOk (@mkst fx' R (v_addi (Z_to_bv 64 pc) 4) M rom)) by (tac F D);
      pose proof (ex_fpure_sound segs fxk fx' rom R pc M ms0 Hms ST) as Hms';
      clear F D ST Hms; rename Hms' into Hms
  end.
(* [comment removed for export] *)
Ltac ex_fmv_d_x Hms :=
  lazymatch type of Hms with
  | msteps ?segs ?ms0 (@mkst ?fxk ?R (Z_to_bv 64 ?pc) ?M ?rom) =>
      let d := eval vm_compute in (match fetch_word segs (Z_to_bv 64 pc) with Some w => decode_any w | None => None end) in
      lazymatch d with
      | Some (Fmv FMV_F_X FMT_D ?rd ?rs1, _) =>
          ex_fpure Hms (mkFP (bvmap_set rd (getr R rs1) (@fp_regs fxk)) (@fp_csr fxk)) ltac:(fun F D => eapply fp_step_fmv_d_x; [exact F | reflexivity | exact D])
      end
  end.

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ex_changed1 : forall E base log (rb : expr) (lo hi b : Z), log_flat E log -> ex_in_regions [(rb, lo, hi)] log = true ->
  edenot E rb = Z_to_bv 64 b -> (0 <= b < 2 ^ 64)%Z ->
  forall a : word, mem_denot E base log a <> base a -> (b + lo <= bv_unsigned a < b + hi)%Z.
Proof.
  intros E base log rb lo hi b Hlf Hreg Hb Rb a Hne. pose proof (ex_changed E base log _ Hlf Hreg a Hne) as X.
  inversion X as [r l H|r l H]; subst; [| inversion H]. rewrite Hb, u_Z2bv in H by lia. exact H.
Qed.
Lemma ex_changed2 : forall E base log (rb1 rb2 : expr) (lo1 hi1 b1 lo2 hi2 b2 : Z), log_flat E log ->
  ex_in_regions [(rb1, lo1, hi1); (rb2, lo2, hi2)] log = true ->
  edenot E rb1 = Z_to_bv 64 b1 -> (0 <= b1 < 2 ^ 64)%Z -> edenot E rb2 = Z_to_bv 64 b2 -> (0 <= b2 < 2 ^ 64)%Z ->
  forall a : word, mem_denot E base log a <> base a -> (b1 + lo1 <= bv_unsigned a < b1 + hi1)%Z \/ (b2 + lo2 <= bv_unsigned a < b2 + hi2)%Z.
Proof.
  intros E base log rb1 rb2 lo1 hi1 b1 lo2 hi2 b2 Hlf Hreg Hb1 R1 Hb2 R2 a Hne. pose proof (ex_changed E base log _ Hlf Hreg a Hne) as X.
  inversion X as [r l H|r l H]; subst; [left; rewrite Hb1, u_Z2bv in H by lia; exact H|].
  inversion H as [r' l' H'|r' l' H']; subst; [right; rewrite Hb2, u_Z2bv in H' by lia; exact H' | inversion H'].
Qed.

(* [comment removed for export] *)
Lemma ex_cell_log : forall segs E m kn log rb rk (n : nat) (v : expr) scs hints',
  know_ok segs E m kn -> log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
  log_lookup kn log rb rk n false [] [] = LHit v scs hints' -> scs_denot segs m E scs -> flat E (SA rb rk) (Z.of_nat n) ->
  exists bs, rdn segs (mem_denot E m log) (adenot E (SA rb rk)) n = Some bs /\ length bs = n /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros segs E m kn log rb rk n v scs hints' HK Hlf H1 H8 Hlk Hsc Hfl.
  pose proof (log_lookup_sound segs E m kn log rb rk n false [] [] HK Hlf H1 H8) as L. rewrite Hlk in L. exact (L Hsc Hfl).
Qed.

(* [comment removed for export] *)
Definition ex_lookup (segs : list Segment) (kn : list kentry) (log : list sentry) (rb : expr) (rk : Z) (n : nat) : option (expr * list sidecond) :=
  match log_lookup kn log rb rk n false [] [] with
  | LHit v scs _ => Some (v, scs)
  | LMiss lscs lh => match know_lookup segs kn rb rk n false lh lscs with LHit v scs _ => Some (v, scs) | _ => None end
  | LStuck => None
  end.
Lemma ex_lookup_sound : forall {fx : FPState} segs E m kn log rb rk (n : nat) (v : expr) scs,
  know_ok segs E m kn -> log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
  ex_lookup segs kn log rb rk n = Some (v, scs) -> scs_denot segs m E scs -> flat E (SA rb rk) (Z.of_nat n) ->
  exists bs, rdn segs (mem_denot E m log) (adenot E (SA rb rk)) n = Some bs /\ length bs = n /\ Z_to_bv 64 (bytes_le_to_Z bs) = edenot E v.
Proof.
  intros fx segs E m kn log rb rk n v scs HK Hlf H1 H8 Hlk Hsc Hfl. unfold ex_lookup in Hlk.
  pose proof (log_lookup_sound segs E m kn log rb rk n false [] [] HK Hlf H1 H8) as L.
  destruct (log_lookup kn log rb rk n false [] []) as [v1 s1 h1|lscs lh|]; [ | | discriminate].
  - injection Hlk as <- <-. exact (L Hsc Hfl).
  - pose proof (know_lookup_sound segs E m kn rb rk n false lh lscs HK H1 H8) as Kn.
    pose proof (know_lookup_acc segs kn rb rk n false lh lscs) as Kacc.
    destruct (know_lookup segs kn rb rk n false lh lscs) as [v2 s2 h2| |]; [ | discriminate | discriminate].
    injection Hlk as <- <-. destruct Kacc as [pre ->].
    assert (Hl : scs_denot segs m E lscs) by (apply scs_denot_app in Hsc as [_ H]; exact H).
    destruct (Kn Hsc Hfl) as (bs & Hrd & Hlen & Hval). exists bs. split; [rewrite (L Hl Hfl); exact Hrd|]. split; [exact Hlen | exact Hval].
Qed.

(* [comment removed for export] *)
Lemma ex_cell_Z : forall {fx : FPState} segs E m kn log rb rk (n : nat) (v : expr) scs scs0 (a z : Z),
  know_ok segs E m kn -> log_flat E log -> (1 <= n)%nat -> (n <= 8)%nat ->
  ex_lookup segs kn log rb rk n = Some (v, scs) -> flat_sc kn (SA rb rk) n ++ scs = scs0 -> scs_denot segs m E scs0 ->
  adenot E (SA rb rk) = Z_to_bv 64 a -> edenot E v = Z_to_bv 64 z -> (0 <= z < 2 ^ (8 * Z.of_nat n))%Z ->
  rdn segs (mem_denot E m log) (Z_to_bv 64 a) n = Some (Z_to_le_bytes n z).
Proof.
  intros fx segs E m kn log rb rk n v scs scs0 a z HK Hlf H1 H8 Hlk Es Hsc Ha Hv Hz. subst scs0.
  apply (flat_sc_sound segs E m kn (SA rb rk) n scs HK H1 H8) in Hsc as [Hfl Hsc].
  destruct (ex_lookup_sound segs E m kn log rb rk n v scs HK Hlf H1 H8 Hlk Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  rewrite <- Ha, Hrd. f_equal.
  pose proof (SX2S.bytes_le_to_Z_bound bs) as B. rewrite Hlen in B.
  assert (P : (2 ^ (8 * Z.of_nat n) <= 2 ^ 64)%Z) by (apply Z.pow_le_mono_r; lia).
  rewrite Hv in Hval. apply (f_equal bv_unsigned) in Hval. rewrite !u_small in Hval by lia.
  rewrite <- Hval, <- Hlen. symmetry. apply Z_to_le_bytes_lez.
Qed.
Lemma ex_cell_w : forall {fx : FPState} segs E m kn log rb rk (v : expr) scs scs0 (a : Z) (x : word),
  know_ok segs E m kn -> log_flat E log ->
  ex_lookup segs kn log rb rk 8 = Some (v, scs) -> flat_sc kn (SA rb rk) 8 ++ scs = scs0 -> scs_denot segs m E scs0 ->
  adenot E (SA rb rk) = Z_to_bv 64 a -> edenot E v = x ->
  rdn segs (mem_denot E m log) (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 x).
Proof.
  intros fx segs E m kn log rb rk v scs scs0 a x HK Hlf Hlk Es Hsc Ha Hv. subst scs0.
  apply (flat_sc_sound segs E m kn (SA rb rk) 8%nat scs HK ltac:(lia) ltac:(lia)) in Hsc as [Hfl Hsc].
  destruct (ex_lookup_sound segs E m kn log rb rk 8 v scs HK Hlf ltac:(lia) ltac:(lia) Hlk Hsc Hfl) as (bs & Hrd & Hlen & Hval).
  rewrite <- Ha, Hrd. f_equal. unfold word_to_le_bytes.
  pose proof (SX2S.bytes_le_to_Z_bound bs) as B. rewrite Hlen in B. change (8 * Z.of_nat 8)%Z with 64%Z in B.
  rewrite <- Hv, <- Hval, u_small by lia. rewrite <- Hlen. symmetry. apply Z_to_le_bytes_lez.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ex_in_region1 (regions : list (expr * Z * Z)) (b : expr) (k n : Z) : bool :=
  existsb (fun r => match r with (rb, lo, hi) => expr_eqb b rb && (lo <=? k)%Z && (k + n <=? hi)%Z end) regions.
Definition ex_kn_keep1 (regions : list (expr * Z * Z)) (K : kentry) : list kentry :=
  match K with
  | KWord (SA b k) w _ => if ex_in_region1 regions b k (Z.of_nat w) then [K] else []
  | KZero (SA b k) (ELit l) => if ((0 <=? l)%Z && (l <? 2 ^ 64)%Z && ex_in_region1 regions b k l)%bool then [K] else []
  | KWr (SA b k) n => if ex_in_region1 regions b k n then [K] else []
  | KAlign _ _ | KRange _ _ _ | KDisj _ _ _ _ => [K]
  | _ => []
  end.
Definition ex_kn_keep (regions : list (expr * Z * Z)) (kn : list kentry) : list kentry := flat_map (ex_kn_keep1 regions) kn.

(* [comment removed for export] *)
Definition ex_expr_dead (dead : list nat) (e : expr) : bool := match e with EVar i => existsb (Nat.eqb i) dead | _ => false end.
Definition ex_kn_gc1 (dead : list nat) (K : kentry) : bool :=
  match K with
  | KAlign e _ | KRange e _ _ => negb (ex_expr_dead dead e)
  | KDisj (SA b1 _) _ (SA b2 _) _ => negb (ex_expr_dead dead b1 || ex_expr_dead dead b2)
  | _ => true
  end.
Definition ex_kn_keepD (dead : list nat) (regions : list (expr * Z * Z)) (kn : list kentry) : list kentry :=
  List.filter (ex_kn_gc1 dead) (ex_kn_keep regions kn).

Definition ex_region_kept (E : env) (M M' : word -> option byte) (r : expr * Z * Z) : Prop :=
  match r with (rb, lo, hi) =>
    forall x : word, (bv_unsigned (edenot E rb) + lo <= bv_unsigned x < bv_unsigned (edenot E rb) + hi)%Z -> M' x = M x end.

Lemma ex_in_region1_sound : forall E M M' regions b k n, Forall (ex_region_kept E M M') regions -> ex_in_region1 regions b k n = true ->
  forall x : word, (bv_unsigned (edenot E b) + k <= bv_unsigned x < bv_unsigned (edenot E b) + k + n)%Z -> M' x = M x.
Proof.
  intros E M M' regions b k n HF Hin x Hx. unfold ex_in_region1 in Hin. apply existsb_exists in Hin. destruct Hin as ([[rb lo] hi] & Hr & Hb).
  apply andb_true_iff in Hb as [Hb H3]. apply andb_true_iff in Hb as [H1 H2]. apply expr_eqb_eq in H1. subst rb.
  apply Z.leb_le in H2, H3. rewrite Forall_forall in HF. apply (HF _ Hr). lia.
Qed.

Lemma ex_know_keep : forall segs E M M' kn regions,
  know_ok segs E M kn -> Forall (ex_region_kept E M M') regions -> know_ok segs E M' (ex_kn_keep regions kn).
Proof.
  intros segs E M M' kn regions HK HF. unfold know_ok, ex_kn_keep. apply Forall_forall. intros K' HinF.
  apply in_flat_map in HinF as (K & Hin & Hb). pose proof (proj1 (Forall_forall _ _) HK K Hin) as HKK.
  destruct K as [[b k] w v|[b k] len|[b k] len bk|lo hi|e m|e lo hi|[b k] n|a1 n1 a2 n2]; cbn [ex_kn_keep1] in Hb;
    try (destruct Hb as [<-|[]]; exact HKK); try (destruct Hb; fail).
  - destruct (ex_in_region1 regions b k (Z.of_nat w)) eqn:Hr; [|destruct Hb]. destruct Hb as [<-|[]].
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hw & Hf & Hrd). split; [exact Hw|]. split; [exact Hf|].
    rewrite <- Hrd. apply rdn_agree. intros j Hj. pose proof (flat_u E _ _ Hf) as Hu. destruct Hf as (G1 & G2 & G3 & G4).
    unfold estart in *. cbn [a_base a_off] in *.
    apply (ex_in_region1_sound E M M' regions b k (Z.of_nat w) HF Hr). rewrite u_small by lia. rewrite Hu. lia.
  - destruct len as [l| | | | | | |]; try (destruct Hb; fail).
    destruct ((0 <=? l)%Z && (l <? 2 ^ 64)%Z && ex_in_region1 regions b k l)%bool eqn:Hc; [|destruct Hb]. destruct Hb as [<-|[]].
    apply andb_true_iff in Hc as [Hc Hr]. apply andb_true_iff in Hc as [Hl0 Hl1]. apply Z.leb_le in Hl0. apply Z.ltb_lt in Hl1.
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hz). split; [exact Hf|].
    assert (El : elenZ E (ELit l) = l) by (unfold elenZ; cbn [edenot]; apply u_small; lia). rewrite El in *.
    destruct Hf as (G1 & G2 & G3 & G4). unfold estart in *. cbn [a_base a_off] in *.
    intros i Hi. rewrite (ex_in_region1_sound E M M' regions b k l HF Hr); [apply Hz; exact Hi|]. rewrite u_small by lia. lia.
  - (* [comment removed for export] *)
    destruct (ex_in_region1 regions b k n) eqn:Hr; [|destruct Hb]. destruct Hb as [<-|[]].
    cbn [kentry_ok] in HKK |- *. destruct HKK as (Hf & Hs). split; [exact Hf|].
    intros d j Hd Hj. destruct Hf as (G1 & G2 & G3 & G4). unfold estart in *. cbn [a_base a_off] in *.
    destruct j as [|j]; [reflexivity|].
    apply store_ok_of_all; [rewrite u_small by lia; lia|].
    intros x Hx. rewrite u_small in Hx by lia.
    pose proof (store_ok_all segs M (S j) (Z_to_bv 64 (bv_unsigned (edenot E b) + k + d)) ltac:(rewrite u_small by lia; lia) (Hs d (S j) Hd Hj) x
                  ltac:(rewrite u_small by lia; exact Hx)) as Hw.
    unfold wview in Hw |- *. rewrite (ex_in_region1_sound E M M' regions b k n HF Hr x ltac:(lia)). exact Hw.
Qed.

Lemma ex_know_keepD : forall segs E M M' kn dead regions,
  know_ok segs E M kn -> Forall (ex_region_kept E M M') regions -> know_ok segs E M' (ex_kn_keepD dead regions kn).
Proof.
  intros segs E M M' kn dead regions HK HF. unfold ex_kn_keepD, know_ok. apply Forall_forall. intros K Hin.
  destruct (proj1 (filter_In (ex_kn_gc1 dead) K (ex_kn_keep regions kn)) Hin) as [Hin' _].
  exact (proj1 (Forall_forall _ _) (ex_know_keep segs E M M' kn regions HK HF) K Hin').
Qed.

