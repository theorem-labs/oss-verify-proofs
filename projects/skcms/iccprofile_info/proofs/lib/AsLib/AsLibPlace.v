(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec PropExecFP LibFrame LibDefs.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.AsLib Require Import AsSymExec AsSymExecSound AsSymRun AsSymDrive AsFuzzContract AsLibShadow AsLibDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_t1 := (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker.
(* [comment removed for export] *)
Local Ltac el_dm_pose x k := let v := eval vm_compute in k in lazymatch v with Zpos _ =>   (* [comment removed for export] *)
  lazymatch goal with _ : (x = k * (x / k) + x mod k)%Z |- _ => fail | _ =>
    pose proof (Z.div_mod x k ltac:(vm_compute; discriminate)); pose proof (Z.mod_pos_bound x k ltac:(vm_compute; reflexivity)) end end.
Local Ltac el_dm := repeat match goal with
  | |- context [ (?x / ?k)%Z ] => el_dm_pose x k
  | |- context [ (?x mod ?k)%Z ] => el_dm_pose x k
  | H : ?T |- _ => lazymatch T with (_ <= _)%Z => idtac | (_ < _)%Z => idtac | @eq Z _ _ => idtac | _ /\ _ => idtac | _ \/ _ => idtac end;
      match T with context [ (?x / ?k)%Z ] => el_dm_pose x k | context [ (?x mod ?k)%Z ] => el_dm_pose x k end
  end.
Local Ltac el_lia_core3 := first [ el_t1 | Zify.zify; xlia zchecker ].   (* [comment removed for export] *)
Local Ltac el_lia_core := first [ el_t1 | ((progress el_dm); el_t1) ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Import ListNotations.
Open Scope Z_scope.
Import ASX. Import ASXS.

Definition ZSH : saddr := SA (ELit 0) AS_LOWEND.
Definition ZSHL : Z := AS_HIGHBEG - AS_LOWEND.
Definition ZIMG : saddr := SA (ELit 0) AS_IMGLO.
Definition ZIMGL : Z := AS_IMGHI - AS_IMGLO.

(* [comment removed for export] *)
Lemma app_zone_sh : forall a n, appm a n -> a + n <= AS_LOWEND \/ AS_LOWEND + ZSHL <= a.
Proof. intros a n (H1 & H2 & H3 & H4 & H5). unfold ZSHL. lia. Qed.
Lemma app_zone_img : forall a n, appm a n -> a + n <= AS_IMGLO \/ AS_IMGLO + ZIMGL <= a.
Proof. intros a n (H1 & H2 & H3 & H4 & H5). unfold ZIMGL. lia. Qed.

(* [comment removed for export] *)
Lemma kdisj_lit_intro : forall segs E M e (x : word) off n lo len,
  edenot E e = x ->
  (bv_unsigned x + off + n <= lo \/ lo + len <= bv_unsigned x + off) ->
  kentry_ok segs E M (KDisj (SA e off) n (SA (ELit 0) lo) len).
Proof.
  intros segs E M e x off n lo len He H. cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot].
  rewrite He. assert (Hz : bv_unsigned (Z_to_bv 64 0) = 0) by reflexivity. rewrite Hz. lia.
Qed.

(* [comment removed for export] *)
Lemma kdisj_app_sh : forall segs E M e (x : word) n,
  edenot E e = x -> appm (bv_unsigned x) n -> kentry_ok segs E M (KDisj (SA e 0) n ZSH ZSHL).
Proof.
  intros segs E M e x n He H. unfold ZSH. apply (kdisj_lit_intro segs E M e x 0 n AS_LOWEND ZSHL He).
  pose proof (app_zone_sh _ _ H). lia.
Qed.
Lemma kdisj_app_img : forall segs E M e (x : word) n,
  edenot E e = x -> appm (bv_unsigned x) n -> kentry_ok segs E M (KDisj (SA e 0) n ZIMG ZIMGL).
Proof.
  intros segs E M e x n He H. unfold ZIMG. apply (kdisj_lit_intro segs E M e x 0 n AS_IMGLO ZIMGL He).
  pose proof (app_zone_img _ _ H). lia.
Qed.

(* [comment removed for export] *)
Lemma kdisj_intro2 : forall segs E M e1 (x1 : word) o1 n1 e2 (x2 : word) o2 n2,
  edenot E e1 = x1 -> edenot E e2 = x2 ->
  (bv_unsigned x1 + o1 + n1 <= bv_unsigned x2 + o2 \/ bv_unsigned x2 + o2 + n2 <= bv_unsigned x1 + o1) ->
  kentry_ok segs E M (KDisj (SA e1 o1) n1 (SA e2 o2) n2).
Proof.
  intros segs E M e1 x1 o1 n1 e2 x2 o2 n2 H1 H2 H. cbn [kentry_ok]. unfold estart. cbn [a_base a_off]. rewrite H1, H2. exact H.
Qed.

(* [comment removed for export] *)
Lemma kdisj_below_stack : forall segs E M e (x : word) n esp (sp : word) d ceil,
  edenot E e = x -> edenot E esp = sp -> bv_unsigned x + n <= ceil -> ceil <= bv_unsigned sp - d ->
  kentry_ok segs E M (KDisj (SA e 0) n (SA esp (- d)) d).
Proof. intros. apply (kdisj_intro2 segs E M e x 0 n esp sp (- d) d); auto. lia. Qed.

(* [comment removed for export] *)
Lemma kdisj_stack : forall segs E M e (x : word) n esp (sp : word) o L,
  edenot E e = x -> edenot E esp = sp -> bv_unsigned x + n <= bv_unsigned sp + o ->
  kentry_ok segs E M (KDisj (SA e 0) n (SA esp o) L).
Proof. intros. apply (kdisj_intro2 segs E M e x 0 n esp sp o L); auto. lia. Qed.

(* [comment removed for export] *)
Ltac dlia := repeat match goal with H : _ \/ _ |- _ => destruct H as [H|H] end; lia.
(* [comment removed for export] *)
Ltac clia := repeat match goal with H : _ \/ _ |- _ => clear H end; lia.

(* [comment removed for export] *)
Ltac place_den := lazymatch goal with |- edenot ?Ev _ = _ => try unfold Ev end;
  cbn [edenot ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals];
  first [ eassumption | reflexivity | (symmetry; eassumption) | (cbn; first [eassumption | reflexivity]) ].
Ltac place_app :=
  first [ assumption
        | match goal with H : appm ?a ?m /\ _ |- appm ?a ?m => exact (proj1 H) end
        | match goal with H : (appm ?a ?m /\ _) /\ _ |- appm ?a ?m => exact (proj1 (proj1 H)) end
        | match goal with H : appm ?a ?m |- appm ?b ?k => apply (app_shrink a m b k H); lia end
        | match goal with H : appm ?a ?m /\ _ |- appm ?b ?k => apply (app_shrink a m b k (proj1 H)); lia end
        | match goal with H : (appm ?a ?m /\ _) /\ _ |- appm ?b ?k => apply (app_shrink a m b k (proj1 (proj1 H))); lia end ].

Lemma app_pos : forall a n, appm a n -> 4096 <= a /\ a + n <= 2 ^ 47 /\ 0 <= n.
Proof. intros a n (H1 & H2 & H3 & H4 & H5). lia. Qed.
Ltac app_facts :=
  repeat match goal with
  | H : appm ?a ?n |- _ =>
      lazymatch goal with _ : (4096 <= a)%Z /\ (a + n <= 2 ^ 47)%Z /\ (0 <= n)%Z |- _ => fail | _ => let h := fresh "AFp" in pose proof (app_pos a n H) as h end
  | H : appm ?a ?n /\ _ |- _ =>
      lazymatch goal with _ : (4096 <= a)%Z /\ (a + n <= 2 ^ 47)%Z /\ (0 <= n)%Z |- _ => fail | _ => let h := fresh "AFp" in pose proof (app_pos a n (proj1 H)) as h end
  | H : (appm ?a ?n /\ _) /\ _ |- _ =>
      lazymatch goal with _ : (4096 <= a)%Z /\ (a + n <= 2 ^ 47)%Z /\ (0 <= n)%Z |- _ => fail | _ => let h := fresh "AFp" in pose proof (app_pos a n (proj1 (proj1 H))) as h end
  | H : stackish ?c ?a ?n |- _ =>
      lazymatch goal with _ : (AS_STKLO <= c <= a)%Z /\ (a + n <= 2 ^ 47)%Z |- _ => fail
      | _ => let h := fresh "AFk" in pose proof (H : (AS_STKLO <= c <= a)%Z /\ (a + n <= 2 ^ 47)%Z) as h end
  end.

(* [comment removed for export] *)
Lemma app_sh_lit : forall a n, appm a n -> a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a.
Proof. intros a n (H1 & H2 & H3 & H4 & H5). unfold AS_LOWEND, AS_HIGHBEG in *. lia. Qed.
Lemma app_img_lit : forall a n, appm a n -> a + n <= 0x10000 \/ 0x5fc000 <= a.
Proof. intros a n (H1 & H2 & H3 & H4 & H5). unfold AS_IMGLO, AS_IMGHI in *. lia. Qed.
Ltac app_sh :=
  repeat match goal with
  | H : appm ?a ?n |- _ =>
      lazymatch goal with _ : (a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a)%Z |- _ => fail | _ => let h := fresh "AFs" in pose proof (app_sh_lit a n H) as h end
  | H : appm ?a ?n /\ _ |- _ =>
      lazymatch goal with _ : (a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a)%Z |- _ => fail | _ => let h := fresh "AFs" in pose proof (app_sh_lit a n (proj1 H)) as h end
  | H : (appm ?a ?n /\ _) /\ _ |- _ =>
      lazymatch goal with _ : (a + n <= 0x7fff7000 \/ 0x10007fff8000 <= a)%Z |- _ => fail | _ => let h := fresh "AFs" in pose proof (app_sh_lit a n (proj1 (proj1 H))) as h end
  end.
Ltac app_img :=
  repeat match goal with
  | H : appm ?a ?n |- _ =>
      lazymatch goal with _ : (a + n <= 0x10000 \/ 0x5fc000 <= a)%Z |- _ => fail | _ => let h := fresh "AFi" in pose proof (app_img_lit a n H) as h end
  | H : appm ?a ?n /\ _ |- _ =>
      lazymatch goal with _ : (a + n <= 0x10000 \/ 0x5fc000 <= a)%Z |- _ => fail | _ => let h := fresh "AFi" in pose proof (app_img_lit a n (proj1 H)) as h end
  | H : (appm ?a ?n /\ _) /\ _ |- _ =>
      lazymatch goal with _ : (a + n <= 0x10000 \/ 0x5fc000 <= a)%Z |- _ => fail | _ => let h := fresh "AFi" in pose proof (app_img_lit a n (proj1 (proj1 H))) as h end
  end.

Ltac kdisj_place :=
  lazymatch goal with
  | |- kentry_ok _ _ _ (KDisj (SA _ 0) _ ZSH ZSHL) => eapply kdisj_app_sh; [place_den | app_facts; rewrite ?u_small by lia; place_app]
  | |- kentry_ok _ _ _ (KDisj (SA _ 0) _ ZIMG ZIMGL) => eapply kdisj_app_img; [place_den | app_facts; rewrite ?u_small by lia; place_app]
  | |- kentry_ok _ _ _ (KDisj (SA _ 0) _ (SA (ELit _) _) _) => fail
  | |- kentry_ok _ _ _ (KDisj (SA _ 0) _ (SA _ _) _) =>
      eapply kdisj_stack; [place_den | place_den | app_facts; rewrite ?u_small by lia; lia]
  | |- kentry_ok _ _ _ (KDisj _ _ _ _) =>
      eapply kdisj_intro2; [place_den | place_den | app_facts; rewrite ?u_small by lia; first [lia | (app_sh; lia) | (app_img; lia)]]
  end.

(* [comment removed for export] *)
Lemma krange_add_intro : forall segs E M e1 e2 (x y : word) lo hi,
  edenot E e1 = x -> edenot E e2 = y -> lo <= bv_unsigned x + bv_unsigned y <= hi -> hi < 2 ^ 64 ->
  kentry_ok segs E M (KRange (EAlu ALU_ADD e1 e2) lo hi).
Proof.
  intros segs E M e1 e2 x y lo hi H1 H2 H3 H4. cbn [kentry_ok edenot]. rewrite H1, H2, u_add64.
  pose proof (u64_range x). pose proof (u64_range y). rewrite Z.mod_small by lia. lia.
Qed.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac flat_place :=
  repeat match goal with
  | H : as_data_ok ?c ?mm ?d ?l ?bb |- _ =>
      lazymatch goal with _ : heapish c (bv_unsigned d) l |- _ => fail | _ => pose proof (proj1 (proj2 H)) end
  | H : data_ok ?mm ?d ?l ?bb |- _ =>
      lazymatch goal with _ : (0 <= l < 2 ^ 26)%Z |- _ => fail | _ => pose proof (proj1 H) end
  | H : stackish ?c ?a ?n |- _ =>
      lazymatch goal with _ : (AS_STKLO <= c <= a)%Z /\ (a + n <= 2 ^ 47)%Z |- _ => fail
      | _ => pose proof (H : (AS_STKLO <= c <= a)%Z /\ (a + n <= 2 ^ 47)%Z) end
  | H : heapish ?c ?a ?n |- _ =>
      lazymatch goal with _ : appm a n /\ (a + n <= c)%Z |- _ => fail
      | _ => pose proof (H : appm a n /\ (a + n <= c)%Z) end
  end.
Ltac kn_place := unfold know_ok; flat_place;
  repeat lazymatch goal with
  | |- Forall _ (KRange (EAlu ALU_ADD _ _) _ _ :: _) =>
      constructor; [eapply krange_add_intro; [place_den | place_den | rewrite ?u_small by lia; lia | lia] | ]
  | |- Forall _ (_ :: _) => constructor; [kdisj_place | ]
  | |- Forall _ [] => constructor
  end.

(* [comment removed for export] *)
Ltac plc := first [ lia | place_app | (split; plc) | (app_facts; lia) ].

(* [comment removed for export] *)
Lemma div8_bounds_pl : forall a, 8 * (a / 8) <= a < 8 * (a / 8) + 8.
Proof. intros a. pose proof (Z.div_mod a 8 ltac:(lia)). pose proof (Z.mod_pos_bound a 8 ltac:(lia)). lia. Qed.
Ltac div8_facts :=
  repeat match goal with
  | |- context [ (?x / 8)%Z ] =>
      lazymatch goal with _ : (8 * (x / 8) <= x < 8 * (x / 8) + 8)%Z |- _ => fail | _ => let h := fresh "AFd" in pose proof (div8_bounds_pl x) as h end
  end.
Ltac sc_v2 := rewrite ?u_srl3; rewrite ?u_add64; rewrite ?u_small by clia; mod_small_all; div8_facts; first [(app_sh; dlia) | (app_img; dlia)].
Ltac sc_v2_hook ::= sc_v2.

(* [comment removed for export] *)
Ltac solve_apart ::=
  unfold apart; repeat (apply Forall_cons; [cbn [fst snd]; rewrite ?u_small_frame by lia; first [lia | (app_sh; lia) | (app_img; lia) | idtac] |]);
  try apply Forall_nil.

(* [comment removed for export] *)
Ltac ceil_lo := first [ lia
  | match goal with H : stackish ?c _ _ |- (AS_STKLO <= ?c)%Z => exact (proj1 (proj1 H)) end
  | match goal with H : as_frame _ ?c _ _ _ |- (AS_STKLO <= ?c)%Z => exact (proj1 (proj1 (proj1 H))) end
  | (unfold stackish in *; lia) ].
Ltac fs_app := first [ assumption
  | match goal with H : fs_hdr _ _ _ ?f _ |- appm ?f _ => exact (proj1 (proj2 (proj2 (proj2 H)))) end ].

(* [comment removed for export] *)
Ltac sc_lia ::= first [clia | dlia].
