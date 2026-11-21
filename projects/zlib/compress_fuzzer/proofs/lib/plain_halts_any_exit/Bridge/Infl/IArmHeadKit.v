(** * Bridge.Infl.IArmHeadKit — helpers shared by IArmHead.v (HEAD, DICTID) and IArmCheck.v
    (CHECK, LENGTH, DONE).

    - facts every arm reads off [icore] ([icore_hd]) and off a [brel] ([brel_rng]);
    - [rt_cbn]: reduce RT's state moves and projections (RT records are small, so [cbn] is
      cheap on them);
    - S5 step lemmas on a state written as [IS.mkW s c r]: one bind past a getter or an
      updater, with the new state again an [IS.mkW].  They are proved by [reflexivity], so the
      setters [IS.wset_*] are only unfolded by conversion inside these proofs, never in a goal. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState InflateArms.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base ZBitsIn Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv IBits.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

Lemma ok_ne_end : RBa.Z_OK <> RBa.Z_STREAM_END.
Proof. discriminate. Qed.

(** The header facts the three arms read. *)
Lemma icore_hd : forall w q, icore w q ->
  RI.q_ret q = RBa.Z_OK
  /\ RI.h_wrap (RI.s_hdr (RI.q_st q)) = 5 /\ RI.h_havedict (RI.s_hdr (RI.q_st q)) = 0
  /\ RI.w_wbits (RI.s_win (RI.q_st q)) = 15
  /\ IS.is_wrap (IS.w_s w) = 5 /\ IS.is_wbits (IS.w_s w) = 15.
Proof.
  intros w q H. unfold icore, iw_rel, ist_core_rel, hdr_rel, win_rel in H. cbv zeta in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  repeat split; congruence.
Qed.

(** Past HEAD: no gzip flags and the Adler-32 still at its start, on both sides. *)
Lemma icore_past_head : forall w q, icore w q -> RI.q_mode q <> RI.M_HEAD ->
  IS.is_flags (IS.w_s w) = 0 /\ IS.is_check (IS.w_s w) = 1
  /\ RI.h_flags (RI.s_hdr (RI.q_st q)) = 0 /\ RI.h_check (RI.s_hdr (RI.q_st q)) = 1.
Proof.
  intros w q H Hm. unfold icore, iw_rel, ist_core_rel, hdr_rel in H. cbv zeta in H.
  repeat match goal with H : _ /\ _ |- _ => destruct H end.
  match goal with H : IS.is_mode (IS.w_s w) <> IS.HEAD -> _ |- _ => destruct H as [Hf Hc] end.
  - intros E. apply Hm. unfold RI.q_mode.
    match goal with Hmd : IS.is_mode (IS.w_s w) = RI.m_val _ |- _ => rewrite E in Hmd; revert Hmd end.
    destruct (RI.h_mode (RI.s_hdr (RI.q_st q))); cbv; intros Hx; first [reflexivity | discriminate Hx].
  - repeat split; congruence.
Qed.

Lemma brel_rng : forall w b, brel w b ->
  0 <= RB.br_bits b <= 39 /\ 0 <= RB.br_hold b < 2 ^ RB.br_bits b
  /\ 0 <= RB.br_next b /\ 0 <= RB.br_have b /\ RB.br_next b + RB.br_have b < 2 ^ 32.
Proof.
  intros w b (Hh & Hbt & Hn & Hv & Hn0 & Hv0 & Hnv & Hbr & Hhr & _).
  rewrite <- Hh, <- Hbt, <- Hn, <- Hv. tauto.
Qed.

Ltac conjs := repeat match goal with |- _ /\ _ => split end.

Lemma inv_eta : forall w q, inv (IS.mkW (IS.w_s w) (IS.w_c w) (IS.w_r w)) q -> inv w q.
Proof. intros [s c r] q H. exact H. Qed.

Ltac rt_cbn :=
  cbn [RI.q_st RI.q_z RI.q_br RI.q_ob RI.q_in RI.q_out RI.q_ret RI.qset_st RI.qset_z RI.qset_br
       RI.qset_ob RI.qset_in RI.qset_out RI.qset_ret RI.qmode RI.qcheck RI.qbad RI.q_mode RI.set_mode
       RI.set_check RI.set_flags RI.set_dmax RI.set_total RI.s_hdr RI.s_win RI.s_cur RI.s_tab RI.s_bld
       RI.h_mode RI.h_last RI.h_wrap RI.h_havedict RI.h_flags RI.h_dmax RI.h_check RI.h_total RI.h_head
       RI.z_tin RI.z_tout RI.z_adler RI.z_dtype RI.zset_adler RI.zset_tout RI.zset_msg RI.o_buf RI.o_put
       RI.o_left RB.br_in RB.br_have RB.br_next RB.br_hold RB.br_bits RB.br_initbits RB.br_dropbits].

(* ------------------------------------------------------------------------- *)
(* S5 steps on an [IS.mkW] state                                             *)
(* ------------------------------------------------------------------------- *)

Lemma ab_gs : forall {A B} (f : IS.inflate_state -> A) (k : A -> IS.AM B) s c r,
  IS.abind (IS.gs f) k (IS.mkW s c r) = k (f s) (IS.mkW s c r).
Proof. reflexivity. Qed.
Lemma ab_gr : forall {A B} (f : IS.iregs -> A) (k : A -> IS.AM B) s c r,
  IS.abind (IS.gr f) k (IS.mkW s c r) = k (f r) (IS.mkW s c r).
Proof. reflexivity. Qed.
Lemma ab_us : forall {B} f (k : unit -> IS.AM B) s c r,
  IS.abind (IS.us f) k (IS.mkW s c r) = k tt (IS.mkW (f s) c r).
Proof. reflexivity. Qed.
Lemma ab_uc : forall {B} f (k : unit -> IS.AM B) s c r,
  IS.abind (IS.uc f) k (IS.mkW s c r) = k tt (IS.mkW s (f c) r).
Proof. reflexivity. Qed.
Lemma ab_ur : forall {B} f (k : unit -> IS.AM B) s c r,
  IS.abind (IS.ur f) k (IS.mkW s c r) = k tt (IS.mkW s c (f r)).
Proof. reflexivity. Qed.
Lemma ab_aret : forall {A B} (a : A) (k : A -> IS.AM B) s c r,
  IS.abind (IS.aret a) k (IS.mkW s c r) = k a (IS.mkW s c r).
Proof. reflexivity. Qed.
Lemma ab_sac : forall {B} v (k : unit -> IS.AM B) s c r,
  IS.abind (IA.set_adler_check v) k (IS.mkW s c r)
  = k tt (IS.mkW (IS.iset_check s v) (IS.icset_adler c v) r).
Proof. reflexivity. Qed.
Lemma ab_mode : forall {B} m (k : unit -> IS.AM B) s c r,
  IS.abind (IA.set_mode m) k (IS.mkW s c r) = k tt (IS.mkW (IS.iset_mode s m) c r).
Proof. reflexivity. Qed.
Lemma ab_hold : forall {B} (k : Z -> IS.AM B) s c r,
  IS.abind IA.HOLD k (IS.mkW s c r) = k (IS.ir_hold r) (IS.mkW s c r).
Proof. reflexivity. Qed.
Lemma ab_init : forall {B} (k : unit -> IS.AM B) s c r,
  IS.abind IA.INITBITS k (IS.mkW s c r) = k tt (IS.mkW s c (IS.irset_bits (IS.irset_hold r 0) 0)).
Proof. reflexivity. Qed.

Lemma ab_assoc : forall {A B C} (m : IS.AM A) (f : A -> IS.AM B) (k : B -> IS.AM C) w,
  IS.abind (IS.abind m f) k w = IS.abind m (fun x => IS.abind (f x) k) w.
Proof. intros. unfold IS.abind. destruct (m w); reflexivity. Qed.

Lemma wbr_mkW : forall s c r b, wbr (IS.mkW s c r) b = IS.mkW s c (setbr r b).
Proof. reflexivity. Qed.

Lemma aleave_mkW : forall {A} s c r, (@IS.aleave A) (IS.mkW s c r) = IS.ALeave (IS.mkW s c r).
Proof. reflexivity. Qed.

(** Step S5 past every bind whose head is a getter or an updater; stops at a macro, a
    branch on a value, or the end. *)
Ltac s5run :=
  repeat (first [ rewrite ab_assoc | rewrite ab_gs | rewrite ab_gr | rewrite ab_us | rewrite ab_uc
                | rewrite ab_ur | rewrite ab_aret | rewrite ab_sac | rewrite ab_mode | rewrite ab_hold
                | rewrite ab_init ]; cbv beta).
