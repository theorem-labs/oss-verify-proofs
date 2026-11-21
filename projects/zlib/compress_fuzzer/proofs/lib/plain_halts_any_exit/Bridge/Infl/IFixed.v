(** * Bridge.Infl.IFixed — pair I7, the fixed tables ([inffixed.h]), by computation.

    S5 stores [lenfix]/[distfix] packed ([InflateState.lenfix_a]/[distfix_a]); RT as
    [Code] triples ([Inflate.lenfix]/[distfix]).  At every nonnegative index S5's entry is
    RT's [code_enc] (past the 512/32 entries both read 0), and both tables have the
    [tview] shape for their roots 9 and 5 (no sub-tables).

    Method: a boolean checker [fixchk] of every [tview] conjunct at one index, run over the
    whole root range by [zall] under [vm_compute], with the soundness lemma [tview_of_chk].
    The 512-entry lists are never unfolded outside the VM. *)

From Stdlib Require Import ZArith List Lia Bool.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require Import ZIface.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Z Require InflateState.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Base Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge Require Import IRelArr IRelInfl.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Bridge.Infl Require Import IInv.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Open Scope Z_scope.

(* ------------------------------------------------------------------------- *)
(* Checkers and their soundness                                              *)
(* ------------------------------------------------------------------------- *)

Definition code_rngb (e : RBa.Code) : bool :=
  (0 <=? RBa.c_op e) && (RBa.c_op e <? 256) && (0 <=? RBa.c_bits e) && (RBa.c_bits e <? 256)
  && (0 <=? RBa.c_val e) && (RBa.c_val e <? 65536).

Lemma code_rngb_sound : forall e, code_rngb e = true -> code_rng e.
Proof.
  intros e H. unfold code_rngb in H.
  rewrite !andb_true_iff, !Z.leb_le, !Z.ltb_lt in H.
  unfold code_rng. lia.
Qed.

(** [tent] as a boolean, on the packed entry. *)
Definition tentb (k : tkind) (e : Z) : bool :=
  let op := IS.code_op e in let val := IS.code_val e in
  match k with
  | KCodes => true
  | KLens => ((Z.land op 16 =? 0) || ((Z.land op 15 <=? 5) && (val + 2 ^ Z.land op 15 <=? 259)))
             && ((op =? 0) || negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0)
                 || (Z.land op 240 =? 0))
  | KDists => negb (op =? 0)
              && ((Z.land op 16 =? 0)
                  || ((Z.land op 15 <=? 13) && (1 <=? val) && (val + 2 ^ Z.land op 15 <=? 32769)))
              && (negb (Z.land op 16 =? 0) || negb (Z.land op 64 =? 0) || (Z.land op 240 =? 0))
  end.

Lemma tentb_sound : forall k e, tentb k e = true -> tent k e.
Proof.
  intros k e H. unfold tentb in H. unfold tent. cbv zeta in *.
  destruct k; [exact I| |];
    repeat first [ rewrite andb_true_iff in H | rewrite orb_true_iff in H
                 | rewrite negb_true_iff in H | rewrite Z.eqb_eq in H | rewrite Z.eqb_neq in H
                 | rewrite Z.leb_le in H ];
    tauto.
Qed.

(** Every [tview] conjunct at index [x], with "no sub-table" in place of the link clause. *)
Definition fixchk (f : Z -> Z) (g : RBa.ztbl) (root : Z) (k : tkind) (x : Z) : bool :=
  (f x =? RBa.code_enc (g x)) && code_rngb (g x) && (IS.code_bits (f x) <=? root)
  && tentb k (f x) && negb (tsub k (IS.code_op (f x))).

Lemma tview_of_chk : forall f g root k,
  1 <= root <= 15 -> zall 0 (2 ^ root) (fixchk f g root k) = true -> tview f g root k.
Proof.
  intros f g root k Hr H. split; [exact Hr|]. intros x Hx.
  pose proof (zall_sound _ _ _ H x Hx) as Hc. unfold fixchk in Hc.
  apply andb_prop in Hc as [Hc Hs]. apply andb_prop in Hc as [Hc Ht].
  apply andb_prop in Hc as [Hc Hb]. apply andb_prop in Hc as [He Hg].
  apply Z.eqb_eq in He. apply Z.leb_le in Hb. apply negb_true_iff in Hs.
  split; [exact He|]. split; [exact (code_rngb_sound _ Hg)|]. split; [exact Hb|].
  split; [exact (tentb_sound _ _ Ht)|].
  intros Hsub. rewrite Hsub in Hs. discriminate.
Qed.

(* ------------------------------------------------------------------------- *)
(* The two tables, by computation                                            *)
(* ------------------------------------------------------------------------- *)

Lemma lenfix_chk :
  zall 0 (2 ^ 9) (fixchk (fun i => arr_get IS.lenfix_a i) RI.lenfix 9 KLens) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma distfix_chk :
  zall 0 (2 ^ 5) (fixchk (fun i => arr_get IS.distfix_a i) RI.distfix 5 KDists) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma tview_lenfix : forall s st,
  tview (IS.code_at s IS.CLenfix) (RI.tbl_of st RI.TRlenfix) 9 KLens.
Proof. intros s st. apply tview_of_chk; [lia|]. exact lenfix_chk. Qed.

Lemma tview_distfix : forall s st,
  tview (IS.code_at s IS.CDistfix) (RI.tbl_of st RI.TRdistfix) 5 KDists.
Proof. intros s st. apply tview_of_chk; [lia|]. exact distfix_chk. Qed.

(** Past the lists' ends both tables read 0 (the "both read 0" check, at every
    index of the next power-of-two block). *)
Lemma lenfix_past_end : forall x, 512 <= x ->
  arr_get IS.lenfix_a x = 0 /\ RBa.code_enc (RI.lenfix x) = 0.
Proof.
  intros x Hx. split.
  - assert (E : zlength IS.lenfix_l = 512) by (vm_compute; reflexivity).
    rewrite arr_get_oob; [vm_compute; reflexivity|]. unfold IS.lenfix_a.
    rewrite arr_len_of_list, E. lia.
  - assert (E : length RI.lenfix_list = 512%nat) by (vm_compute; reflexivity).
    unfold RI.lenfix, RI.tbl_of_list. rewrite nth_overflow; [reflexivity|]. rewrite E. lia.
Qed.

Lemma distfix_past_end : forall x, 32 <= x ->
  arr_get IS.distfix_a x = 0 /\ RBa.code_enc (RI.distfix x) = 0.
Proof.
  intros x Hx. split.
  - assert (E : zlength IS.distfix_l = 32) by (vm_compute; reflexivity).
    rewrite arr_get_oob; [vm_compute; reflexivity|]. unfold IS.distfix_a.
    rewrite arr_len_of_list, E. lia.
  - assert (E : length RI.distfix_list = 32%nat) by (vm_compute; reflexivity).
    unfold RI.distfix, RI.tbl_of_list. rewrite nth_overflow; [reflexivity|]. rewrite E. lia.
Qed.
