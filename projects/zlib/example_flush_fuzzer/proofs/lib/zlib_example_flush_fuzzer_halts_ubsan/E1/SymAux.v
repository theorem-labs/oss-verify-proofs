(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11: comments removed. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan Require Import PropExec CatExec SeqExec StoreOk SymExec.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.E1 Require Import SymEx2Expr SymEx2 SymEx2Tac MemRel.
From OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.zspec.zmodel Require Import ZIface.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Local Open Scope Z_scope.


Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.
Definition sep (a n b m : Z) : Prop := a + n <= b \/ b + m <= a.


Lemma sep_sub : forall a n b m a' n' b' m',
  sep a n b m -> a <= a' -> a' + n' <= a + n -> b <= b' -> b' + m' <= b + m -> sep a' n' b' m'.
Proof. intros a n b m a' n' b' m' [H|H] H1 H2 H3 H4; [left|right]; lia. Qed.

End FXG.
Ltac sep_solve :=
  first [ lia
        | match goal with
          | H : sep _ _ _ _ |- _ =>
              let H' := fresh "Hsep" in pose proof H as H'; unfold sep in H';
              destruct H'; solve [ lia | left; lia | right; lia ]
          end ].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Lemma zaluw_sll_small : forall a k, 0 <= a -> 0 <= k < 32 -> a * 2 ^ k < 2 ^ 31 ->
  zaluw ALU_SLL a k = a * 2 ^ k.
Proof.
  intros a k Ha Hk Hak. unfold zaluw. rewrite zw_sllw, u_zw.
  rewrite (Z.mod_small k 32) by lia.
  assert (0 <= a * 2 ^ k) by (apply Z.mul_nonneg_nonneg; [lia | apply Z.pow_nonneg; lia]).
  unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite (Z.mod_small (a * 2 ^ k + 2 ^ 31)) by (split; [lia|]; change (2 ^ 32) with (2 ^ 31 + 2 ^ 31); lia).
  rewrite Z.mod_small; [lia|]. split; [lia|].
  apply (Z.lt_trans _ (2 ^ 31)); [lia|]. apply Z.pow_lt_mono_r; lia.
Qed.


Lemma zaluw_srl_small : forall a k, 0 <= a < 2 ^ 31 -> 0 <= k < 32 ->
  zaluw ALU_SRL a k = a / 2 ^ k.
Proof.
  intros a k Ha Hk. unfold zaluw. rewrite zw_srlw, u_zw.
  rewrite (Z.mod_small k 32) by lia. rewrite (Z.mod_small a (2 ^ 32)) by lia.
  assert (H0 : 0 <= a / 2 ^ k) by (apply Z.div_pos; [lia | apply Z.pow_pos_nonneg; lia]).
  assert (Hp : 1 <= 2 ^ k) by (change 1 with (2 ^ 0); apply Z.pow_le_mono_r; lia).
  assert (H1 : a / 2 ^ k <= a).
  { apply Z.div_le_upper_bound; [lia|]. nia. }
  unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  rewrite (Z.mod_small (a / 2 ^ k + 2 ^ 31)) by (split; [lia|]; change (2 ^ 32) with (2 ^ 31 + 2 ^ 31); lia).
  rewrite Z.mod_small; lia.
Qed.

Lemma szwrap32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 32 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (32 - 1)) with 2147483648. lia. Qed.

Lemma zaluw_sll_m1 : forall e, 0 <= e < 32 -> zaluw ALU_SLL (-1) e = 2 ^ 64 - 2 ^ e.
Proof.
  intros e He. unfold zaluw. rewrite zw_sllw, u_zw, (Z.mod_small e 32) by lia.
  pose proof (Z.pow_le_mono_r 2 e 31 ltac:(lia) ltac:(lia)). pose proof (Z.pow_pos_nonneg 2 e ltac:(lia) ltac:(lia)).
  rewrite szwrap32_small by (change (2 ^ 31) with 2147483648 in *; lia).
  replace (-1 * 2 ^ e) with (2 ^ 64 - 2 ^ e + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. change (2 ^ 31) with 2147483648 in *. change (2 ^ 64) with 18446744073709551616. lia.
Qed.

Lemma szwrap64_small : forall a, -9223372036854775808 <= a < 9223372036854775808 -> szwrap 64 a = a.
Proof. intros a H. apply szwrap_small; [lia|]. change (2 ^ (64 - 1)) with 9223372036854775808. lia. Qed.

Lemma szwrap64_32_small : forall a, -2147483648 <= a < 2147483648 -> szwrap 64 (szwrap 32 a) = a.
Proof. intros a H. rewrite szwrap32_small by lia. apply szwrap64_small. lia. Qed.

Lemma szwrap32_mod : forall v, (szwrap 32 v) mod 2 ^ 32 = v mod 2 ^ 32.
Proof. intros v. apply szwrap_eqm. lia. Qed.

Lemma szwrap32_u64 : forall a, 0 <= a < 2 ^ 32 ->
  (szwrap 32 a) mod 2 ^ 64 = (if a <? 2 ^ 31 then a else a + 2 ^ 64 - 2 ^ 32).
Proof.
  intros a Ha. unfold szwrap. change (2 ^ (32 - 1)) with (2 ^ 31).
  destruct (Z.ltb_spec a (2 ^ 31)) as [L|L].
  - rewrite (Z.mod_small (a + 2 ^ 31)) by (change (2 ^ 32) with (2 ^ 31 + 2 ^ 31) in *; lia).
    rewrite Z.mod_small; lia.
  - replace (a + 2 ^ 31) with ((a - 2 ^ 31) + 1 * 2 ^ 32) by (change (2 ^ 32) with (2 ^ 31 + 2 ^ 31); lia).
    rewrite Z.mod_add by lia.
    rewrite (Z.mod_small (a - 2 ^ 31)) by (change (2 ^ 32) with (2 ^ 31 + 2 ^ 31) in *; lia).
    replace (a - 2 ^ 31 - 2 ^ 31) with ((a + 2 ^ 64 - 2 ^ 32) + (-1) * 2 ^ 64)
      by (change (2 ^ 32) with (2 ^ 31 + 2 ^ 31); lia).
    rewrite Z.mod_add by lia. apply Z.mod_small.
    change (2 ^ 64) with 18446744073709551616 in *. change (2 ^ 32) with 4294967296 in *.
    change (2 ^ 31) with 2147483648 in *. lia.
Qed.

Lemma zw_neg_mod : forall a, zw (a mod 2 ^ 64) = zw a.
Proof. intros a. apply zw_mod. Qed.



Section WithSegs.
Variable segs : list Segment.

Lemma cell_mod : forall mem a (w : nat) v v',
  cell segs mem a w v -> v' mod 2 ^ (8 * Z.of_nat w) = v mod 2 ^ (8 * Z.of_nat w) -> cell segs mem a w v'.
Proof.
  intros mem a w v v' Hc Hm. unfold cell in *. rewrite Hc. f_equal.
  rewrite <- (SymExec.Z_to_le_bytes_mod w v), <- (SymExec.Z_to_le_bytes_mod w v').
  rewrite Hm. reflexivity.
Qed.

Lemma cells_ext_mod : forall mem P st w n f g,
  cells segs mem P st w n f ->
  (forall i, 0 <= i < n -> g i mod 2 ^ (8 * Z.of_nat w) = f i mod 2 ^ (8 * Z.of_nat w)) ->
  cells segs mem P st w n g.
Proof. intros mem P st w n f g Hc Hfg i Hi. apply (cell_mod mem _ w (f i)); [exact (Hc i Hi) | apply Hfg; exact Hi]. Qed.

Lemma cells_ext : forall mem P st w n f g,
  cells segs mem P st w n f -> (forall i, 0 <= i < n -> g i = f i) -> cells segs mem P st w n g.
Proof. intros mem P st w n f g Hc Hfg i Hi. rewrite (Hfg i Hi). exact (Hc i Hi). Qed.

Lemma cells_snoc : forall mem P st w n f,
  cells segs mem P st w n f -> 0 <= n -> cell segs mem (P + st * n) w (f n) -> cells segs mem P st w (n + 1) f.
Proof.
  intros mem P st w n f Hc Hn Hl i Hi.
  destruct (Z.eq_dec i n) as [->|]; [exact Hl | apply Hc; lia].
Qed.

Lemma cells_nil : forall mem P st w f, cells segs mem P st w 0 f.
Proof. intros mem P st w f i Hi. lia. Qed.






Definition fcells (sp : Z) (m : word -> option byte) (l : list (Z * nat * Z)) : Prop :=
  Forall (fun e : Z * nat * Z => let '(o, w, v) := e in cell segs m (sp + o) w v) l.

Lemma fcells_nil : forall sp m, fcells sp m [].
Proof. intros. apply Forall_nil. Qed.

Lemma fcells_cons : forall sp m o w v l,
  cell segs m (sp + o) w v -> fcells sp m l -> fcells sp m ((o, w, v) :: l).
Proof. intros. apply Forall_cons; assumption. Qed.

Lemma fcells_cons_inv : forall sp m o w v l,
  fcells sp m ((o, w, v) :: l) -> cell segs m (sp + o) w v /\ fcells sp m l.
Proof. intros sp m o w v l H. apply Forall_cons_iff in H. exact H. Qed.

Lemma fcells_get : forall sp m l o w v, fcells sp m l -> In (o, w, v) l -> cell segs m (sp + o) w v.
Proof. intros sp m l o w v H Hin. exact (proj1 (Forall_forall _ _) H (o, w, v) Hin). Qed.

Fixpoint fslots_miss (l : list (Z * nat * Z)) (o' n' : Z) : bool :=
  match l with
  | [] => true
  | (o, w, _) :: l' => ((o + Z.of_nat w <=? o') || (o' + n' <=? o)) && fslots_miss l' o' n'
  end.



Lemma fcells_store_far : forall sp fsz m l (b : Z) bs,
  fcells sp m l -> sep sp fsz b (Z.of_nat (length bs)) ->
  0 <= sp -> sp + fsz <= 2 ^ 64 -> 0 <= b -> b + Z.of_nat (length bs) <= 2 ^ 64 ->
  (forall e, In e l -> let '(o, w, _) := e in 0 <= o /\ o + Z.of_nat w <= fsz) ->
  fcells sp (wbytes m (zw b) bs) l.
Proof.
  intros sp fsz m l b bs H Hsep Hsp Hf Hb0 Hb1 Hin.
  induction l as [|[[o w] v] l IH]; [apply Forall_nil|].
  apply Forall_cons_iff in H as [Hc Hl].
  pose proof (Hin (o, w, v) (or_introl eq_refl)) as Hr. cbv beta iota in Hr. destruct Hr as [Hr1 Hr2].
  apply Forall_cons.
  - apply cell_write_other; [exact Hc | lia | lia | lia | lia |]. destruct Hsep; [left|right]; lia.
  - apply IH; [exact Hl |]. intros e He. apply Hin. right. exact He.
Qed.

End WithSegs.


Lemma lxor_m1_mod64 : forall a, 0 <= a < 2 ^ 64 -> (Z.lxor a (-1)) mod 2 ^ 64 = 2 ^ 64 - 1 - a.
Proof.
  intros a Ha. rewrite Z.lxor_m1_r. unfold Z.lnot.
  replace (Z.pred (- a)) with ((2 ^ 64 - 1 - a) + (-1) * 2 ^ 64) by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

Lemma zmod64_neg : forall d, - 2 ^ 64 <= d < 0 -> d mod 2 ^ 64 = d + 2 ^ 64.
Proof.
  intros d Hd. replace d with ((d + 2 ^ 64) + (-1) * 2 ^ 64) at 1 by lia.
  rewrite Z.mod_add by lia. apply Z.mod_small. lia.
Qed.

End FXG.
Ltac is_zlit t :=
  lazymatch t with
  | Z0 => idtac
  | Zpos ?p => is_plit p
  | Zneg ?p => is_plit p
  end
with is_plit p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_plit q
  | xI ?q => is_plit q
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac zlit_logic :=
  repeat match goal with
  | |- context [Z.lxor ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.lxor a b) in change (Z.lxor a b) with c
  | |- context [Z.land ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.land a b) in change (Z.land a b) with c
  | |- context [Z.lor ?a ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (Z.lor a b) in change (Z.lor a b) with c
  | |- context [?a * 2 ^ ?b] => is_zlit a; is_zlit b; let c := eval vm_compute in (a * 2 ^ b) in change (a * 2 ^ b) with c
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac ltb_tf :=
  repeat (cbn [andb orb negb];
          match goal with
          | |- context [?a <? ?b] =>
              first [ rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia ]
          | |- context [?a <=? ?b] =>
              first [ rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia ]
          | |- context [?a =? ?b] =>
              first [ rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia ]
          end);
  cbn [andb orb negb].
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac zmod_bounds :=
  repeat match goal with
  | |- context [?a mod ?b] =>
      lazymatch goal with
      | H : 0 <= a mod b < b |- _ => fail
      | _ => pose proof (Z.mod_pos_bound a b ltac:(lia))
      end
  end.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.

End FXG.
Ltac zcond_close :=
  rewrite ?szwrap64_32_small by lia; rewrite ?szwrap32_small by lia; rewrite ?szwrap64_small by lia;
  rewrite ?lxor_m1_mod64 by lia;
  repeat (rewrite Z.mod_small by lia);
  ltb_tf; zlit_logic; lia.
Section FXG. Context {fx : OSSVerify.Proofs.zlib.example_flush_fuzzer.lib.zlib_example_flush_fuzzer_halts_ubsan.PropExec.FPState}.


Section Wbytes.
Variable segs : list Segment.

Lemma memcpy_dst_cells : forall (m : word -> option byte) (dst : Z) (bs : list byte),
  0 <= dst -> dst + Z.of_nat (length bs) <= 2 ^ 64 ->
  cells segs (wbytes m (zw dst) bs) dst 1 1 (Z.of_nat (length bs))
        (fun i => bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0))).
Proof.
  intros m dst bs Hd0 Hd1 i Hi. unfold cell.
  pose proof (rdn_wbytes_hit segs bs m (zw dst) ltac:(rewrite u_zw_small by lia; lia)) as H.
  replace (dst + 1 * i) with (dst + Z.of_nat (Z.to_nat i)) by lia.
  rewrite zw_add_nat, (rdn_nth segs _ _ _ _ (Z.to_nat i) H) by lia.
  cbn [Z_to_le_bytes]. rewrite Z_to_bv_bv_unsigned. reflexivity.
Qed.

Lemma memcpy_agree_out : forall (m : word -> option byte) (dst : Z) (bs : list byte),
  0 <= dst -> dst + Z.of_nat (length bs) <= 2 ^ 64 ->
  agree_out [(dst, Z.of_nat (length bs))] m (wbytes m (zw dst) bs).
Proof.
  intros m dst bs Hd0 Hd1.
  apply agree_out_wbytes; [apply agree_out_refl | lia | lia |].
  apply sub_franges_here; lia.
Qed.
End Wbytes.
End FXG.
