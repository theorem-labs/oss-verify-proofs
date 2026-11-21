(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.zspec.zmodel Require Import ZIface.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZSysLite ZCall ZCallL.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import ZArr ZArr4.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Import IDefs.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK Require Export IConj INoCast IXfer.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.

Ltac zlia_with_sep L :=
  match goal with
  | S : ctx_sep ?rh ?cx |- _ =>
      let D := fresh "D" in pose proof (L rh cx S) as D;
      cbn [c_u c_p c_q c_n c_ob c_osz c_w] in D; cbv [STATE_SIZE WIN_SIZE FRA ROM_LO_ALL] in D;
      decompose [or] D; clear D; lia
  end.

Ltac zlia_sep_pairs G p q ob u w :=
  match G with
  | context [w] =>
      match G with
      | context [p] => solve [ zlia_with_sep sep_w_p ]
      | context [q] => solve [ zlia_with_sep sep_w_q ]
      | context [ob] => solve [ zlia_with_sep sep_w_ob ]
      | _ => solve [ zlia_with_sep sep_w_rom ]
      end
  | context [p] =>
      match G with
      | context [q] => solve [ zlia_with_sep sep_p_q ]
      | context [ob] => solve [ zlia_with_sep sep_p_ob ]
      | _ => solve [ zlia_with_sep sep_p_rom ]
      end
  | context [ob] =>
      match G with
      | context [q] => solve [ zlia_with_sep sep_ob_q ]
      | context [u] => solve [ zlia_with_sep sep_ob_u ]
      end
  end.

Ltac zlia_sep_targeted :=
  match goal with
  | S : ctx_sep _ (ICX ?u ?p ?q _ ?ob _ ?w _ _ _ _ _) |- ?G => zlia_sep_pairs G p q ob u w
  | S : ctx_sep _ ?cx |- ?G => zlia_sep_pairs G (c_p cx) (c_q cx) (c_ob cx) (c_u cx) (c_w cx)
  end.

Ltac zlia_two G p q ob u w :=
  match G with
  | context [w] =>
      match G with
      | context [p] => solve [ zlia_with_sep sep_w_p ]
      | context [q] => solve [ zlia_with_sep sep_w_q ]
      | context [ob] => solve [ zlia_with_sep sep_w_ob ]
      end
  | context [p] =>
      match G with
      | context [q] => solve [ zlia_with_sep sep_p_q ]
      | context [ob] => solve [ zlia_with_sep sep_p_ob ]
      end
  | context [ob] =>
      match G with
      | context [q] => solve [ zlia_with_sep sep_ob_q ]
      end
  end.

Ltac zlia_sep_guess :=
  match goal with
  | S : ctx_sep _ (ICX ?u ?p ?q _ ?ob _ ?w _ _ _ _ _) |- ?G => zlia_two G p q ob u w
  | S : ctx_sep _ ?cx |- ?G => zlia_two G (c_p cx) (c_q cx) (c_ob cx) (c_u cx) (c_w cx)
  end.

Ltac zlia_zsep1 :=
  match goal with
  | H : ZSEP ?P |- _ => let D := fresh "D" in pose proof (H : P) as D; decompose [or] D; clear D; lia
  end.
Ltac zlia_zsep_all :=
  repeat match goal with H : ZSEP ?P |- _ => change P in H; decompose [or] H; clear H end; lia_std.
Ltac zlia_zsep :=
  repeat match goal with |- _ /\ _ => split end;
  first [ lia | zlia_zsep1 | zlia_zsep_all ].

Definition zsepmark (P : Prop) : Prop := P.
Ltac zhas G x := lazymatch G with context [x] => idtac end.
Ltac zsep_mark L :=
  lazymatch goal with
  | S : ctx_sep ?rh ?cx |- _ =>
      let T := type of (L rh cx S) in
      lazymatch goal with
      | _ : zsepmark T |- _ => idtac
      | _ => let D := fresh "ZSM" in pose proof (L rh cx S : zsepmark T) as D
      end
  end.
Ltac zpairs_of C p q ob u w romlo :=
  tryif zhas C w then
    (tryif zhas C p then zsep_mark sep_w_p else
     tryif zhas C q then zsep_mark sep_w_q else
     tryif zhas C ob then zsep_mark sep_w_ob else
     tryif zhas C romlo then zsep_mark sep_w_rom else idtac)
  else tryif zhas C p then
    (tryif zhas C q then zsep_mark sep_p_q else
     tryif zhas C ob then zsep_mark sep_p_ob else
     tryif zhas C romlo then zsep_mark sep_p_rom else idtac)
  else tryif zhas C ob then
    (tryif zhas C q then zsep_mark sep_ob_q else
     tryif zhas C u then zsep_mark sep_ob_u else idtac)
  else idtac.
Ltac zpairs_conj G p q ob u w romlo :=
  lazymatch G with
  | ?A /\ ?B => zpairs_conj A p q ob u w romlo; zpairs_conj B p q ob u w romlo
  | _ \/ _ => zpairs_of G p q ob u w romlo
  | _ => idtac
  end.
Ltac zpairs_revert :=
  repeat match goal with
         | D : zsepmark _ |- _ =>
             unfold zsepmark in D;
             cbn [c_u c_p c_q c_n c_ob c_osz c_w] in D; cbv [STATE_SIZE WIN_SIZE FRA ROM_LO_ALL] in D;
             revert D
         end.
Ltac zlia_pairs_go G p q ob u w :=
  let romlo := eval cbv in ROM_LO_ALL in
  zpairs_conj G p q ob u w romlo;
  lazymatch goal with
  | _ : zsepmark _, _ : zsepmark _, _ : zsepmark _, _ : zsepmark _ |- _ => fail "zlia_pairs: more than 3 facts"
  | _ : zsepmark _ |- _ => zpairs_revert; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZPrune.zlia_t1
  | _ => fail "zlia_pairs: no pair in the goal"
  end.
Ltac zlia_pairs :=
  lazymatch goal with
  | S : ctx_sep _ (ICX ?u ?p ?q _ ?ob _ ?w _ _ _ _ _) |- ?G => solve [ zlia_pairs_go G p q ob u w ]
  | S : ctx_sep _ ?cx |- ?G => solve [ zlia_pairs_go G (c_p cx) (c_q cx) (c_ob cx) (c_u cx) (c_w cx) ]
  end.

Ltac zlia ::=
  first
  [ zlia_pairs
  | solve [ OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZPrune.zlia_t1 ]
  | zfastfail;
    first
    [ zlia_sep_guess
    | solve [ lia ]
    | zlia_sep_targeted
    | solve [ zlia_with_sep sep_p_rom ] | solve [ zlia_with_sep sep_w_rom ]
    | solve [ zlia_with_sep sep_p_q ]   | solve [ zlia_with_sep sep_p_ob ]
    | solve [ zlia_with_sep sep_ob_q ]  | solve [ zlia_with_sep sep_ob_u ]
    | solve [ zlia_with_sep sep_w_p ]   | solve [ zlia_with_sep sep_w_q ]
    | solve [ zlia_with_sep sep_w_ob ]
    | solve [ zlia_zsep ] ] ].

Ltac zlia_chk :=
  lazymatch goal with
  | |- ?G => tryif (let X := fresh in assert (X : ~ G) by OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZPrune.zlia_t1) then fail else zlia
  end.

Ltac zlia_nodisj := lia.

Ltac zhead a :=
  lazymatch a with
  | ?x + _ => zhead x
  | ?x - _ => zhead x
  | ?x => x
  end.

Ltac zstore_ok_lit A k a len H segs M :=
  let k' := eval cbv in (Z.of_nat k) in
  lazymatch is_zlit_b len with
  | true =>
    lazymatch zbase_off A with
    | (?b, ?o) =>
      lazymatch zbase_off a with
      | (?b', ?o') =>
          constr_eq b b';
          let inside := eval cbv in (andb (Z.leb o' o) (Z.leb (o + k') (o' + len))) in
          lazymatch inside with
          | true => apply (store_ok_of_mem_wr segs M a len A k H); [zlia | cbn [Z.of_nat]; zlia]
          | false => fail
          end
      end
    end
  end.

Ltac zstore_ok_solve ::=
  lazymatch goal with
  | |- store_ok ?segs ?M (w64 ?A) ?k = true =>
    let hA := zhead A in
    first
    [ match goal with
      | H : mem_wr segs M ?a ?len |- _ => zstore_ok_lit A k a len H segs M
      end
    |
      match goal with
      | H : mem_wr segs M ?a ?len |- _ =>
          solve [ apply (store_ok_of_mem_wr segs M a len A k H);
                  [ OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZPrune.zlia_t1
                  | cbn [Z.of_nat]; OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.ubsan_agrees_alloc_forced_only.IK.ZPrune.zlia_t1 ] ]
      end
    | match goal with
      | H : mem_wr segs M ?a ?len |- _ =>
          let ha := zhead a in constr_eq hA ha;
          apply (store_ok_of_mem_wr segs M a len A k H); [zlia_chk | cbn [Z.of_nat]; zlia_chk]
      end
    | match goal with
      | H : mem_wr segs M ?a ?len |- _ =>
          apply (store_ok_of_mem_wr segs M a len A k H); [zlia_chk | cbn [Z.of_nat]; zlia_chk]
      end
    | fail 1 "zstore_ok_solve: no mem_wr fact covers" A k ]
  end.

Ltac zcond_tac ::=
  nc_concl ltac:(fun g => eval cbv beta iota delta [zcond] in g);
  repeat match goal with H : ?x mod 18446744073709551616 = _ |- context [?x mod 18446744073709551616] => rewrite H end;
  rewrite ?mod_small_u64 by zlia;
  rewrite ?swrap64_small by zlia; rewrite ?swrap32_small by zlia;
  first
  [ reflexivity
  | apply Z.eqb_eq; zlia
  | apply Z.eqb_neq; zlia
  | apply Z.ltb_lt; zlia
  | apply Z.ltb_ge; zlia
  | apply Bool.negb_true_iff; first [apply Z.eqb_neq; zlia | apply Z.ltb_ge; zlia]
  | apply Bool.negb_false_iff; first [apply Z.eqb_eq; zlia | apply Z.ltb_lt; zlia]
  | zlia ].

Ltac zstrip_base A b :=
  lazymatch A with
  | b => constr:(0)
  | b + ?e => e
  | ?A1 + ?e => let e1 := zstrip_base A1 b in constr:(e1 + e)
  | _ =>
      lazymatch b with
      | ?X + ?c => let e1 := zstrip_base A X in constr:(e1 - c)
      | _ => constr:(A - b)
      end
  end.
Ltac zdivk e k :=
  lazymatch k with
  | 1 => e
  | _ =>
    lazymatch e with
    | k * ?x => x
    | ?x * k => x
    | ?e1 + ?e2 => let x1 := zdivk e1 k in let x2 := zdivk e2 k in constr:(x1 + x2)
    | ?e1 - ?e2 => let x1 := zdivk e1 k in let x2 := zdivk e2 k in constr:(x1 - x2)
    | _ =>
        lazymatch is_zlit_b e with
        | true => let v := eval vm_compute in (e / k) in v
        | false => constr:(e / k)
        end
    end
  end.
Ltac zarr_addr_tac k :=
  lazymatch goal with
  | |- ?A = ?b + ?k' * ?i =>
      let e := zstrip_base A b in
      let x := zdivk e k' in
      unify i x; lia
  end.

Ltac zload_arr_with LEM k F E D :=
  match goal with
  | Ha : mem_arr k ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zarr_addr_tac k
      | znorm; zlia_chk | ]
  end.

Ltac zarr_range_tac :=
  first [ match goal with
          | Hr : forall j, _ -> _ <= ?f j < _ |- _ <= ?f _ < _ => apply Hr; zlia
          end
        | zlia_nodisj
        | match goal with
          | Hr : forall j, _ -> _ <= ?f j < _ |- _ <= ?f _ < _ => apply Hr; zlia
          | Hr : forall j, _ -> _ <= ?f j <= _ |- _ => split; [apply Hr; zlia | eapply Z.le_lt_trans; [apply Hr; zlia | zlia]]
          end ].

Ltac zload_arr_with' LEM k F E D :=
  match goal with
  | Ha : mem_arr k ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zarr_addr_tac k
      | znorm; zlia_chk | znorm; zarr_range_tac | ]
  end.

Ltac zarr4_addr_tac :=
  lazymatch goal with
  | |- ?A = ?b + 4 * ?i + ?off =>
      let e := zstrip_base A b in
      let x := zdivk constr:(e - off) constr:(4) in
      unify i x; lia
  | |- ?A = ?b + 4 * ?i =>
      let e := zstrip_base A b in
      let x := zdivk e constr:(4) in
      unify i x; lia
  end.
Ltac zload_arr4_with LEM F E D :=
  match goal with
  | Ha : mem_arr 4 ?segs ?M ?base ?n ?f |- _ =>
      eapply (LEM segs _ _ _ _ _ _ _ _ _ _ base n f);
      [ exact F | exact E | exact D | zhalted | exact Ha
      | znorm; zarr4_addr_tac
      | znorm; zlia_chk | ]
  end.

Ltac tstep_with F E D :=
  first
  [ zstep_with F E D
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ1 false _ _ _, _) =>
        first [ zload_arr_with' zu_lbu_arr' 1 F E D | zload_arr_with zu_lbu_arr 1 F E D
              | zload_arr4_with zu_lbu_arr4_op F E D | zload_arr4_with zu_lbu_arr4_bits F E D
              | zload_arr_with zu_lbu_arr2_lo 2 F E D ]; znorm
    | decode_any _ = Some (Load SZ1 true _ _ _, _) =>
        zload_arr_with zu_lb_arr 1 F E D; znorm
    | decode_any _ = Some (Load SZ2 false _ _ _, _) =>
        first [ zload_arr_with' zu_lhu_arr' 2 F E D | zload_arr_with zu_lhu_arr 2 F E D
              | zload_arr4_with zu_lhu_arr4_val F E D ]; znorm
    | decode_any _ = Some (Load SZ2 true _ _ _, _) =>
        first [ zload_arr_with' zu_lh_arr' 2 F E D | zload_arr_with zu_lh_arr 2 F E D ]; znorm
    | decode_any _ = Some (Load SZ4 false _ _ _, _) =>
        first [ zload_arr_with' zu_lwu_arr' 4 F E D | zload_arr_with zu_lwu_arr 4 F E D ]; znorm
    | decode_any _ = Some (Load SZ4 true _ _ _, _) =>
        first [ zload_arr_with' zu_lw_arr' 4 F E D | zload_arr_with zu_lw_arr 4 F E D ]; znorm
    | decode_any _ = Some (Load SZ8 true _ _ _, _) =>
        zload_arr_with zu_ld_arr 8 F E D; znorm
    end ].

Tactic Notation "tstep" tactic0(fd) := let pc := zpc in fd pc tstep_with.
Tactic Notation "tsteps" tactic0(fd) := repeat (let pc := zpc in fd pc tstep_with).
Tactic Notation "tsteps_to" tactic0(fd) constr(stop) :=
  repeat (lazymatch goal with
          | |- realizes _ (zcfg _ ?pc _ _ _) _ =>
              lazymatch pc with stop => fail | _ => fd pc tstep_with end
          end).

Ltac zmem_transport_arr M a bs :=
  repeat match goal with
  | H : mem_arr ?k ?segs M ?base ?n ?f |- _ =>
      first [ apply (mem_arr_frame segs k M base n f a bs) in H; [|unfold zdisj; zlen_norm; zlia_chk]
            | idtac "ITac: mem_arr fact dropped at store" a; clear H ]
  end.

Ltac zmem_post_arr :=
  lazymatch goal with
  | |- realizes ?segs (zcfg _ ?pc ?R (wbytes ?M (w64 ?a) ?bs) ?MD) ?T => zmem_transport_arr M a bs
  end.

Ltac tstore_arr fd Ha i :=
  lazymatch type of Ha with
  | mem_arr ?k ?segs ?M ?base ?n ?f =>
      let pc := zpc in
      fd pc ltac:(fun F E D =>
        lazymatch type of D with
        | decode_any _ = Some (Store SZ1 _ _ _, _) =>
            eapply zu_sb; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ2 _ _ _, _) =>
            eapply zu_sh; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ4 _ _ _, _) =>
            eapply zu_sw; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        | decode_any _ = Some (Store SZ8 _ _ _, _) =>
            eapply zu_sd; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |]; znorm
        end);
      lazymatch goal with
      | |- realizes _ (zcfg _ _ _ (wbytes M (w64 ?a) (Z_to_le_bytes ?kk ?v)) _) _ =>
          apply (mem_arr_upd segs k M base n f a i v) in Ha; [| zlia | zlia];
          (let kn := eval cbv in (Z.to_nat k) in change (Z.to_nat k) with kn in Ha);
          repeat match goal with
          | H : mem_arr ?k' segs M ?base' ?n' ?f' |- _ =>
              first [ apply (mem_arr_frame segs k' M base' n' f' a (Z_to_le_bytes kk v)) in H; [|unfold zdisj; zlen_norm; zlia_chk]
                    | idtac "ITac: mem_arr fact dropped at array store" a; clear H ]
          end;
          zmem_post
      end
  end.

Ltac zrebase :=
  lazymatch goal with
  | |- realizes ?segs (zcfg ?segs' ?pc (zupd ?Rb ?l) ?M ?MD) ?T =>
      let R0 := fresh "R" in
      set (R0 := zupd Rb l);
      change (realizes segs (zcfg segs' pc (zupd R0 []) M MD) T);
      repeat match goal with
      | H : zget_l Rb l ?k = ?v |- _ => rewrite <- (zget_zupd Rb l k) in H; fold R0 in H
      end;
      clearbody R0
  end.

Lemma zsetreg_lemma : forall segs pc Rb k (e v : Z) rest M MD T, v = e ->
  realizes segs (zcfg segs pc (zupd Rb ((k, v) :: rest)) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb ((k, e) :: rest)) M MD) T.
Proof. intros. subst. assumption. Qed.
Ltac zsetreg v tac := eapply (zsetreg_lemma _ _ _ _ _ v); [tac|].

Ltac zgenreg x :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ =>
      let x' := fresh x in set (x' := e); clearbody x'
  end.
Ltac zgenreg_bool x :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.b2z ?b) :: _)) _ _) _ =>
      let x' := fresh x in let Hx := fresh "R" x in
      set (x' := Z.b2z b);
      assert (Hx : 0 <= x' <= 1) by (subst x'; destruct b; cbn [Z.b2z]; lia);
      clearbody x'
  end.
Ltac zgenreg_range x lo hi tac :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ =>
      let x' := fresh x in let Hx := fresh "R" x in
      set (x' := e);
      assert (Hx : lo <= x' < hi) by (subst x'; tac);
      clearbody x'
  end.

Ltac zlen_fast :=
  repeat match goal with
  | |- context [Z.of_nat (@length ?A (Z_to_le_bytes ?k ?v))] =>
      let n := eval cbv in (Z.of_nat k) in
      change (Z.of_nat (@length A (Z_to_le_bytes k v))) with n
  end.
Ltac zdisj_tac ::= unfold zdisj; zlen_fast; first [ zlia | zlen_norm; zlia ].

Ltac zbool :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.b2z ?b) :: _)) _ _) _ =>
      first
      [ zsetreg 1 ltac:(rewrite ?mod_small_u64 by zlia;
          lazymatch goal with |- 1 = Z.b2z ?b' =>
            replace b' with true; [reflexivity | symmetry; first [apply Z.ltb_lt; zlia | apply Z.eqb_eq; zlia]] end)
      | zsetreg 0 ltac:(rewrite ?mod_small_u64 by zlia;
          lazymatch goal with |- 0 = Z.b2z ?b' =>
            replace b' with false; [reflexivity | symmetry; first [apply Z.ltb_ge; zlia | apply Z.eqb_neq; zlia]] end)
      | fail 1 "zbool: cannot decide" b ]
  end.
Ltac zlit :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e) :: _)) _ _) _ =>
      let v := eval vm_compute in e in zsetreg v ltac:(reflexivity)
  end.

Lemma zfupd_arr_get_set : forall (a : arr) i v j, 0 <= i < arr_len a -> zfupd (arr_get a) i v j = arr_get (arr_set a i v) j.
Proof.
  intros a i v j Hi. destruct (Z.eq_dec j i) as [->|Hne].
  - rewrite zfupd_same, arr_get_set_same by exact Hi. reflexivity.
  - rewrite zfupd_other, arr_get_set_other by lia. reflexivity.
Qed.

Lemma mem_arr_arr_set : forall k segs M base n (a : arr) i v,
  mem_arr k segs M base n (zfupd (arr_get a) i v) -> 0 <= i < arr_len a ->
  mem_arr k segs M base n (arr_get (arr_set a i v)).
Proof.
  intros k segs M base n a i v H Hi. eapply mem_arr_ext; [exact H|].
  intros j Hj. cbn beta. apply zfupd_arr_get_set. exact Hi.
Qed.

Lemma lxor_m1 : forall a, Z.lxor a (-1) = - a - 1.
Proof. intros. rewrite Z.lxor_m1_r. unfold Z.lnot. lia. Qed.

Lemma srliw_small : forall x k, 0 <= x < 4294967296 -> 0 < k < 32 ->
  bv_swrap 32 (Z.shiftr (x mod 4294967296) k) = x / 2 ^ k.
Proof.
  intros x k Hx Hk. rewrite Z.mod_small by lia. rewrite Z.shiftr_div_pow2 by lia.
  apply swrap32_small.
  assert (2 <= 2 ^ k) by (change 2 with (2 ^ 1) at 1; apply Z.pow_le_mono_r; lia).
  assert (0 <= x / 2 ^ k) by (apply Z.div_pos; lia).
  assert (x / 2 ^ k < 2147483648) by (apply Z.div_lt_upper_bound; [lia|]; nia).
  lia.
Qed.

Lemma srli_small : forall x k, 0 <= x < 18446744073709551616 -> 0 <= k ->
  Z.shiftr (x mod 18446744073709551616) k = x / 2 ^ k.
Proof. intros. rewrite Z.mod_small by lia. apply Z.shiftr_div_pow2. lia. Qed.


Lemma land_ones_range : forall a k, 0 <= k -> 0 <= Z.land a (2 ^ k - 1) < 2 ^ k.
Proof.
  intros a k Hk. replace (2 ^ k - 1) with (Z.ones k) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia).
  rewrite Z.land_ones by exact Hk. apply Z.mod_pos_bound. apply Z.pow_pos_nonneg; lia.
Qed.
Lemma land_7 : forall a, 0 <= Z.land a 7 < 8.
Proof. intros a. change 7 with (2 ^ 3 - 1). change 8 with (2 ^ 3). apply land_ones_range. lia. Qed.
Lemma land_255 : forall a, 0 <= Z.land a 255 < 256.
Proof. intros a. change 255 with (2 ^ 8 - 1). change 256 with (2 ^ 8). apply land_ones_range. lia. Qed.



Lemma mod_u64_neg : forall z, -18446744073709551616 <= z < 0 ->
  z mod 18446744073709551616 = z + 18446744073709551616.
Proof.
  intros z Hz. rewrite <- (Z_mod_plus_full z 1 18446744073709551616). rewrite Z.mod_small by lia. lia.
Qed.


Ltac zsmall :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, bv_swrap 32 ?e) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply swrap32_small; zlia)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, bv_swrap 64 ?e) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply swrap64_small; zlia)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 18446744073709551616) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply Z.mod_small; zlia)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 4294967296) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply Z.mod_small; zlia)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 65536) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply Z.mod_small; zlia)
  | |- realizes _ (zcfg _ _ (zupd _ ((_, ?e mod 256) :: _)) _ _) _ => zsetreg e ltac:(symmetry; apply Z.mod_small; zlia)
  end.
Tactic Notation "tstep1" tactic0(fd) := (let pc := zpc in fd pc tstep_with); try zsmall.

Lemma zext32_shift : forall x, 0 <= x < 4294967296 ->
  Z.shiftr (Z.shiftl x 32 mod 18446744073709551616) 32 = x.
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2, Z.shiftr_div_pow2 by lia.
  rewrite Z.mod_small by (change (2 ^ 32) with 4294967296; lia).
  rewrite Z.div_mul by lia. reflexivity.
Qed.
Ltac zext32 := lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.shiftr (Z.shiftl ?x 32 mod 18446744073709551616) 32) :: _)) _ _) _ =>
      zsetreg x ltac:(symmetry; apply zext32_shift; zlia)
  end.

Lemma lxor_bound : forall a b n, 0 <= a < 2 ^ n -> 0 <= b < 2 ^ n -> 0 <= Z.lxor a b < 2 ^ n.
Proof.
  intros a b n Ha Hb.
  destruct (Z_lt_le_dec n 0) as [Hn|Hn]. { rewrite Z.pow_neg_r in Ha by lia. lia. }
  assert (L0 : 0 <= Z.lxor a b) by (apply Z.lxor_nonneg; lia).
  split; [exact L0|].
  destruct (Z.eq_dec (Z.lxor a b) 0) as [E|E]. { rewrite E. apply Z.pow_pos_nonneg; lia. }
  destruct (Z.eq_dec n 0) as [->|Hn0].
  { change (2 ^ 0) with 1 in *. assert (a = 0) by lia. assert (b = 0) by lia. subst. exfalso. apply E. reflexivity. }
  apply Z.log2_lt_pow2; [lia|].
  eapply Z.le_lt_trans; [apply Z.log2_lxor; lia|].
  assert (La : Z.log2 a < n).
  { destruct (Z.eq_dec a 0) as [->|]. { change (Z.log2 0) with 0. lia. } apply Z.log2_lt_pow2; lia. }
  assert (Lb : Z.log2 b < n).
  { destruct (Z.eq_dec b 0) as [->|]. { change (Z.log2 0) with 0. lia. } apply Z.log2_lt_pow2; lia. }
  apply Z.max_lub_lt; assumption.
Qed.

Lemma xor_seqz_sel : forall x y, 0 <= x < 18446744073709551616 -> 0 <= y < 18446744073709551616 ->
  Z.land (Z.b2z (Z.lxor x y mod 18446744073709551616 <? 1) + -1) x = (if x =? y then 0 else x).
Proof.
  intros x y Hx Hy. change 18446744073709551616 with (2 ^ 64) in *.
  pose proof (lxor_bound x y 64 Hx Hy) as B. rewrite Z.mod_small by exact B.
  destruct (Z.eqb_spec x y) as [->|NE].
  - rewrite Z.lxor_nilpotent. reflexivity.
  - assert (NZ : Z.lxor x y <> 0) by (intros E; apply NE; apply Z.lxor_eq; exact E).
    replace (Z.lxor x y <? 1) with false by (symmetry; apply Z.ltb_ge; lia).
    cbn [Z.b2z]. change (0 + -1) with (-1). apply Z.land_m1_l.
Qed.

Ltac zimp E :=
  cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
       kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in E;
  cbv [zget_l] in E; cbn [alookup Pos.eqb] in E;
  rewrite ?zget_zupd in E; cbv [zget_l] in E; cbn [alookup Pos.eqb] in E;
  repeat match type of E with
  | context [match alookup ?l ?k with Some e => e | None => zget ?Rb _ end] =>
      change (match alookup l k with Some e => e | None => zget Rb k end) with (zget_l Rb l k) in E
  end;
  repeat match goal with
  | H : zget_l ?Rb ?l ?k = _ |- _ =>
      lazymatch type of E with context [zget_l Rb l k] => lazymatch type of H with _ = _ => rewrite H in E end end
  | H : zget ?Rb ?k = _ |- _ =>
      lazymatch type of E with _ = zget Rb k => rewrite H in E end
  end.
Ltac zimps :=
  repeat match goal with
  | E : zget ?R ?k = zget_l ?Rb ?l ?k' |- _ => zimp E; lazymatch type of E with zget R k = zget_l Rb l k' => fail | _ => idtac end
  | E : zget ?R ?k = zget (zupd ?Rb ?l) ?k' |- _ => zimp E; lazymatch type of E with zget R k = zget (zupd Rb l) k' => fail | _ => idtac end
  end.

Ltac zarith_goal :=
  lazymatch goal with
  | |- @eq _ _ _ => idtac
  | |- Stdlib.ZArith.BinInt.Z.le _ _ => idtac | |- Stdlib.ZArith.BinInt.Z.lt _ _ => idtac
  | |- Stdlib.ZArith.BinInt.Z.ge _ _ => idtac | |- Stdlib.ZArith.BinInt.Z.gt _ _ => idtac
  | |- Stdlib.ZArith.BinInt.Z.divide _ _ => idtac
  | |- Corelib.Init.Peano.le _ _ => idtac | |- Corelib.Init.Peano.lt _ _ => idtac
  | |- Corelib.Init.Peano.ge _ _ => idtac | |- Corelib.Init.Peano.gt _ _ => idtac
  | |- Stdlib.NArith.BinNat.N.le _ _ => idtac | |- Stdlib.NArith.BinNat.N.lt _ _ => idtac
  | |- Stdlib.PArith.BinPos.Pos.le _ _ => idtac | |- Stdlib.PArith.BinPos.Pos.lt _ _ => idtac
  | |- _ /\ _ => idtac | |- _ \/ _ => idtac | |- ~ _ => idtac | |- False => idtac | |- True => idtac
  | |- _ <-> _ => idtac | |- _ -> _ => idtac
  | |- _ => fail "zarith_goal: not an arithmetic-shaped goal"
  end.

Ltac zkept :=
  repeat match goal with
  | |- ?x = ?x => reflexivity
  | H : zget ?X ?k = _ |- zget ?X ?k = _ => rewrite H
  | H : zget_l ?X ?l ?k = _ |- zget_l ?X ?l ?k = _ => rewrite H
  end;
  first [ reflexivity | assumption | zarith_goal; lia ].

Ltac klia := cbv [WIN_SIZE STATE_SIZE FRA N_LENS N_WORK N_CODES ZS_OFF ZS_SIZE ROM_LO_ALL] in *; lia.
Ltac slia := unfold ZSEP in *; cbv [WIN_SIZE STATE_SIZE FRA N_LENS N_WORK N_CODES ZS_OFF ZS_SIZE ROM_LO_ALL] in *; lia_std.

Ltac zkeys := cbv [kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                   kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6
                   o_strm o_mode o_last o_wrap o_havedict o_flags o_dmax o_check o_total o_head o_wbits
                   o_wsize o_whave o_wnext o_window o_hold o_bits o_length o_offset o_extra o_lencode
                   o_distcode o_lenbits o_distbits o_ncode o_nlen o_ndist o_shave o_next o_lens o_work
                   o_codes o_sane o_back o_was STATE_SIZE N_LENS N_WORK N_CODES WIN_SIZE
                   ORDER_ADDR LENFIX_ADDR DISTFIX_ADDR LBASE_ADDR LEXT_ADDR DBASE_ADDR DEXT_ADDR JTAB_ADDR MOD31_ADDR
                   zs_next_in zs_avail_in zs_total_in zs_next_out zs_avail_out zs_total_out zs_msg zs_state
                   zs_zalloc zs_zfree zs_opaque zs_data_type zs_adler zs_reserved
                   FRA ROM_LO_ALL ZS_OFF ZS_SIZE] in *.

Ltac zreg := nc_concl ltac:(fun g => eval cbv [zget_l kRA kSP kGP kTP kT0 kT1 kT2 kS0 kS1 kA0 kA1 kA2 kA3 kA4 kA5 kA6 kA7
                  kS2 kS3 kS4 kS5 kS6 kS7 kS8 kS9 kS10 kS11 kT3 kT4 kT5 kT6] in g);
             nc_concl ltac:(fun g => eval cbn [alookup Pos.eqb] in g); rewrite ?zget_zupd;
             nc_concl ltac:(fun g => eval cbv [zget_l] in g); nc_concl ltac:(fun g => eval cbn [alookup Pos.eqb] in g);
             zrefold_getl; zbase; first [ reflexivity | assumption | zarith_goal; lia ].

Ltac hyp := lazymatch goal with |- ?G => match goal with Hh : G |- _ => exact Hh end end.
Ltac destr_conj_stock H :=
  lazymatch type of H with
  | _ /\ _ => let H1 := fresh "F" in destruct H as [H1 H]; destr_conj_stock H1; destr_conj_stock H
  | _ => idtac
  end.
Ltac destr_conj H := first [ destr_conj_lin H | destr_conj_stock H ].
Ltac split_conj := repeat match goal with |- _ /\ _ => split end.

Lemma seqz_xor_neq : forall a b, 0 <= a < 18446744073709551616 -> 0 <= b < 18446744073709551616 -> a <> b ->
  Z.b2z (Z.lxor a b mod 18446744073709551616 <? 1) = 0.
Proof.
  intros a b Ha Hb Hne. change 18446744073709551616 with (2 ^ 64) in *.
  pose proof (lxor_bound a b 64 Ha Hb) as B. rewrite Z.mod_small by exact B.
  assert (NZ : Z.lxor a b <> 0) by (intros E; apply Hne; apply Z.lxor_eq; exact E).
  replace (Z.lxor a b <? 1) with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
Qed.
Lemma lnot_val_mod : forall p, 0 <= p < 18446744073709551616 ->
  (- p - 1) mod 18446744073709551616 = 18446744073709551615 - p.
Proof.
  intros p Hp. rewrite <- (Z_mod_plus_full (- p - 1) 1 18446744073709551616). rewrite Z.mod_small by lia. lia.
Qed.
Lemma lnot_val_mod' : forall p, 0 <= p < 18446744073709551616 ->
  (- p + -1) mod 18446744073709551616 = 18446744073709551615 - p.
Proof. intros p Hp. replace (- p + -1) with (- p - 1) by lia. apply lnot_val_mod. exact Hp. Qed.
Ltac znot :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.lxor ?x (-1)) :: _)) _ _) _ =>
      zsetreg (- x + -1) ltac:(rewrite lxor_m1; lia);
      try (let H := fresh "Hnot" in pose proof (lnot_val_mod' x ltac:(zlia)) as H)
  end.

Lemma land_mask0 : forall x n, 0 <= n -> x mod 2 ^ n = 0 -> Z.land x (2 ^ n - 1) = 0.
Proof. intros x n Hn Hm. replace (2 ^ n - 1) with (Z.ones n) by (unfold Z.ones; rewrite Z.shiftl_1_l; lia). rewrite Z.land_ones by exact Hn. exact Hm. Qed.
Lemma mod0_add : forall x k m, 0 < m -> x mod m = 0 -> k mod m = 0 -> (x + k) mod m = 0.
Proof. intros x k m Hm Hx Hk. rewrite Z.add_mod, Hx, Hk by lia_std. reflexivity. Qed.
Lemma mod0_sub : forall x k m, 0 < m -> x mod m = 0 -> k mod m = 0 -> (x - k) mod m = 0.
Proof. intros x k m Hm Hx Hk. rewrite Zminus_mod, Hx, Hk by lia_std. reflexivity. Qed.
Lemma mod0_div : forall x a b, 0 < a -> 0 < b -> x mod (a * b) = 0 -> x mod a = 0.
Proof.
  intros x a b Ha Hb H. rewrite Z.rem_mul_r in H by lia_std.
  pose proof (Z.mod_pos_bound x a Ha) as B. pose proof (Z.mod_pos_bound (x / a) b Hb) as B2. nia.
Qed.
Lemma mod0_16_8 : forall x, x mod 16 = 0 -> x mod 8 = 0.
Proof. intros x H. apply (mod0_div x 8 2); [lia_std | lia_std | exact H]. Qed.
Lemma mod0_16_4 : forall x, x mod 16 = 0 -> x mod 4 = 0.
Proof. intros x H. apply (mod0_div x 4 4); [lia_std | lia_std | exact H]. Qed.
Lemma mod0_16_2 : forall x, x mod 16 = 0 -> x mod 2 = 0.
Proof. intros x H. apply (mod0_div x 2 8); [lia_std | lia_std | exact H]. Qed.
Lemma mod0_8_4 : forall x, x mod 8 = 0 -> x mod 4 = 0.
Proof. intros x H. apply (mod0_div x 4 2); [lia_std | lia_std | exact H]. Qed.
Lemma mod0_4_2 : forall x, x mod 4 = 0 -> x mod 2 = 0.
Proof. intros x H. apply (mod0_div x 2 2); [lia_std | lia_std | exact H]. Qed.
Lemma mod0_mul : forall k m, 0 < m -> (m * k) mod m = 0.
Proof. intros k m Hm. rewrite Z.mul_comm. apply Z.mod_mul. lia_std. Qed.

Ltac zmod0 :=
  first
  [ assumption
  | reflexivity
  | apply mod0_mul; lia_std
  | apply mod0_add; [lia_std | zmod0 | zmod0]
  | apply mod0_sub; [lia_std | zmod0 | zmod0]
  | apply mod0_16_8; zmod0 | apply mod0_16_4; zmod0 | apply mod0_16_2; zmod0
  | apply mod0_8_4; zmod0 | apply mod0_4_2; zmod0 ].
Ltac zalign :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ((_, Z.land ?e ?m) :: _)) _ _) _ =>
      lazymatch m with
      | 1 => zsetreg 0 ltac:(symmetry; apply (land_mask0 e 1); [lia_std | zmod0])
      | 3 => zsetreg 0 ltac:(symmetry; apply (land_mask0 e 2); [lia_std | zmod0])
      | 7 => zsetreg 0 ltac:(symmetry; apply (land_mask0 e 3); [lia_std | zmod0])
      | 15 => zsetreg 0 ltac:(symmetry; apply (land_mask0 e 4); [lia_std | zmod0])
      end
  end.
