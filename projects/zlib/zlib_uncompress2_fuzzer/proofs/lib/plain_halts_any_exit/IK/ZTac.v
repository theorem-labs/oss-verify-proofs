(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress2_fuzzer.lib.plain_halts_any_exit.IK Require Export ZStep ZMem ZPrune.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
#[local] Existing Instance fx0.



Lemma swrap64_small : forall z, - 9223372036854775808 <= z < 9223372036854775808 -> bv_swrap 64 z = z.
Proof.
  intros z Hz. apply bv_swrap_small.
  change (bv_half_modulus 64) with 9223372036854775808. lia.
Qed.

Lemma swrap32_small : forall z, - 2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small.
  change (bv_half_modulus 32) with 2147483648. lia.
Qed.

Lemma zadd_assoc_fold : forall x a b c, a + b = c -> x + a + b = x + c.
Proof. intros; lia. Qed.
Lemma zadd_0_r' : forall x, x + 0 = x. Proof. intros; lia. Qed.
Lemma zadd_0_l' : forall x, 0 + x = x. Proof. intros; lia. Qed.
Lemma zsub_fold : forall x a, x - a = x + (- a). Proof. intros; lia. Qed.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Ltac zlia0 :=
  repeat match goal with
         | H : context [Z.modulo _ _] |- _ => clear H
         | H : context [Z.div _ _] |- _ => clear H
         end;
  lia.



Ltac is_zlit t :=
  lazymatch t with
  | Z0 => idtac
  | Zpos ?p => is_pos_head p
  | Zneg ?p => is_pos_head p
  end
with is_pos_head p :=
  lazymatch p with
  | xH => idtac
  | xO _ => idtac
  | xI _ => idtac
  end.
Ltac is_closed_pos p :=
  lazymatch p with
  | xH => idtac
  | xO ?q => is_closed_pos q
  | xI ?q => is_closed_pos q
  end.

Ltac is_zlit_b t :=
  match t with
  | _ => let _ := match t with _ => is_zlit t end in constr:(true)
  | _ => constr:(false)
  end.

Ltac zbase_off t :=
  lazymatch t with
  | ?x + ?c =>
      lazymatch is_zlit_b c with
      | true => lazymatch zbase_off x with (?b, ?o) => let o2 := eval cbv in (o + c) in constr:((b, o2)) end
      | false => constr:((t, 0))
      end
  | ?x - ?c =>
      lazymatch is_zlit_b c with
      | true => lazymatch zbase_off x with (?b, ?o) => let o2 := eval cbv in (o - c) in constr:((b, o2)) end
      | false => constr:((t, 0))
      end
  | _ => lazymatch is_zlit_b t with true => constr:((0, t)) | false => constr:((t, 0)) end
  end.

Ltac zsame_base A a :=
  lazymatch zbase_off A with (?b, _) =>
  lazymatch zbase_off a with (?b', _) => constr_eq b b' end end.

Ltac zle_false p q :=
  lazymatch zbase_off p with (?b, ?o) =>
  lazymatch zbase_off q with (?b', ?o') =>
    constr_eq b b'; lazymatch eval cbv in (Z.ltb o' o) with true => idtac end
  end end.
Ltac zlt_false p q :=
  lazymatch zbase_off p with (?b, ?o) =>
  lazymatch zbase_off q with (?b', ?o') =>
    constr_eq b b'; lazymatch eval cbv in (Z.leb o' o) with true => idtac end
  end end.
Ltac zff G :=
  lazymatch G with
  | ?A /\ ?B => first [ zff A | zff B ]
  | ?A \/ ?B => zff A; zff B
  | Z.le ?p ?q => zle_false p q
  | Z.lt ?p ?q => zlt_false p q
  | Z.ge ?p ?q => zle_false q p
  | Z.gt ?p ?q => zlt_false q p
  | @eq Z ?p ?q => first [ zle_false p q | zle_false q p ]
  end.
Ltac zfastfail := tryif (lazymatch goal with |- ?G => zff G end) then fail else idtac.

Ltac zlia_lib := zfastfail; zlia_core.
Ltac zlia := zlia_lib.

Ltac lia ::= zlia_core.


Ltac zfold_step :=
  match goal with
  | |- context [?a + ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a + b) in change (a + b) with c
  | |- context [?a - ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a - b) in change (a - b) with c
  | |- context [?a * ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a * b) in change (a * b) with c
  | |- context [Z.shiftl ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.shiftl a b) in change (Z.shiftl a b) with c
  | |- context [Z.shiftr ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.shiftr a b) in change (Z.shiftr a b) with c
  | |- context [Z.land ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.land a b) in change (Z.land a b) with c
  | |- context [Z.lor ?a ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (Z.lor a b) in change (Z.lor a b) with c
  | |- context [?a mod ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a mod b) in change (a mod b) with c
  | |- context [bv_swrap ?n ?a] =>
      is_zlit a;
      let c := eval cbv in (bv_swrap n a) in change (bv_swrap n a) with c
  | |- context [page_round_up_Z ?a] =>
      is_zlit a;
      let c := eval cbv in (page_round_up_Z a) in change (page_round_up_Z a) with c
  | |- context [?x + ?a + ?b] =>
      is_zlit a; is_zlit b;
      let c := eval cbv in (a + b) in
      rewrite (zadd_assoc_fold x a b c eq_refl)
  | |- context [?x - ?a] =>
      is_zlit a;
      lazymatch a with Z0 => fail | _ => idtac end;
      let c := eval cbv in (- a) in
      rewrite (zsub_fold x a); change (- a) with c
  | |- context [?x + 0] => rewrite (zadd_0_r' x)
  | |- context [0 + ?x] => rewrite (zadd_0_l' x)
  end.

Ltac zfold := repeat zfold_step.


Ltac zc_x0 r := let v := eval cbv in (is_x0 r) in change (is_x0 r) with v.
Ltac zc_key r := let v := eval cbv in (bv_key r) in change (bv_key r) with v.
Ltac zc_s n i := let v := eval cbv in (@bv_signed n i) in change (@bv_signed n i) with v.
Ltac zc_u n i := let v := eval cbv in (@bv_unsigned n i) in change (@bv_unsigned n i) with v.
Ltac znorm_consts :=
  repeat match goal with |- context [is_x0 ?r] => zc_x0 r end;
  repeat match goal with |- context [bv_key ?r] => zc_key r end;
  repeat match goal with
  | |- context [@bv_signed ?n ?i] => lazymatch i with @BV _ _ _ => zc_s n i end
  end;
  repeat match goal with
  | |- context [@bv_unsigned ?n ?i] => lazymatch i with @BV _ _ _ => zc_u n i end
  end.

Ltac znorm_tree :=
  cbv beta iota delta [wb zrd_l zget_l zalu zalu32 zalu32u zmul zmul32 zcond zjalr_tgt];
  cbn beta iota delta [alookup Pos.eqb];
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd ?Rb _) _ _) _ =>
      tryif is_var Rb then idtac else cbv beta iota delta [zget tget]
  | |- _ => try (cbv beta iota delta [zget tget])
  end.

Ltac zrefold_getl :=
  repeat match goal with
  | |- context [match alookup ?l ?k with Some e => e | None => zget ?Rb _ end] =>
      change (match alookup l k with Some e => e | None => zget Rb k end) with (zget_l Rb l k)
  end.

Ltac zbase :=
  repeat match goal with
  | H : alookup ?l ?k = _ |- context [alookup ?l ?k] => rewrite H; cbv iota
  end;
  zrefold_getl;
  repeat match goal with
  | H : zget_l ?Rb ?l ?k = _ |- context [zget_l ?Rb ?l ?k] => rewrite H
  | H : zget ?Rb ?k = _ |- context [zget ?Rb ?k] => rewrite H
  end.

Ltac list_is_explicit l :=
  lazymatch l with
  | nil => idtac
  | _ :: ?t => list_is_explicit t
  end.

Ltac zdedup :=
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd _ ?l) _ _) _ =>
      lazymatch l with
      | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ :: _ =>
          tryif list_is_explicit l
          then (rewrite zcfg_dedup; cbv beta iota delta [dedup remove_key Pos.eqb])
          else idtac
      | _ => idtac
      end
  | |- _ => idtac
  end.

Ltac znorm_pre := cbv beta delta [zrd_l wb].

Ltac zbig_list L :=
  lazymatch L with
  | _ :: _ :: _ :: _ :: _ :: _ :: _ => idtac
  end.

Ltac zgoal_list :=
  match goal with
  | |- context [zupd _ ?L] => lazymatch L with wb _ _ ?tl => tl | _ => L end
  | |- context [zrd_l _ ?L _] => L
  | |- context [zget_l _ ?L _] => L
  end.

Ltac zwith_list_hidden tac :=
  first
  [ let L := zgoal_list in
    zbig_list L;
    let k := fresh "zL" in
    set (k := L) in |- *; tac; subst k
  | tac ].

Ltac zwith_tail_hidden tac :=
  first
  [ let L := zgoal_list in
    lazymatch L with
    | _ :: ?tl =>
        zbig_list tl;
        let k := fresh "zL" in
        set (k := tl) in |- *; tac; subst k
    end
  | tac ].

Ltac znorm_tree1 := cbv beta iota delta [wb zrd_l zget_l zalu zalu32 zalu32u zmul zmul32 zcond zjalr_tgt].
Ltac znorm_tree2 :=
  cbn beta iota delta [alookup Pos.eqb];
  lazymatch goal with
  | |- realizes _ (zcfg _ _ (zupd ?Rb _) _ _) _ =>
      tryif is_var Rb then idtac else cbv beta iota delta [zget tget]
  | |- context [zget ?Rb _] => tryif is_var Rb then idtac else cbv beta iota delta [zget tget]
  | |- _ => idtac
  end.

Ltac znorm :=
  zwith_list_hidden ltac:(znorm_pre; znorm_consts; znorm_tree1);
  znorm_tree2; zbase;
  zwith_tail_hidden zfold;
  zdedup.
Ltac znorm_full := znorm_pre; znorm_consts; znorm_tree; zbase; zfold; zdedup.

Ltac zpc_lit :=
  lazymatch goal with
  | |- realizes _ (zcfg _ ?pc _ _ _) _ => first [ is_zlit pc | fail 1 "pc is not a literal:" pc ]
  end.


Ltac zrdn_norm := znorm.

Ltac zlen_fold_closed :=
  repeat match goal with
  | |- context [Z.of_nat (@length ?A ?x)] =>
      lazymatch x with context [Z.to_nat _] => fail | _ => idtac end;
      let n := eval lazy in (Z.of_nat (@length A x)) in
      is_zlit n; change (Z.of_nat (@length A x)) with n
  end.

Ltac zlen_norm :=
  zlen_fold_closed;
  lazymatch goal with
  | |- context [@length _ _] =>
      rewrite ?length_app, ?repeat_length, ?length_map, ?length_Z_to_le_bytes', ?Nat2Z.inj_add;
      zlen_fold_closed
  | |- _ => idtac
  end.


Ltac zfact_exact :=
  lazymatch goal with
  | |- mem_u64 ?segs ?M ?A _ => match goal with H : mem_u64 segs M A _ |- _ => exact H end
  | |- mem_u32 ?segs ?M ?A _ => match goal with H : mem_u32 segs M A _ |- _ => exact H end
  | |- mem_u16 ?segs ?M ?A _ => match goal with H : mem_u16 segs M A _ |- _ => exact H end
  | |- mem_u8 ?segs ?M ?A _ => match goal with H : mem_u8 segs M A _ |- _ => exact H end
  end.

Ltac zread_solve :=
  zrdn_norm;
  lazymatch goal with
  | |- rdn ?segs ?M (w64 ?A) ?n = Some ?bs =>
    first
    [
      match goal with
      | H : mem_u64 segs M A _ |- _ => exact (mem_u64_rdn _ _ _ _ H)
      | H : mem_u32 segs M A _ |- _ => exact (mem_u32_rdn _ _ _ _ H)
      | H : mem_u16 segs M A _ |- _ => exact (mem_u16_rdn _ _ _ _ H)
      | H : mem_u8  segs M A _ |- _ => exact (mem_u8_rdn _ _ _ _ H)
      | H : mem_is segs M A ?bs' |- _ => exact (mem_is_firstn segs M A bs' n H ltac:(zlen_norm; lia))
      | H : rdn segs M (w64 A) n = Some _ |- _ => exact H
      end
    |
      match goal with
      | H : mem_is segs M ?a ?bs' |- _ =>
          zsame_base A a;
          replace (w64 A) with (w64 (a + (A - a))) by (f_equal; lia);
          apply (mem_is_sub segs M a bs' (A - a) n H); [zlia | zlen_norm; zlia]
      | H : mem_zero segs M ?a ?len |- _ =>
          zsame_base A a;
          replace (w64 A) with (w64 (a + (A - a))) by (f_equal; lia);
          apply (mem_zero_sub segs M a len (A - a) n H); zlia
      end
    |
      match goal with
      | H : mem_is segs M ?a ?bs' |- _ =>
          tryif zsame_base A a then fail else idtac;
          replace (w64 A) with (w64 (a + (A - a))) by (f_equal; lia);
          apply (mem_is_sub segs M a bs' (A - a) n H); [zlia | zlen_norm; zlia]
      end
    |
      match goal with
      | H : mem_zero segs M ?a ?len |- _ =>
          tryif zsame_base A a then fail else idtac;
          replace (w64 A) with (w64 (a + (A - a))) by (f_equal; lia);
          apply (mem_zero_sub segs M a len (A - a) n H); zlia
      end
    | fail 1 "zread_solve: no memory fact covers" A n ]
  end.


Ltac zstore_ok_solve :=
  lazymatch goal with
  | |- store_ok ?segs ?M (w64 ?A) ?k = true =>
    first
    [ match goal with
      | H : mem_wr segs M ?a ?len |- _ =>
          zsame_base A a;
          apply (store_ok_of_mem_wr segs M a len A k H); [zlia | cbn [Z.of_nat]; zlia]
      end
    | match goal with
      | H : mem_wr segs M ?a ?len |- _ =>
          tryif zsame_base A a then fail else idtac;
          apply (store_ok_of_mem_wr segs M a len A k H); [zlia | cbn [Z.of_nat]; zlia]
      end
    | fail 1 "zstore_ok_solve: no mem_wr fact covers" A k ]
  end.

Ltac zdisj_general := unfold zdisj; zlen_norm; zlia.

Ltac zdisj_tac :=
  lazymatch goal with
  | |- zdisj ?a ?n ?a' ?n' =>
      lazymatch is_zlit_b n with
      | true =>
        lazymatch is_zlit_b n' with
        | true =>
          lazymatch zbase_off a with
          | (?b, ?o) =>
            lazymatch zbase_off a' with
            | (?b', ?o') =>
                tryif constr_eq b b' then
                  let sep := eval cbv in (orb (Z.leb (o + n) o') (Z.leb (o' + n') o)) in
                  lazymatch sep with
                  | true => zdisj_general
                  | false => fail
                  end
                else zdisj_general
            end
          end
        | false => zdisj_general
        end
      | false => zdisj_general
      end
  | |- _ => zdisj_general
  end.

Ltac zlookup lc k :=
  let v := eval cbn in (alookup lc k) in
  lazymatch v with
  | Some ?x => x
  | alookup ?l' k => lazymatch goal with H : alookup l' k = Some ?x |- _ => x end
  end.

Ltac zpre :=
  cbn [alookup Pos.eqb];
  first [ assumption | reflexivity | lia | idtac ].

Ltac zmem_wr_solve :=
  first
  [ match goal with
    | H : mem_wr ?segs ?M ?a _ |- mem_wr ?segs ?M ?A _ => zsame_base A a; apply (mem_wr_sub _ _ _ _ _ _ H); zlia
    end
  | match goal with
    | H : mem_wr ?segs ?M ?a _ |- mem_wr ?segs ?M ?A _ =>
        tryif zsame_base A a then fail else idtac; apply (mem_wr_sub _ _ _ _ _ _ H); zlia
    end ].

Ltac zmem_transport M a bs :=
  repeat match goal with
  | H : mem_u64 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u64_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u32 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u32_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u16 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u16_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_u8 ?segs M ?a' ?e |- _ =>
      first [ apply (mem_u8_frame segs M a bs a' e) in H; [|zdisj_tac] | clear H ]
  | H : mem_is ?segs M ?a' ?bs' |- _ =>
      first [ apply (mem_is_frame segs M a bs a' bs') in H; [|zdisj_tac] | clear H ]
  | H : mem_zero ?segs M ?a' ?len |- _ =>
      first [ apply (mem_zero_frame segs M a bs a' len) in H; [|zdisj_tac] | clear H ]
  | H : mem_wr ?segs M ?a' ?len |- _ =>
      apply (mem_wr_frame segs M a bs a' len) in H
  | H : rdn ?segs M _ _ = Some _ |- _ => clear H
  end.

Ltac zmem_post :=
  lazymatch goal with
  | |- realizes ?segs (zcfg _ ?pc ?R (wbytes ?M (w64 ?a) ?bs) ?MD) ?T =>
      zmem_transport M a bs;
      first
      [ lazymatch bs with
        | Z_to_le_bytes 8 ?e => pose proof (mem_u64_stored segs M a e ltac:(zlia) ltac:(zlia))
        | Z_to_le_bytes 4 ?e => pose proof (mem_u32_stored segs M a e ltac:(zlia) ltac:(zlia))
        | Z_to_le_bytes 2 ?e => pose proof (mem_u16_stored segs M a e ltac:(zlia) ltac:(zlia))
        | Z_to_le_bytes 1 ?e => pose proof (mem_u8_stored segs M a e ltac:(zlia) ltac:(zlia))
        | _ => pose proof (mem_is_stored segs M a bs ltac:(zlia) ltac:(zlen_norm; zlia))
        end
      | idtac "zmem_post: could not establish read-back fact at" a ];
      let Mn := fresh "M" in
      set (Mn := wbytes M (w64 a) bs) in *;
      clearbody Mn; try clear M
  end.


Create Rewrite HintDb zmodel.
#[export] Hint Rewrite m_fds_with_fds m_halted_with_fds m_fs_with_fds m_vmmaps_with_fds m_tid_with_fds m_stdin_with_fds : zmodel.
Ltac zmd := autorewrite with model zmodel.

Ltac zhalted := first [ assumption | reflexivity | zmd; first [assumption | reflexivity] ].

Ltac zap4 L F E D := eapply L; [exact F | exact E | exact D | zhalted | ..].
Ltac zap_st L F E D := eapply L; [exact F | exact E | exact D | zhalted | znorm; reflexivity | znorm; zstore_ok_solve |].
Ltac zcbv_iota := cbv iota.
Ltac zexact H := exact H.

Ltac zstep_with F E D :=
  lazymatch type of D with
  | decode_any _ = Some (OpImm _ _ _ _, _) =>
      zap4 zu_opimm F E D; znorm
  | decode_any _ = Some (ShiftImm _ _ _ _, _) =>
      zap4 zu_shiftimm F E D; znorm
  | decode_any _ = Some (Op _ _ _ _, _) =>
      zap4 zu_op F E D; znorm
  | decode_any _ = Some (OpImm32 _ _ _, _) =>
      zap4 zu_opimm32 F E D; znorm
  | decode_any _ = Some (ShiftImm32 _ _ _ _, _) =>
      zap4 zu_shiftimm32 F E D; znorm
  | decode_any _ = Some (Op32 _ _ _ _, _) =>
      zap4 zu_op32 F E D; znorm
  | decode_any _ = Some (Mul _ _ _ _, _) =>
      zap4 zu_mul F E D; znorm
  | decode_any _ = Some (Mul32 _ _ _ _, _) =>
      zap4 zu_mul32 F E D; znorm
  | decode_any _ = Some (Lui _ _, _) =>
      zap4 zu_lui F E D; znorm
  | decode_any _ = Some (Auipc _ _, _) =>
      zap4 zu_auipc F E D; znorm
  | decode_any _ = Some (Jal _ _, _) =>
      zap4 zu_jal F E D; znorm
  | decode_any _ = Some (Jalr _ _ _, _) =>
      zap4 zu_jalr F E D; znorm; zpc_lit
  | decode_any _ = Some (Load SZ8 true _ _ _, _) =>
      first
      [ eapply zu_ld_u64; [exact F | exact E | exact D | zhalted | znorm; zfact_exact |]; znorm
      | eapply zu_ld; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm ]
  | decode_any _ = Some (Load SZ4 false _ _ _, _) =>
      first
      [ eapply zu_lwu_u32; [exact F | exact E | exact D | zhalted | znorm; zfact_exact |]; znorm
      | eapply zu_lwu; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm ]
  | decode_any _ = Some (Load SZ4 true _ _ _, _) =>
      first
      [ eapply zu_lw_u32; [exact F | exact E | exact D | zhalted | znorm; zfact_exact |]; znorm
      | eapply zu_lw; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm ]
  | decode_any _ = Some (Load SZ2 false _ _ _, _) =>
      eapply zu_lhu; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm
  | decode_any _ = Some (Load SZ2 true _ _ _, _) =>
      eapply zu_lh; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm
  | decode_any _ = Some (Load SZ1 false _ _ _, _) =>
      eapply zu_lbu; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm
  | decode_any _ = Some (Load SZ1 true _ _ _, _) =>
      eapply zu_lb; [exact F | exact E | exact D | zhalted | zread_solve |]; znorm
  | decode_any _ = Some (Store SZ8 _ _ _, _) =>
      zap_st zu_sd F E D; znorm; zmem_post
  | decode_any _ = Some (Store SZ4 _ _ _, _) =>
      zap_st zu_sw F E D; znorm; zmem_post
  | decode_any _ = Some (Store SZ2 _ _ _, _) =>
      zap_st zu_sh F E D; znorm; zmem_post
  | decode_any _ = Some (Store SZ1 _ _ _, _) =>
      zap_st zu_sb F E D; znorm; zmem_post
  | True => fail "zstep: ecall (use a syscall tactic)"
  | ?t => fail "zstep: unsupported instruction" t
  end.

Ltac zpc :=
  lazymatch goal with
  | |- realizes _ (zcfg _ ?pc _ _ _) _ => pc
  end.

Tactic Notation "zstep" tactic0(fd) :=
  let pc := zpc in fd pc zstep_with.

Tactic Notation "zsteps" tactic0(fd) :=
  repeat (let pc := zpc in fd pc zstep_with).

Tactic Notation "zsteps_to" tactic0(fd) constr(stop) :=
  repeat (let pc := zpc in
          lazymatch pc with
          | stop => fail
          | _ => fd pc zstep_with
          end).


Lemma zu_branch_b : forall (b : bool) segs pc Rb l M MD T w c rs1 rs2 (imm : bv 13),
  fetch_word segs (w64 pc) = Some w -> is_ecall w = false ->
  decode_any w = Some (Branch c rs1 rs2 imm, 4%Z) -> m_halted MD = None ->
  zcond c (zrd_l Rb l rs1) (zrd_l Rb l rs2) = b ->
  realizes segs (zcfg segs (if b then pc + bv_signed imm else pc + 4) (zupd Rb l) M MD) T ->
  realizes segs (zcfg segs pc (zupd Rb l) M MD) T.
Proof. intros; eapply zu_branch; eassumption. Qed.

Ltac zcond_decide :=
  lazymatch goal with
  | |- (_ =? _) = true => apply Z.eqb_eq; zlia
  | |- (_ =? _) = false => apply Z.eqb_neq; zlia
  | |- (_ <? _) = true => apply Z.ltb_lt; zlia
  | |- (_ <? _) = false => apply Z.ltb_ge; zlia
  | |- negb _ = true => apply Bool.negb_true_iff; zcond_decide
  | |- negb _ = false => apply Bool.negb_false_iff; zcond_decide
  | |- _ => zlia
  end.

Ltac zcond_tac :=
  cbv beta iota delta [zcond];
  repeat match goal with H : ?x mod 18446744073709551616 = _ |- context [?x mod 18446744073709551616] => rewrite H end;
  rewrite ?mod_small_u64 by zlia;
  rewrite ?swrap64_small by zlia; rewrite ?swrap32_small by zlia;
  first [ reflexivity | zcond_decide ].

Ltac zbr_with bv F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch _ _ _ _, _) =>
      eapply (zu_branch_b bv); [zexact F | zexact E | zexact D | zhalted | znorm; zcond_tac | ]; zcbv_iota; znorm
  | ?t => fail 1 "zbr: not a branch" t
  end.

Tactic Notation "zbr" tactic0(fd) constr(bv) :=
  let pc := zpc in fd pc ltac:(fun F E D => zbr_with bv F E D).

Ltac zcase_with F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Branch ?c ?rs1 ?rs2 _, _) =>
      lazymatch goal with
      | |- realizes _ (zcfg _ _ ?R _ _) _ =>
        let cnd := constr:(zcond c (zrd R rs1) (zrd R rs2)) in
        let cnd' := eval cbv beta iota delta [zcond zrd zget tget is_x0 bv_key bv_unsigned Z.eqb Z.to_pos Z.add Pos.add Pos.succ] in cnd in
        let Hc := fresh "Hc" in
        destruct cnd' eqn:Hc;
        [ eapply (zu_branch _ _ _ _ _ _ _ _ _ _ _ _ true); [exact F | exact E | exact D | zhalted | znorm; exact Hc | ]; cbv iota; znorm
        | eapply (zu_branch _ _ _ _ _ _ _ _ _ _ _ _ false); [exact F | exact E | exact D | zhalted | znorm; exact Hc | ]; cbv iota; znorm ]
      end
  | ?t => fail 1 "zcase: not a branch" t
  end.

Tactic Notation "zcase" tactic0(fd) :=
  let pc := zpc in fd pc zcase_with.


Ltac zecall_with F E D :=
  eapply zu_ecall; [exact F | exact E | zhalted |]; znorm.

Tactic Notation "zecall" tactic0(fd) :=
  let pc := zpc in fd pc zecall_with.

Ltac zret_with F E D :=
  lazymatch type of D with
  | decode_any _ = Some (Jalr _ _ _, _) =>
      eapply zu_jalr_to; [exact F | exact E | exact D | zhalted | znorm; reflexivity | first [assumption | reflexivity] | ]; znorm
  | ?t => fail 1 "zret: not a jalr" t
  end.

Tactic Notation "zret" tactic0(fd) :=
  let pc := zpc in fd pc zret_with.
