(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Lib Require Import Tac Arr Bytes StoreFast ZBridge.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.Sj Require Import SjS1Out SjStage2 SjLeaves.
From OssFuzzTheorems.Proofs.simdjson.fuzz_element.lib.U Require Import Sj_stage2_defs Sj_stage2_traps.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Open Scope bv_scope.

Lemma land3_mod : forall x, (Z.land x 3 = x mod 4)%Z.
Proof. intros x. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.
Lemma land7_mod : forall x, (Z.land x 7 = x mod 8)%Z.
Proof. intros x. change 7%Z with (Z.ones 3). rewrite Z.land_ones by lia. reflexivity. Qed.

Ltac g_lxor_in K :=
  repeat match type of K with
  | context [Z.lxor ?x 18446744073709551615] => rewrite (ZBridge.zb_lxor_ones x) in K by lia
  end.
Ltac g_norm_in K := rewrite ?land3_mod, ?land7_mod in K; g_lxor_in K.
Ltac g_lia := lia.

Ltac g_b2z_in K :=
  repeat match type of K with
  | context [Z.b2z (Z.ltb ?a ?b)] =>
      first [ replace (Z.ltb a b) with true in K by (symmetry; apply Z.ltb_lt; g_lia)
            | replace (Z.ltb a b) with false in K by (symmetry; apply Z.ltb_ge; g_lia) ]
  | context [Z.b2z (Z.eqb ?a ?b)] =>
      first [ replace (Z.eqb a b) with true in K by (symmetry; apply Z.eqb_eq; g_lia)
            | replace (Z.eqb a b) with false in K by (symmetry; apply Z.eqb_neq; g_lia) ]
  end;
  cbn [Z.b2z] in K;
  change (Z.lxor 1 0) with 1%Z in K; change (Z.lxor 0 1) with 1%Z in K; change (Z.lxor 1 1) with 0%Z in K; change (Z.lxor 0 0) with 0%Z in K.
Ltac g_solve K := exfalso; g_b2z_in K; zify_cond K; g_norm_in K;
  lazymatch type of K with
  | context [Z.modulo] => s2_unhide; g_lia
  | _ => g_lia
  end.

Ltac gguard :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ (if ?c then Z_to_bv 64 ?a else Z_to_bv 64 ?b) _ _ _ _) =>
      let tb := eval vm_compute in (is_trapj b) in
      lazymatch tb with
      | true => let K := fresh "KG" in destruct c eqn:K; [clear K | first [ g_solve K | fail 3 "UBSan guard not discharged (else arm traps)" ] ]
      | false =>
          let ta := eval vm_compute in (is_trapj a) in
          lazymatch ta with
          | true => let K := fresh "KG" in destruct c eqn:K; [ first [ g_solve K | fail 3 "UBSan guard not discharged (then arm traps)" ] | clear K]
          end
      end
  end.

Ltac s2_store_done_wr_v2 :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ (write_to_mem ?m ?a ?bs) _) =>
      let Ea := addr_expr a in
      (match goal with
       | H : wr_at segs m ?A ?N |- _ =>
           let idx := strip_base Ea A in
           let n := lazymatch bs with
                    | le8 _ => constr:(8%nat) | le4 _ => constr:(4%nat) | le2 _ => constr:(2%nat) | le1 _ => constr:(1%nat)
                    | [_] => constr:(1%nat) | Z_to_le_bytes ?k _ => constr:(k) end in
           let HS := fresh "HSOK" in
           assert (HS : store_ok segs m a n = true)
             by (apply (wr_store_ok_at m A N idx n a H); [lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia | unfold wa; f_equal; lia])
       end);
      store_done
  | _ => idtac
  end.

Lemma u8_B_hook : forall bs i, bytes_ok bs -> bv_unsigned (Z_to_bv 8 (B bs i)) = B bs i.
Proof. intros bs i H. apply u8_small. apply B_range. exact H. Qed.
Ltac gnorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 8 (B ?bs ?i))] => rewrite (u8_B_hook bs i) by assumption
  end;
  s2norm.

Ltac g_store_hook := idtac.
Ltac gstep := zstep; gnorm; g_store_hook; s2_store_done_wr_v2.

Ltac greg_val R n :=
  let p := eval vm_compute in (Z.to_pos (n + 1)) in
  let v := eval lazy beta iota delta [tget] in (tget p R) in
  lazymatch v with Some ?x => x end.

Ltac gsafe keep R x :=
  let chk m := (tryif keep m then idtac else (let y := greg_val R m in tryif constr_eq x y then fail 1 else idtac)) in
  chk 1%Z; chk 5%Z; chk 6%Z; chk 7%Z; chk 8%Z; chk 9%Z; chk 10%Z; chk 11%Z; chk 12%Z; chk 13%Z; chk 14%Z; chk 15%Z; chk 16%Z; chk 17%Z;
  chk 18%Z; chk 19%Z; chk 20%Z; chk 21%Z; chk 22%Z; chk 23%Z; chk 24%Z; chk 25%Z; chk 26%Z; chk 27%Z; chk 28%Z; chk 29%Z; chk 30%Z; chk 31%Z.
Ltac gforget keep n :=
  lazymatch goal with |- evt _ _ (MS ?R _ _ _ _ _ _) =>
    let x := greg_val R n in
    tryif is_var x then idtac else
    (tryif gsafe keep R x then (let j := fresh "jk" in generalize x; intro j) else idtac)
  end.
Ltac gforget_F :=
  lazymatch goal with |- evt _ _ (MS _ ?F _ _ _ _ _) =>
    tryif is_var F then idtac else (let j := fresh "jF" in generalize F; intro j) end.
Ltac gforget_all keep :=
  let go n := (tryif keep n then gforget keep n else idtac) in
  go 1%Z; go 5%Z; go 6%Z; go 7%Z; go 8%Z; go 9%Z; go 10%Z; go 11%Z; go 12%Z; go 13%Z; go 14%Z; go 15%Z; go 16%Z; go 17%Z;
  go 18%Z; go 19%Z; go 20%Z; go 21%Z; go 22%Z; go 23%Z; go 24%Z; go 25%Z; go 26%Z; go 27%Z; go 28%Z; go 29%Z; go 30%Z; go 31%Z;
  gforget_F.

Ltac grun := repeat first [ gguard | gstep ].

Ltac grun_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | gstep ]).

Inductive forgets : list cell -> list cell -> Prop :=
| fg_nil : forgets [] []
| fg_keep : forall c l l', forgets l l' -> forgets (c :: l) (c :: l')
| fg_drop : forall c l l', forgets l l' -> forgets (c :: l) (CB (csize c) (cbytes c) :: l').

Lemma rw_cells_forgets : forall segs m sl sl', forgets sl sl' -> forall A rest,
  rw_cells segs m A (sl ++ rest) -> rw_cells segs m A (sl' ++ rest).
Proof.
  intros segs m sl sl' H. induction H as [|c l l' H IH|c l l' H IH]; intros A rest HR; [exact HR| |].
  - change ((c :: l) ++ rest) with ([c] ++ (l ++ rest)) in HR. apply rw_cells_app in HR. destruct HR as [H1 H2].
    change ((c :: l') ++ rest) with ([c] ++ (l' ++ rest)). apply rw_cells_app. split; [exact H1|]. apply IH. exact H2.
  - change ((c :: l) ++ rest) with ([c] ++ (l ++ rest)) in HR. apply rw_cells_app in HR. destruct HR as [H1 H2].
    change ((CB (csize c) (cbytes c) :: l') ++ rest) with ([CB (csize c) (cbytes c)] ++ (l' ++ rest)). apply rw_cells_app. split.
    + pose proof (rw_cells_merge segs m A [] [c] []) as M. cbn [app cells_size cells_bytes Nat.add] in M.
      rewrite Nat.add_0_r, app_nil_r in M. apply M. exact H1.
    + cbn [cells_size csize Nat.add] in *. rewrite Nat.add_0_r in *. apply IH. exact H2.
Qed.

Lemma MEMI_forgets : forall E nxt sl sl' sc fc m1, MEMI E nxt sl sc fc m1 -> forgets sl sl' -> MEMI E nxt sl' sc fc m1.
Proof.
  intros E nxt sl sl' sc fc m1 (FRM & FR & REST) H. split; [exact FRM|]. split; [|exact REST].
  eapply rw_cells_forgets; [exact H| exact FR].
Qed.

Ltac forgets_tac := repeat first [ apply fg_nil | apply fg_keep | apply fg_drop ].

Ltac s2_close_forget :=
  lazymatch goal with
  | |- MEMI ?E _ _ _ _ ?m =>
      lazymatch goal with

      | FRh : rw_cells _ m (Z.add (bv_unsigned (e_sp _)) _) (?c0 :: ?c1 :: ?c2 :: ?c3 :: ?c4 :: ?c5 :: ?c6 :: ?c7 :: ?c8 :: ?c9 :: _) |- _ =>
          eapply (MEMI_forgets _ _ [c0; c1; c2; c3; c4; c5; c6; c7; c8; c9]); [ s2_close_mem | ]
      end
  end.

Ltac s2_close_memx :=
  eapply (MEMX_of_MEMI _ _);
  [ s2_close_mem; [ rewrite ?upd_length; eassumption | apply oc_rel_nil | rewrite ?upd_length; eassumption | apply ia_rel_nil ]
  | reflexivity .. ].

Ltac gshow_regs :=
  lazymatch goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) =>
    let sh n := (let v := greg_val R n in idtac "REG" n "=" v) in
    sh 1%Z; sh 5%Z; sh 6%Z; sh 7%Z; sh 8%Z; sh 9%Z; sh 10%Z; sh 11%Z; sh 12%Z; sh 13%Z; sh 14%Z; sh 15%Z; sh 16%Z; sh 17%Z;
    sh 18%Z; sh 19%Z; sh 20%Z; sh 21%Z; sh 22%Z; sh 23%Z; sh 24%Z; sh 25%Z; sh 26%Z; sh 27%Z; sh 28%Z; sh 29%Z; sh 30%Z; sh 31%Z;
    idtac "PC =" pc
  end.

Ltac gdec := first [ if_true | if_false ].
Ltac grun_dec := repeat first [ gguard | gstep | gdec ].
Ltac grun_dec_to A :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => lazymatch pc with A => fail | _ => idtac end
          | _ => idtac end;
          first [ gguard | gstep | gdec ]).

Ltac gexplore stop fin :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) => stop pc
          | _ => idtac end;
          first [ gguard | gstep ]);
  first [ fin tt | (let KB := fresh "KB" in if_cases KB; clear KB; gexplore stop fin) ].

Ltac gexit KX :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ (Z_to_bv 64 0x4bfd0%Z) _ _ _ _) =>
      let v := greg_val R 10%Z in
      lazymatch v with
      | Z_to_bv 64 ?e => eapply (KX e); [s2_errlit|]; s2_close_memx
      end
  end.
