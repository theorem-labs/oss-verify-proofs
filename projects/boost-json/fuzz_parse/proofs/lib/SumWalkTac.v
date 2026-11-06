(* Machine-generated data computed from the task's compiled program image (decoder-built tables and encoded data blocks); may contain fragments of third-party object code - see NOTICE. No Anthropic licence header applies to this file. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From LinuxProcessSemantics.LinuxProcessSem Require Import StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare WalkTac StoreOk StreamSim MmapSim.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos35stdpp9bitvectorbdefinitionshfbbv_unsigned37Corelib4Init5Logicka2eq01Z3h5LinuxProcessSemanticsfLinuxProcessSem6BvBasem6dbytes_le_to_Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsq5h0word_to_le_bytes46Stdlib6ZArith6BinInt1Zv02ltv03powhf2bvhf7Z_to_bvka3and69OSSVerify6Proofsaboost_jsonafuzz_parse3lib8PropExec~~~~~~hi84v_lwv02le37Corelib4Init9Datatypeshn04boolhi84c_eqv03eqbhn04truev03addv06of_nathn04listhn06lengthhn06optionhi83rdnhn03natka2or3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypehu47Segment69OSSVerify6Proofsaboost_jsonafuzz_parse3lib7CatExec~~~~~~ii46wbytes" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section FPX1. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma bytes_le_to_Z_4 : ltac2:(zQ "90!h9!jc!le!m3!p5!tc!hg8!hgd!hh3>1v@1$8@1$0#k0>0@2$6@2$1@1$0#k0^1@2$7+2+i0@3$2$3@1$4@2$5N4^2@2$1@1$0#k0^2").
Proof.
  intros v Hv. rewrite bytes_le_N.
  change (2 ^ (8 * Z.of_nat 4))%Z with (2^32)%Z.
  apply Z.mod_small. pose proof (u64_range v). lia.
Qed.

Lemma v_lw_small : ltac2:(zQ "90!h9!hh8!hi2!le!m3!hm3!hmb!hg8!hh3>1z$4>0@2$2@2$6Z^1@2$7^1+ogggggg0@3$3@1$8@1$0#k0@1$5@2$1@1$0#k0^2@2$1@1$0#k0^2").
Proof.
  intros z Hz. unfold v_lw. f_equal. rewrite u_Z2bv by lia.
  apply (bv_swrap_small 32). change (bv_half_modulus 32) with 2147483648%Z. lia.
Qed.

(* [comment removed for export] *)

Lemma c_eq_Z : ltac2:(zQ "b1!hi2!h9!m3!hmb!hg8!hgd!hh8!ho8!le!hp0!hp8&@2$0@2$3Z^2@2$4^2@2$5+2+k0>1a$2>1b$2>0~0>0~0@3$8$7@2$9@2$6@1$1#k0^4@2$6@1$1#k0^3@2$a^4^3").
Proof. intros a b Ha Hb. unfold c_eq, bv_eqb. rewrite !u_Z2bv by lia. reflexivity. Qed.

Lemma c_eq_refl : ltac2:(zQ "60!ho8!hpe!le!h9!hp0!hh3>1x@1$5@1$3#k0@3$2$0@2$4^1^1$1").
Proof. intros x. unfold c_eq. apply bv_eqb_refl. Qed.
End FPX1.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac zlen :=
  repeat match goal with
         | |- context [length (word_to_le_bytes ?n ?v)] => rewrite (length_N_to_le_bytes n v)
         end;
  cbn [Z.of_nat Pos.of_succ_nat Pos.succ length].
Ltac zsimp := zlen; u_norm.

(* [comment removed for export] *)
Ltac sok_stack SOK :=
  store_ok_peel;
  eapply (store_ok_sub _ _ _ _ 144%nat); [ | exact SOK | | ]; zsimp; lia.

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac clear_disj := repeat match goal with H : _ \/ _ |- _ => clear H end.
Ltac lia_fast := first [ solve [ clear_disj; lia ] | lia ].
(* [comment removed for export] *)
Section FPX2. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
Lemma rdn_wbytes_out_Z : ltac2:(zQ "h31!h9!hi2!hmb!hh3!hq6!hqc!hgd!hr5!hh8!hrd!hs7!m3!ht1!hg8!ht8!le!htf!ih9!ile&@2$4^3@1$5@2$9@1$3@1$0#8^5>4segs@1$7$h1>2bs@1$7@1$3@1$0#8>1m>0@1$3@1$0#k0@1$a@1$3@1$0#8>2zb$b>2za$b>1n$e>0@2$1@2$1@2$2Z^2@2$d^2@2$6+2+k0@2$1@2$2@2$4^2@1$5^1@2$6+2+k0@2$1@2$1@2$2Z^3@2$d^3@2$6+2+k0@2$1@2$2~0@2$6+2+k0@2$h0@2$2@2$4^2@1$5^1^3@2$2~0^2@3$f@1$a@1$7@1$3@1$0#8@4$c^7@3$h2^5@2$8@1$0#k0^4^6@2$8@1$0#k0^3^2@4$c^7^5@2$8@1$0#k0^3^2").
Proof.
  (intros segs bs m zb za n nd_i1; ndestruct nd_i1 as (Ha & Han & Hb & Hbn & Hd)).
  apply rdn_wbytes_out; rewrite ?u_Z2bv by lia; lia.
Qed.
End FPX2.
Ltac rdn_peel1 :=
  first [ rewrite rdn_wbytes_out_Z by (zlen; lia_fast)
        | rewrite rdn_wbytes_out by (zsimp; lia_fast) ].  (* [comment removed for export] *)
Ltac rdn_by H := repeat rdn_peel1; exact H.
(* [comment removed for export] *)
Ltac rdn_hyp :=
  match goal with
  | H : rdn _ _ ?a ?n = Some _ |- rdn _ _ ?a ?n = Some _ => exact H
  end.
Ltac rdn_solve :=
  lazymatch goal with
  | |- rdn _ (wbytes _ ?a _) ?b _ = _ =>
      tryif constr_eq a b then (apply rdn_wbytes_hit8; zsimp; lia)
      else (rdn_peel1; rdn_solve)
  | |- _ => rdn_hyp
  end.

(* [comment removed for export] *)
Ltac zbv_target x i :=
  lazymatch x with
  | Z_to_bv 64 (?a - ?b)%Z => let d := eval cbv in (b - i)%Z in constr:(Z_to_bv 64 (a - d))
  | Z_to_bv 64 (?a + ?b)%Z => let d := eval cbv in (b + i)%Z in constr:(Z_to_bv 64 (a + d))
  | Z_to_bv 64 ?a =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (a - d))
      | _ => constr:(Z_to_bv 64 (a + i))
      end
  | _ =>
      lazymatch i with
      | Zneg _ => let d := eval cbv in (- i)%Z in constr:(Z_to_bv 64 (bv_unsigned x - d))
      | _ => constr:(Z_to_bv 64 (bv_unsigned x + i))
      end
  end.

(* [comment removed for export] *)
Ltac addr_norm :=
  match goal with
  | |- context [v_addi ?x ?i] =>
      let e := constr:(v_addi x i) in
      tryif check_closed_term e then wlit_closed e
      else first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  | _ => idtac
  end.

(* [comment removed for export] *)
Ltac sp_renorm :=
  match goal with
  | |- context [regupd _ 2 (v_addi ?x ?i)] =>
      let e := constr:(v_addi x i) in
      first
        [ rewrite (v_addi_0 x)
        | let t := zbv_target x i in
          replace e with t by (unfold v_addi; u_norm; first [reflexivity | f_equal; lia]) ]
  end.

(* [comment removed for export] *)
Ltac getr_hyps :=
  repeat match goal with
         | H : getr ?rs ?n = _ |- context [getr ?rs ?n] => rewrite H
         end.
Ltac addr_tac := getr_hyps; unfold v_addi; u_norm; first [reflexivity | f_equal; lia | apply bv_eq; u_norm; lia].
Ltac val_tac := first [reflexivity | assumption | symmetry; assumption].

(* [comment removed for export] *)
Ltac stepST F D aa vv oktac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Store SZ8 _ _ _, _) =>
        eapply step_sd_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ4 _ _ _, _) =>
        eapply step_sw_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac | oktac ]
    | decode_any _ = Some (Store SZ1 _ _ _, _) =>
        eapply MmapSim.step_sb_at with (a := aa) (v := vv);
        [ exact F | reflexivity | exact D | gres; imm_norm; addr_tac | gres; val_tac
        | reflexivity | oktac ]
    end
  | step_simpl ].

(* [comment removed for export] *)
Ltac stepLD F D bsv vv rdtac vtac :=
  chain_step;
  [ reflexivity
  | lazymatch type of D with
    | decode_any _ = Some (Load SZ8 _ _ _ _, _) => eapply step_ld with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 true _ _ _, _) => eapply step_lw with (bs := bsv) (v := vv)
    | decode_any _ = Some (Load SZ4 false _ _ _, _) => eapply step_lwu with (bs := bsv) (v := vv)
    end;
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac | vtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
Ltac stepLD8 F D vv := stepLD F D (word_to_le_bytes 8 vv) vv ltac:(addr_norm; rdn_solve) ltac:(apply bytes_le_to_Z_8).

(* [comment removed for export] *)
Ltac stepLBU F D bb rdtac :=
  chain_step;
  [ reflexivity
  | eapply step_lbu with (b := bb);
    [ exact F | reflexivity | exact D | gres; imm_norm; getr_hyps; rdtac ]
  | step_simpl ]; vnorm.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
  | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
      lazymatch z with
      | context [bv_unsigned (Z_to_bv 64 _)] => fail
      | _ => rewrite (u_Z2bv z) by lia
      end
  end.

(* [comment removed for export] *)


Section FPX3. Context {fx : OSSVerify.Proofs.boost_json.fuzz_parse.lib.PropExec.FPState}.
End FPX3.

(* [comment removed for export] *)

(* [comment removed for export] *)


(* [comment removed for export] *)
Ltac zaddr H :=
  repeat match type of H with
  | context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in change (a + b)%Z with c in H
  end.

(* [comment removed for export] *)
Ltac zaddr_goal :=
  repeat match goal with
  | |- context [Z_to_bv 64 (?a + ?b)%Z] =>
      let c := eval cbv in (a + b)%Z in
      lazymatch c with
      | Zpos _ => change (a + b)%Z with c
      end
  end.

(* [comment removed for export] *)
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
