(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib Require Import HeapCeil.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Image ZBridge SysStep SFModel CellsX Arr TacX.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Bs Require Import ASegs AsShadow AllocRep.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4TacX~~~~~~02wz37Corelib4Init5Logicjf3andjf2eq37Corelib7Numbers7BinNumsle4Nposle1Z79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Mem~~~~~~o24zx3246Stdlib6ZArith6BinInt1Zs32les32lts33pow35stdpp9bitvectorbdefinitionsub2bvs33muls36shiftls36shiftrub7Z_to_bvubbbv_unsigned37Corelib4Init9Datatypeshjd4conshjd3nil79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib3Arr~~~~~~hm46u32arr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Cells~~~~~~hq84cellhjd3apphjd6lengthhjd4listhjd6optionjf3iffhq82C479OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib4Step~~~~~~ihb8rw_cellss33adds36of_nathm46u64arrhq82C879OSSVerify6Proofsaboost_jsonafuzz_parse3lib2Bs5ASegs~~~~~~io15asegsjf2exhq82CB79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~it03stks33subs36to_nat79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BscAllocWalkKit~~~~~~ji26hidden3h5LinuxProcessSemanticsfLinuxProcessSemcMemImageTypejme7Segment" s.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

(* [comment removed for export] *)
Section HCW.
  Context {HCEIL : HeapCeil}.

Lemma zx32_wz : ltac2:(zQ "a0!jb!l3!l9!n7!ne!rc!tb!u0!u5!hg8>1x$4>0@2$1@2$6Z^1@2$7^1@2$8+2+i0@3$2@1$9@1$3#k0@1$5@1$0^2@1$0^2").
Proof. intros x Hx. unfold zx32, wz. rewrite unsigned_lit by lia. rewrite Z.mod_small by lia. reflexivity. Qed.

Lemma shl32_shr30 : ltac2:(zQ "c0!n7!ne!l3!l9!tb!u0!hgd!u5!hh3!hhc!hi5!hif>1x$1>0@2$2@2$4Z^1@2$5^1@2$7+2+i0@3$3$1@2$9@2$b@1$0#k0@2$a@1$0#k0@2$8^2+i0+he@2$6+4^2").
Proof.
  intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. rewrite Z.shiftr_div_pow2 by lia.
  replace (x * 2^32) with ((4 * x) * 2^30) by lia. apply Z.div_mul. lia.
Qed.

Lemma shl32_val : ltac2:(zQ "b0!n7!ne!u5!l3!l9!tb!u0!hgd!hh3!hi5!hif>1x$1>0@2$3@2$5Z^1@2$6^1@2$2+2+i0@3$4$1@2$a@1$0#k0@2$9@1$0#k0@2$8^2+i0@2$7^2@2$2+2+i0").
Proof. intros x Hx. rewrite Z.shiftl_mul_pow2 by lia. rewrite unsigned_lit by lia. reflexivity. Qed.

(* [comment removed for export] *)
Section WithSegs.
  Variable segs : ltac2:(zQ "20!hvd!jq3@1$0$1").
  Lemma u32arr_snoc : ltac2:(zQ "h20!n7!hg8!hl5!hld!hpe!hu4!huc!hv3!hvd!ig5!l3!igf!ne!ih5!il6!im2!hgd!im8>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$c>2ws@1$8@1$1@1$0#k0>1w@1$1@1$0#k0@2$b@4$4?4segs^4^3@3$6@1$1@1$0#k0^2@3$2@1$1@1$0#k0^1@1$3@1$1@1$0#k0@2$a@4$4?4segs^4^3^2@4$e?4segs^4@2$f^3@2$h0+4@1$h1@2$7@1$1@1$0#k0^2@3$2$5@1$d^1@1$3$5").
  Proof.
    intros m A ws w. unfold u32arr, rw_cells, cells_at. rewrite u32s_app. cbn [u32s map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
    rewrite app_nil_r. rewrite bytes_at_app, u32s_length, length_app. cbn [length].
    replace (Z.of_nat (4 * length ws)) with (4 * Z.of_nat (length ws)) by lia.
    replace (4 * Z.of_nat (length ws + 1)) with (4 * Z.of_nat (length ws) + 4) by lia.
    rewrite wr_at_app by lia. change (Z.of_nat (4 + 0)) with 4. tauto.
  Qed.
  Lemma u64arr_snoc : ltac2:(zQ "h20!n7!hg8!hl5!hld!in1!hu4!huc!hv3!hvd!ig5!l3!igf!ne!inb!il6!im2!hgd!im8>1m>0@1$1@1$0#k0@1$9@1$1@1$0#8>1A$c>2ws@1$8@1$1@1$0#k0>1w@1$1@1$0#k0@2$b@4$4?4segs^4^3@3$6@1$1@1$0#k0^2@3$2@1$1@1$0#k0^1@1$3@1$1@1$0#k0@2$a@4$4?4segs^4^3^2@4$e?4segs^4@2$f^3@2$h0+8@1$h1@2$7@1$1@1$0#k0^2@3$2$5@1$d^1@1$3$5").
  Proof.
    intros m A ws w. unfold u64arr, rw_cells, cells_at. rewrite u64s_app. cbn [u64s map concat cells_bytes cbytes cells_wf cell_wf cells_size csize app].
    rewrite app_nil_r. rewrite bytes_at_app, u64s_length, length_app. cbn [length].
    replace (Z.of_nat (8 * length ws)) with (8 * Z.of_nat (length ws)) by lia.
    replace (8 * Z.of_nat (length ws + 1)) with (8 * Z.of_nat (length ws) + 8) by lia.
    rewrite wr_at_app by lia. change (Z.of_nat (8 + 0)) with 8. tauto.
  Qed.

End WithSegs.

(* [comment removed for export] *)

End HCW.



(* [comment removed for export] *)
Ltac addr_diff_near E A :=
  let k := addr_diff E A in
  let b := eval vm_compute in (Z.ltb (Z.abs k) 2048)%Z in
  lazymatch b with true => k end.

Ltac solve_load_near :=
  match goal with
  | |- context [ov_read_bytes ?segs ?m ?a ?n] =>
    let E := addr_expr a in
    match goal with
    | H : rw_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (rw_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | H : ro_cells segs m ?A ?cs0 |- _ =>
        let k := addr_diff_near E A in
        let kn := eval vm_compute in (Z.to_nat k) in
        split_for_access H segs m A cs0 kn n;
        let cs := lazymatch type of H with ro_cells _ _ _ ?cs => cs end in
        let c := eval_cell_at cs kn in
        lazymatch c with Some ?c0 =>
          rewrite (ro_cells_read_at segs m A cs kn c0 n a H) by (first [cells_cbv; reflexivity | reflexivity | addr_eq_tac])
        end
    | HR : ov_read_bytes segs m ?a' n = Some ?bs |- _ =>
        cbv delta [wa] in HR;
        first [ rewrite HR
              | replace (ov_read_bytes segs m a n) with (Some bs)
                  by (rewrite <- HR; f_equal; word_eq_tac) ]
    end
  end;
  load_post.

Ltac solve_load ::= first [ solve_load_near | solve_load_image ].

(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac head_of t := lazymatch t with ?h _ => head_of h | _ => t end.
Ltac post_callN segs m :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO;
  (let h := head_of ltac:(type of PO) in try unfold h in PO);
  rewrite ?unsigned_lit in PO by lia; rewrite ?Z.add_0_r in PO; revert ms' PO; post_call segs m.
Tactic Notation "callN" uconstr(SPEC) :=
  lazymatch goal with
  | |- evt ?segs _ (MS _ _ _ _ _ ?m _) => eapply evt_cut; [ eapply SPEC | post_callN segs m ]
  end.

(* [comment removed for export] *)
Section HCW2.
  Context {HCEIL : HeapCeil}.

Lemma stk_cells : ltac2:(zQ "h00!n7!hg8!hvd!ne!irc!hu4!hl5!hld!ig5!is5!isa!jgc!il6!tb!jh3!jh9>1m>0@1$1@1$0#k0@1$8@1$1@1$0#8>2lo$3>2hi$3>0@4$b$4^3^2^1>0@2$d^3^2@2$9@1$2@1$1@1$0#8\4junk@1$2@1$1@1$0#8@4$c$4^6^5@3$6$5@2$a@1$f@2$e^4^5^1@1$7$5").
Proof.
  intros m lo hi ST LE. destruct (stk_carve asegs m lo hi (Z.to_nat (hi - lo)) ST) as [_ [junk R]]; [lia|].
  rewrite Z2Nat.id in R by lia. replace (hi - (hi - lo)) with lo in R by lia. exists junk. exact R.
Qed.

(* [comment removed for export] *)
Inductive hidden (P : Prop) : Prop := Hide (p : P).

End HCW2.

Ltac hide_hyp H := apply Hide in H.
Ltac unhide_hyp H := destruct H as [H].
Lemma hidden_out : ltac2:(zQ "10!jm4>1PP>0@1$0^1^2").
Proof. intros P [p]. exact p. Qed.

(* [comment removed for export] *)
Ltac nb_from pf T :=
  lazymatch T with
  | ?A /\ ?B => nb_from constr:(@proj1 A B pf) A; nb_from constr:(@proj2 A B pf) B
  | akobj ?X 4096 => first [ lazymatch goal with _ : akobj X 4096 |- _ => idtac end | pose proof (pf : akobj X 4096) as THB | idtac ]
  | aapp ?X 160 => first [ lazymatch goal with _ : aapp X 160 |- _ => idtac end | pose proof (pf : aapp X 160) as CTB | idtac ]
  | _ => idtac
  end.
Ltac name_bands :=
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [akobj _ 4096] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : hidden ?P |- _ => lazymatch P with context [aapp _ 160] => nb_from constr:(hidden_out P H) P end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [akobj _ 4096] => nb_from H P end end
       end);
  try (match goal with
       | H : ?P |- _ => lazymatch P with hidden _ => fail | _ /\ _ => lazymatch P with context [aapp _ 160] => nb_from H P end end
       end).
(* [comment removed for export] *)
Section HCW3.
  Context {HCEIL : HeapCeil}.

End HCW3.

(* [comment removed for export] *)
