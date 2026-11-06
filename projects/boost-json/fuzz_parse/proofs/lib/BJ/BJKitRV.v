(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require BJ0Gc2. (* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Tac Arr SysStep TacX ZBridge Exec CellsX Bytes.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Ref Require Import RSegs RMalloc_iface_stmt.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.BJ Require Import BJKitIn.
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import Nd.   (* [comment removed for export] *)
From OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib Require Import NaryI.
Require Import OSSVerify.Proofs.boost_json.fuzz_parse.lib.Lib.CDef.
Local Ltac2 zQ s := CDef.cdeft "37Corelib7Numbers7BinNums04Npos3h5LinuxProcessSemantics5Riscv7Preludehf5bvmap79OSSVerify6Proofsaboost_jsonafuzz_parse3lib2BJ7BJKitRV~~~~~~kd2rv35stdpp9bitvectorbdefinitionsof2bvkd3ra0kd3ra1kd3ra2kd3ra3kd3ra4kd3ra5kd3ra6kd3ra7kd3rgpkd3rrakd3rs0kd3rs1kd4rs10kd4rs11kd3rs2kd3rs3kd3rs4kd3rs5kd3rs6kd3rs7kd3rs8kd3rs9kd3rspkd3rt0kd3rt1kd3rt2kd3rt3kd3rt4kd3rt5kd3rt6kd3rtp79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib5Frame~~~~~~hmd3mkR37Corelib4Init9Datatypeshr06option01Z3h5LinuxProcessSemanticsfLinuxProcessSemeRiscvSemanticsht5dmachine_state37Corelib4Init5Logicihd2exhr04Noneihd3andihd2eqkd4mkRr79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib6MState~~~~~~il32MS79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Lib8PropExec~~~~~~ip67seg_rom79OSSVerify6Proofsaboost_jsonafuzz_parse3lib3Ref5RSegs~~~~~~iu05rsegsof7Z_to_bvkd8seg_postofbbv_unsigned" s.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Record rv := RV {
  rra : word; rsp : word; rgp : word; rtp : word; rt0 : word; rt1 : word; rt2 : word; rs0 : word; rs1 : word;
  ra0 : word; ra1 : word; ra2 : word; ra3 : word; ra4 : word; ra5 : word; ra6 : word; ra7 : word;
  rs2 : word; rs3 : word; rs4 : word; rs5 : word; rs6 : word; rs7 : word; rs8 : word; rs9 : word; rs10 : word; rs11 : word;
  rt3 : word; rt4 : word; rt5 : word; rt6 : word }.

Definition mkRr : ltac2:(zQ "40!h9!k5!oa!qc>1r$2@2$1@1$0#5@1$3@1$0#k0") := ltac2:(zQ "i10!r1!r7!rd!s3!s9!sf!t5!tb!u1!u7!ud!v3!v9!hg0!hg7!hgd!hh3!hh9!hhf!hi5!hib!hj1!hj7!hjd!hk3!hk9!hkf!hl5!hlb!hm1!hm7!oa!hq9\1r$hf@hf$i0@1$9^1@1$h6^1@1$8^1@1$he^1@1$h7^1@1$h8^1@1$h9^1@1$a^1@1$b^1@1$0^1@1$1^1@1$2^1@1$3^1@1$4^1@1$5^1@1$6^1@1$7^1@1$e^1@1$f^1@1$h0^1@1$h1^1@1$h2^1@1$h3^1@1$h4^1@1$h5^1@1$c^1@1$d^1@1$ha^1@1$hb^1@1$hc^1@1$hd^1").


(* [comment removed for export] *)
Ltac rv_reg R i :=
  let p := eval vm_compute in (bv_key (Z_to_bv 5 i)) in
  eval cbv beta iota delta [tget mkR mkRr rra rsp rgp rtp rt0 rt1 rt2 rs0 rs1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
                            rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rt3 rt4 rt5 rt6]
       in (match tget p R with Some v => v | None => w0 end).

Ltac rv_of R :=
  let x1 := rv_reg R 1 in let x2 := rv_reg R 2 in let x3 := rv_reg R 3 in let x4 := rv_reg R 4 in
  let x5 := rv_reg R 5 in let x6 := rv_reg R 6 in let x7 := rv_reg R 7 in let x8 := rv_reg R 8 in
  let x9 := rv_reg R 9 in let x10 := rv_reg R 10 in let x11 := rv_reg R 11 in let x12 := rv_reg R 12 in
  let x13 := rv_reg R 13 in let x14 := rv_reg R 14 in let x15 := rv_reg R 15 in let x16 := rv_reg R 16 in
  let x17 := rv_reg R 17 in let x18 := rv_reg R 18 in let x19 := rv_reg R 19 in let x20 := rv_reg R 20 in
  let x21 := rv_reg R 21 in let x22 := rv_reg R 22 in let x23 := rv_reg R 23 in let x24 := rv_reg R 24 in
  let x25 := rv_reg R 25 in let x26 := rv_reg R 26 in let x27 := rv_reg R 27 in let x28 := rv_reg R 28 in
  let x29 := rv_reg R 29 in let x30 := rv_reg R 30 in let x31 := rv_reg R 31 in
  constr:(RV x1 x2 x3 x4 x5 x6 x7 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 x28 x29 x30 x31).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac rv_proj_cbn :=
  cbn [rra rsp rgp rtp rt0 rt1 rt2 rs0 rs1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rt3 rt4 rt5 rt6].
Ltac post_boxed P := first [ is_var P | lazymatch P with ?f _ => is_var f end ].
Ltac box_post :=
  lazymatch goal with
  | |- evt ?segs ?P ?st =>
      tryif post_boxed P then idtac else
      (lazymatch st with
       | MS (mkRr ?r) _ _ _ _ _ _ =>
           tryif is_var r then
             (pattern r;
              lazymatch goal with
              | |- (fun x => evt _ (@?PP x) (@?ST x)) _ =>
                  pose (SEGPF := PP); let st' := eval cbv beta in (ST r) in change (evt segs (SEGPF r) st')
              end)
           else idtac
       | _ => idtac
       end)
  | |- _ => idtac
  end.
Ltac unbox_post :=
  repeat match goal with
  | B := ?body : rv -> machine_state -> Prop |- evt ?segs (?BV ?r) ?st =>
      constr_eq BV B;     (* [comment removed for export] *)
      let P := eval cbv beta in (body r) in
      let P := eval cbn [rra rsp rgp rtp rt0 rt1 rt2 rs0 rs1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rt3 rt4 rt5 rt6] in P in
      change (evt segs P st); clear B
  | B := _ : rv -> machine_state -> Prop |- _ => subst B; cbv beta; rv_proj_cbn
  end.
(* [comment removed for export] *)
Ltac hide_post_once := lazymatch goal with |- evt _ ?P _ => tryif post_boxed P then idtac else set (SEGPOST := P) | |- _ => idtac end.
Ltac intro_rv_subst ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 :=
  try subst ra; try subst sp; try subst gp; try subst tp; try subst t0; try subst t1; try subst t2; try subst s0; try subst s1;
  try subst a0; try subst a1; try subst a2; try subst a3; try subst a4; try subst a5; try subst a6; try subst a7;
  try subst s2; try subst s3; try subst s4; try subst s5; try subst s6; try subst s7; try subst s8; try subst s9; try subst s10;
  try subst s11; try subst t3; try subst t4; try subst t5; try subst t6.
Ltac intro_rv r :=
  box_post;
  destruct r as [ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6];
  change (mkRr (RV ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6))
    with (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) in *;
  cbn [rra rsp rgp rtp rt0 rt1 rt2 rs0 rs1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7 rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rt3 rt4 rt5 rt6] in *;
  intro_rv_subst ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6;
  unbox_post.

(* [comment removed for export] *)
Ltac st1b :=
  st1;
  try (lazymatch goal with
       | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) => rewrite (le1_byte w); mem_after_store
       end).

(* [comment removed for export] *)
Definition boxP : ltac2:(zQ "00>1PPP") := ltac2:(zQ "00\1PP^1").
Ltac box_ugly K :=
  lazymatch type of K with
  | context [Z.lor _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
  | context [Z.land _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
  | context [Z.shiftl _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
  | context [Z.shiftr _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
  | context [Z.modulo _ _] => change (boxP ltac:(let T := type of K in exact T)) in K
  | _ => idtac
  end.
Ltac gen_data :=
  repeat (lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      match R with
      | context [Z_to_bv 64 (Z.lor ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.lor a b)) in |- *; clearbody w
      | context [Z_to_bv 64 (Z.land ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.land a b)) in |- *; clearbody w
      | context [Z_to_bv 64 (Z.shiftl ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.shiftl a b)) in |- *; clearbody w
      | context [Z_to_bv 64 (Z.shiftr ?a ?b)] => let w := fresh "dw" in set (w := Z_to_bv 64 (Z.shiftr a b)) in |- *; clearbody w
      end
  end).

(* [comment removed for export] *)
Ltac run_to stops :=
  repeat (lazymatch goal with
          | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
              lazymatch stops with
              | context [pc] => fail
              | _ => st1b; gen_data
              end
          end).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition seg_post : ltac2:(zQ "70!h9!qc!hs8!ht2!igc!k5!oa>1F@2$5@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>6LEAVES>0$3>0$6>0>0@1$1@1$0#k0@1$2@1$1@1$0#8P>0$4P") := ltac2:(zQ "h01!h9!qc!hs8!ij1!ht2!oa!igc!ij7!ijf!ik6!k5!ikc!ip0!it5!jhc!ji5&>0@1$1@1$0#k0@1$2@1$1@1$0#8\1F@2$a@1$0#5@1$1@1$0#k0\2fc@1$1@1$0#i0\6LEAVES>0$4>0$5>0~0P\2ms$6@2$3$4\3pc'$4@2$3$5\2r'$5@2$3~0\2m'~0@2$8@3$9$6^4@7$c@1$b^2^7@2$f@1$0#k0^3^6@1$7@1$1@1$0#k0^1@1$d$e@3^5^3^2^1").
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma seg_post_intro : ltac2:(zQ "d1!h9!qc!hs8!ht2!oa!ij7!k5!ikc!jif!ip0!it5!jhc!ji5&>0@1$1@1$0#k0@1$2@1$1@1$0#8>1F@2$6@1$0#5@1$1@1$0#k0>2fc@1$1@1$0#i0>6LEAVES>0$3>0$4>0~0P>2pc$3>1r$4>1m~0>0@3^4^3^2^1@4$8^7^6^5@7$9@1$7^3^7@2$c@1$0#k0^4^6@1$5@1$1@1$0#k0^2@1$a$b").
Proof. intros F fc LEAVES pc r m H. nexists pc, r, m. split; [reflexivity| exact H]. Qed.

Lemma unsigned_zb : ltac2:(zQ "60!h9!jja!ik6!ht2!ji5!qc>1x@1$5@1$0#8@3$2$3@2$1@1$0#k0@2$4@1$0#k0@2$1@1$0#8^1@2$1@1$0#8^1").
Proof. intros x. pose proof (bv_unsigned_in_range _ x) as R. unfold bv_modulus in R; cbn in R. apply unsigned_lit. lia. Qed.

(* [comment removed for export] *)
Ltac hide_post := lazymatch goal with |- evt _ ?P _ => set (SEGPOST := P) end.
Ltac unhide_post := try match goal with P := _ : machine_state -> Prop |- _ => subst P end.
(* [comment removed for export] *)
Ltac prune_or K tac :=
  lazymatch type of K with
  | boxP _ => tac
  | _ => first [ exfalso; lia | tac ]
  end.

Ltac print_hyps :=
  try (match goal with H : ?T |- _ =>
         lazymatch T with
         | rw_cells _ _ _ _ => idtac "  " H ":" T
         | ro_cells _ _ _ _ => idtac "  " H ":" T
         | @eq Z _ _ => idtac "  " H ":" T
         | Z.lt _ _ => idtac "  " H ":" T
         | Z.le _ _ => idtac "  " H ":" T
         | not _ => idtac "  " H ":" T
         | _ /\ _ => idtac "  " H ":" T
         | munch _ _ _ => idtac "  " H ":" T
         | stk _ _ _ _ => idtac "  " H ":" T
         | _ => fail
         end; fail end).
Ltac print_leaf :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ ?pc _ _ ?m _) => idtac "=== LEAF pc=" pc "mem=" m; let r := rv_of R in idtac r; print_hyps
  end.
Ltac explore stops :=
  run_to stops;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch stops with
      | context [pc] => print_leaf; apply evt_done; unhide_post; exact I
      | _ => idtac "=== STUCK at" pc; print_leaf
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; box_ugly K;
      [ prune_or K ltac:(explore stops) | prune_or K ltac:(explore stops) ]
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => idtac "=== LEAF (nonliteral pc)" pc; print_leaf; apply evt_done; unhide_post; exact I
  end.

Ltac rv_cbv := cbv beta iota delta [rra rsp rgp rtp rt0 rt1 rt2 rs0 rs1 ra0 ra1 ra2 ra3 ra4 ra5 ra6 ra7
                                   rs2 rs3 rs4 rs5 rs6 rs7 rs8 rs9 rs10 rs11 rt3 rt4 rt5 rt6].
(* [comment removed for export] *)
Ltac fin_arith := first [ lia | rewrite ?unsigned_lit by lia; lia ].
Ltac fin_atom :=
  first [ eassumption
        | reflexivity
        | lazymatch goal with
          | |- @eq Z _ _ => rv_cbv; fin_arith
          | |- (_ <= _)%Z => rv_cbv; fin_arith
          | |- (_ < _)%Z => rv_cbv; fin_arith
          | |- not _ => rv_cbv; fin_arith
          | |- @eq _ _ _ => rv_cbv; first [ reflexivity | eassumption | f_equal; lia | apply bv_eq; rewrite ?unsigned_lit by lia; lia ]
          | |- _ => rv_cbv; first [ reflexivity | eassumption ]
          end ].
(* [comment removed for export] *)
Ltac seg_unfold := fail.
(* [comment removed for export] *)
Ltac unfold_rvl := try (match goal with r := _ : rv |- _ => subst r end).
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac fin_conj :=
  lazymatch goal with
  | |- ex _ => eexists; fin_conj
  | |- _ /\ _ => first [ nsplit | split ]; fin_conj
  | |- _ => unfold_rvl; first [ fin_atom | seg_unfold; fin_conj ]
  end.
Ltac fin_leaf1 := first [ nsplit | split ]; [ reflexivity | fin_conj .. ].
Ltac fin_leaves :=
  lazymatch goal with
  | |- _ \/ _ => first [ or_pick ltac:(fin_leaf1)
                        | first [ split; [reflexivity|]; fin_conj | left; split; [reflexivity|]; fin_conj | right; fin_leaves ] ]
  | |- _ => first [ fin_leaf1 | split; [reflexivity|]; fin_conj ]
  end.
(* [comment removed for export] *)
Ltac fin_leaf_with r :=
  let rl := fresh "rvl" in
  pose (rl := r);
  first [ eapply (seg_post_intro _ _ _ _ rl _);
          (let G := lazymatch goal with |- ?G => G end in let G' := eval cbv beta in G in change G')
        | eexists; exists rl; eexists; split; [reflexivity|] ];
  fin_leaves.
Ltac fin_leaf :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let r := rv_of R in apply evt_done; unhide_post; fin_leaf_with r
  end.
Ltac fin_leaf_ret :=
  lazymatch goal with
  | |- evt _ _ (MS ?R _ _ _ _ _ _) =>
      let r := rv_of R in apply evt_done; unhide_post; fin_leaf_with r
  end.
Ltac explore2 stops :=
  run_to stops;
  lazymatch goal with
  | |- evt _ _ (MS _ _ (Z_to_bv 64 ?pc) _ _ _ _) =>
      lazymatch stops with
      | context [pc] => first [fin_leaf | idtac "=== FINISHER FAILED at" pc; print_leaf]
      | _ => idtac "=== STUCK at" pc; print_leaf
      end
  | |- evt _ _ (MS _ _ (if _ then _ else _) _ _ _ _) =>
      let K := fresh "K" in if_cases K; zify_cond K; try rewrite !unsigned_zb in K; box_ugly K;
      [ prune_or K ltac:(explore2 stops) | prune_or K ltac:(explore2 stops) ]
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => first [fin_leaf_ret | idtac "=== FINISHER FAILED at (nonliteral)" pc; print_leaf]
  end.
(* [comment removed for export] *)
