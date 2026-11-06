(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qnhz.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qnhz.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QsRG.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QsRG. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QO3A.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QO3A. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Q7m0.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Q7m0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QSpR.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QSpR.Mq4. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QuJV.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QuJV. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QCPB.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QCPB.Mq0. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QH7x.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QH7x.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QEpW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QEpW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbrW.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbrW. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QZDE.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QZDE. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QbVh.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QbVh. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QWxq_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QWxq_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QlEo_c1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QlEo_c1. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QXup.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QXup.
From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qio9.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qio9. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require QHXC.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import QHXC. From OSSVerify.Proofs.json_c.json_object_fuzzer.lib Require Qfe5.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache. Import Qfe5.
Import ListNotations.
Import SX2. Import SX2S.
Open Scope Z_scope.

Definition harvested (P : Prop) : Prop := P.

Ltac index_of w VALS :=
lazymatch VALS with
| w :: _ => constr:(O)
| _ :: ?rest => let i := index_of w rest in constr:(S i)
end.

Ltac has_atom w VALS :=
lazymatch VALS with
| w :: _ => idtac
| _ :: ?rest => has_atom w rest
end.

Ltac add_atom w VALS :=
match VALS with
| _ => let _ := match goal with _ => has_atom w VALS end in VALS
| _ => let r := eval cbn [app] in (VALS ++ [w])%list in r
end.

Ltac collect_Z VALS t :=
lazymatch t with
| Z.add ?a ?k =>
lazymatch k with
| Z0 => collect_Z VALS a | Zpos _ => collect_Z VALS a | Zneg _ => collect_Z VALS a
| _ => let V1 := collect_Z VALS a in collect_Z V1 k
end
| Z.sub ?a ?k =>
lazymatch k with
| Z0 => collect_Z VALS a | Zpos _ => collect_Z VALS a | Zneg _ => collect_Z VALS a
| _ => add_atom (Z_to_bv 64 t) VALS
end
| @bv_unsigned 64 ?w => collect_W VALS w
| Z0 => VALS | Zpos _ => VALS | Zneg _ => VALS
| _ => add_atom (Z_to_bv 64 t) VALS
end
with collect_W VALS w :=
lazymatch w with
| Z_to_bv 64 ?t => collect_Z VALS t
| wa ?t => collect_Z VALS t
| _ => add_atom w VALS
end.

Ltac reify_Z VALS t :=
lazymatch t with
| Z.add ?a ?k =>
lazymatch k with
| Z0 => reify_Z VALS a
| Zpos _ => let e := reify_Z VALS a in constr:(EAlu ALU_ADD e (ELit k))
| Zneg _ => let e := reify_Z VALS a in constr:(EAlu ALU_ADD e (ELit k))
| _ => let e1 := reify_Z VALS a in let e2 := reify_Z VALS k in constr:(EAlu ALU_ADD e1 e2)
end
| Z.sub ?a ?k =>
lazymatch k with
| Z0 => reify_Z VALS a
| Zpos _ => let e := reify_Z VALS a in let nk := eval vm_compute in (- k) in constr:(EAlu ALU_ADD e (ELit nk))
| Zneg _ => let e := reify_Z VALS a in let nk := eval vm_compute in (- k) in constr:(EAlu ALU_ADD e (ELit nk))
| _ => let i := index_of (Z_to_bv 64 t) VALS in constr:(EVar i)
end
| @bv_unsigned 64 ?w => reify_W VALS w
| Z0 => constr:(ELit t) | Zpos _ => constr:(ELit t) | Zneg _ => constr:(ELit t)
| _ => let i := index_of (Z_to_bv 64 t) VALS in constr:(EVar i)
end
with reify_W VALS w :=
lazymatch w with
| Z_to_bv 64 ?t => reify_Z VALS t
| wa ?t => reify_Z VALS t
| _ => let i := index_of w VALS in constr:(EVar i)
end.

Ltac reify_addr VALS t :=
lazymatch t with
| Z.add ?a ?k =>
lazymatch k with
| Zpos _ => let e := reify_Z VALS a in constr:(SA e k)
| Zneg _ => let e := reify_Z VALS a in constr:(SA e k)
| Z0 => let e := reify_Z VALS a in constr:(SA e 0)
| _ => let e := reify_Z VALS t in constr:(SA e 0)
end
| Z.sub ?a ?k =>
lazymatch k with
| Zpos _ => let e := reify_Z VALS a in let nk := eval vm_compute in (- k) in constr:(SA e nk)
| _ => let e := reify_Z VALS t in constr:(SA e 0)
end
| Z0 => constr:(SA (ELit 0) t) | Zpos _ => constr:(SA (ELit 0) t)
| _ => let e := reify_Z VALS t in constr:(SA e 0)
end.

Ltac goal_mem := lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?m _) => m end.
Ltac goal_segs := lazymatch goal with |- evt ?segs _ _ => segs end.

Ltac collect_regs VALS :=
lazymatch goal with
| |- evt _ _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16
?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
let V := collect_W VALS x2 in
let V := collect_W V x1 in let V := collect_W V x3 in let V := collect_W V x4 in
let V := collect_W V x5 in let V := collect_W V x6 in let V := collect_W V x7 in let V := collect_W V x8 in
let V := collect_W V x9 in let V := collect_W V x10 in let V := collect_W V x11 in let V := collect_W V x12 in
let V := collect_W V x13 in let V := collect_W V x14 in let V := collect_W V x15 in let V := collect_W V x16 in
let V := collect_W V x17 in let V := collect_W V x18 in let V := collect_W V x19 in let V := collect_W V x20 in
let V := collect_W V x21 in let V := collect_W V x22 in let V := collect_W V x23 in let V := collect_W V x24 in
let V := collect_W V x25 in let V := collect_W V x26 in let V := collect_W V x27 in let V := collect_W V x28 in
let V := collect_W V x29 in let V := collect_W V x30 in let V := collect_W V x31 in
V
end.

Ltac build_sr VALS :=
lazymatch goal with
| |- evt _ _ (MS (mkR ?x1 ?x2 ?x3 ?x4 ?x5 ?x6 ?x7 ?x8 ?x9 ?x10 ?x11 ?x12 ?x13 ?x14 ?x15 ?x16
?x17 ?x18 ?x19 ?x20 ?x21 ?x22 ?x23 ?x24 ?x25 ?x26 ?x27 ?x28 ?x29 ?x30 ?x31) _ _ _ _ _ _) =>
let e1 := reify_W VALS x1 in let e2 := reify_W VALS x2 in let e3 := reify_W VALS x3 in let e4 := reify_W VALS x4 in
let e5 := reify_W VALS x5 in let e6 := reify_W VALS x6 in let e7 := reify_W VALS x7 in let e8 := reify_W VALS x8 in
let e9 := reify_W VALS x9 in let e10 := reify_W VALS x10 in let e11 := reify_W VALS x11 in let e12 := reify_W VALS x12 in
let e13 := reify_W VALS x13 in let e14 := reify_W VALS x14 in let e15 := reify_W VALS x15 in let e16 := reify_W VALS x16 in
let e17 := reify_W VALS x17 in let e18 := reify_W VALS x18 in let e19 := reify_W VALS x19 in let e20 := reify_W VALS x20 in
let e21 := reify_W VALS x21 in let e22 := reify_W VALS x22 in let e23 := reify_W VALS x23 in let e24 := reify_W VALS x24 in
let e25 := reify_W VALS x25 in let e26 := reify_W VALS x26 in let e27 := reify_W VALS x27 in let e28 := reify_W VALS x28 in
let e29 := reify_W VALS x29 in let e30 := reify_W VALS x30 in let e31 := reify_W VALS x31 in
constr:([ELit 0; e1; e2; e3; e4; e5; e6; e7; e8; e9; e10; e11; e12; e13; e14; e15; e16;
e17; e18; e19; e20; e21; e22; e23; e24; e25; e26; e27; e28; e29; e30; e31]%list)
end.

Ltac collect_cells VALS cs :=
lazymatch cs with
| [] => VALS
| C8 ?v :: ?rest => let V := collect_W VALS v in collect_cells V rest
| C4 ?v :: ?rest => let V := collect_W VALS v in collect_cells V rest
| C2 ?v :: ?rest => let V := collect_W VALS v in collect_cells V rest
| C1 (Z_to_bv 8 Z0) :: ?rest => collect_cells VALS rest
| C1 (Z_to_bv 8 (Zpos _)) :: ?rest => collect_cells VALS rest
| C1 ?b :: ?rest => let V := collect_W VALS (Z_to_bv 64 (bv_unsigned b)) in collect_cells V rest
| CB _ _ :: ?rest => collect_cells VALS rest
end.

Ltac collect_hyps VALS m :=
match goal with
| H : rw_cells ?segs m ?A ?cs |- _ =>
let V := collect_Z VALS A in let V := collect_cells V cs in
let _ := match goal with _ => change (rw_cells segs m A cs) with (harvested (rw_cells segs m A cs)) in H end in
collect_hyps V m
| H : ro_cells ?segs m ?A ?cs |- _ =>
let V := collect_Z VALS A in let V := collect_cells V cs in
let _ := match goal with _ => change (ro_cells segs m A cs) with (harvested (ro_cells segs m A cs)) in H end in
collect_hyps V m
| H : bytes_at ?segs m ?A (le8 ?v) |- _ =>
let V := collect_Z VALS A in let V := collect_W V v in
let _ := match goal with _ => change (bytes_at segs m A (le8 v)) with (harvested (bytes_at segs m A (le8 v))) in H end in
collect_hyps V m
| H : bytes_at ?segs m ?A (le4 ?v) |- _ =>
let V := collect_Z VALS A in let V := collect_W V v in
let _ := match goal with _ => change (bytes_at segs m A (le4 v)) with (harvested (bytes_at segs m A (le4 v))) in H end in
collect_hyps V m
| _ => let _ := match goal with _ => unfold harvested in * end in VALS
end.

Ltac kn_cells VALS base d k cs acc :=
lazymatch cs with
| [] => acc
| ?c :: ?rest =>
let k' := eval vm_compute in (k + Z.of_nat (csize c))%Z in
let off := eval vm_compute in (d + k)%Z in
lazymatch c with
| C8 ?v => let e := reify_W VALS v in kn_cells VALS base d k' rest constr:((KWord (SA base off) 8 e :: acc)%list)
| C4 ?v => let e := reify_W VALS v in kn_cells VALS base d k' rest constr:((KWord (SA base off) 4 e :: acc)%list)
| C2 ?v => let e := reify_W VALS v in kn_cells VALS base d k' rest constr:((KWord (SA base off) 2 e :: acc)%list)
| C1 (Z_to_bv 8 ?z) =>
let e := lazymatch z with
| Z0 => constr:(ELit 0) | Zpos _ => constr:(ELit z)
| _ => reify_W VALS (Z_to_bv 64 (bv_unsigned (Z_to_bv 8 z))) end in
kn_cells VALS base d k' rest constr:((KWord (SA base off) 1 e :: acc)%list)
| C1 ?b => let e := reify_W VALS (Z_to_bv 64 (bv_unsigned b)) in kn_cells VALS base d k' rest constr:((KWord (SA base off) 1 e :: acc)%list)
| CB _ _ => kn_cells VALS base d k' rest acc
end
end.

Ltac kn_hyps VALS m acc :=
match goal with
| H : rw_cells ?segs m ?A ?cs |- _ =>
let sa := reify_addr VALS A in
lazymatch sa with SA ?base ?d =>
let n := eval cbv beta iota zeta delta [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat (cells_size cs)) in
let acc1 := lazymatch n with
| Zpos _ => kn_cells VALS base d 0%Z cs constr:((KWr (SA base d) n :: acc)%list)
| _ => acc
end in
let _ := match goal with _ => change (rw_cells segs m A cs) with (harvested (rw_cells segs m A cs)) in H end in
kn_hyps VALS m acc1
end
| H : ro_cells ?segs m ?A ?cs |- _ =>
let sa := reify_addr VALS A in
lazymatch sa with SA ?base ?d =>
let n := eval cbv beta iota zeta delta [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in (Z.of_nat (cells_size cs)) in
let acc1 := lazymatch n with
| Zpos _ => kn_cells VALS base d 0%Z cs acc
| _ => acc
end in
let _ := match goal with _ => change (ro_cells segs m A cs) with (harvested (ro_cells segs m A cs)) in H end in
kn_hyps VALS m acc1
end
| H : bytes_at ?segs m ?A (le8 ?v) |- _ =>
let sa := reify_addr VALS A in let e := reify_W VALS v in
lazymatch sa with SA ?base ?d =>
let _ := match goal with _ => change (bytes_at segs m A (le8 v)) with (harvested (bytes_at segs m A (le8 v))) in H end in
kn_hyps VALS m constr:((KWord (SA base d) 8 e :: acc)%list)
end
| H : bytes_at ?segs m ?A (le4 ?v) |- _ =>
let sa := reify_addr VALS A in let e := reify_W VALS v in
lazymatch sa with SA ?base ?d =>
let _ := match goal with _ => change (bytes_at segs m A (le4 v)) with (harvested (bytes_at segs m A (le4 v))) in H end in
kn_hyps VALS m constr:((KWord (SA base d) 4 e :: acc)%list)
end
| _ => let _ := match goal with _ => unfold harvested in * end in acc
end.

Fixpoint ro_kimgs (sl : list Segment) : list kentry :=
match sl with
| [] => []
| s :: rest => if seg_writable s then ro_kimgs rest
else KImg (Z.of_N (seg_base s)) (Z.of_N (seg_base s) + Z.of_N (seg_size s)) :: ro_kimgs rest
end.

Ltac kn_img segs m acc :=
match goal with
| MI : mem_inv segs m |- _ => let l := eval vm_compute in (ro_kimgs segs) in eval cbn [app] in (l ++ acc)%list
| _ => acc
end.

Ltac den_cbn := cbn [nthe nth edenot ev eb vals_ev blobs_ev a_base a_off].

Ltac den_norm :=
repeat first [ rewrite den_sub_lin | rewrite den_sub_lin2 | rewrite den_not | rewrite den_add_zl | rewrite den_add_wl ];
rewrite ?Z_to_bv_add0, ?Z_to_bv_of_word.

Ltac solve_den := den_cbn; den_norm; first [ reflexivity | apply bv_eq; rewrite ?Z_to_bv_unsigned; reflexivity | fail 1 "solve_den: cannot prove" ].

Ltac prove_regs_ok :=
eapply regs_ok_mkR; [ reflexivity | solve_den .. ].

Ltac norm_uz :=
repeat match goal with
| |- context [bv_unsigned (Z_to_bv 64 ?z)] => rewrite (u64_of_Z z) by lia
end.

Ltac addr_diff2 E A :=
match goal with
| _ => let _ := match goal with _ => constr_eq E A end in constr:(0%Z)
| _ => addr_diff E A
end.

Ltac zterm_of_atom w := lazymatch w with Z_to_bv 64 ?z => z | _ => constr:(bv_unsigned w) end.

Ltac zform VALS e :=
lazymatch e with
| ELit ?z => z
| EVar ?i => let w := eval cbv beta iota delta [nth vals_ev] in (nth i VALS (Z_to_bv 64 0)) in zterm_of_atom w
| EAlu ALU_ADD ?a ?b =>
let za := zform VALS a in let zb := zform VALS b in
lazymatch za with Z0 => zb | _ => lazymatch zb with Z0 => za | _ => constr:((za + zb)%Z) end end
end.

Ltac zaddr_of base off :=

lazymatch base with
| Z_to_bv 64 ?z =>
lazymatch z with
| Z0 => off
| Zpos _ => let r := eval vm_compute in (z + off) in r
| _ => lazymatch off with Z0 => z | _ => constr:(z + off) end
end
| _ => lazymatch off with Z0 => constr:(bv_unsigned base) | _ => constr:(bv_unsigned base + off) end
end.

Ltac base_word VALS E base :=
lazymatch base with
| EVar _ => let w := eval cbn [nthe nth edenot ev eb vals_ev blobs_ev] in (edenot E base) in w
| ELit ?z => constr:(Z_to_bv 64 z)
| _ => let z := zform VALS base in constr:(Z_to_bv 64 z)
end.

Ltac base_eq := first [ reflexivity | rewrite Z.add_0_r; reflexivity | norm_uz; first [ reflexivity | ring | lia ] ].

Ltac base_den := den_cbn; den_norm; first [ reflexivity | rewrite Z_to_bv_of_word; reflexivity ].
Ltac w_bounds := cbv; split; repeat constructor.

Ltac kentry_solve segs :=
den_cbn;
lazymatch goal with
| |- kentry_ok _ ?E ?m (KImg ?lo ?hi) =>
lazymatch goal with MI : mem_inv segs m |- _ =>
apply (kimg_of_mem_inv segs E m lo hi MI); [vm_compute; reflexivity | lia | lia] end
| |- kentry_ok _ ?E ?m (KRange ?e ?lo ?hi) =>
eapply (krange_of segs E m e); [den_cbn; reflexivity | ]; den_cbn;
match goal with |- _ <= bv_unsigned ?w <= _ => pose proof (u64_range w) end; norm_uz; lia
| |- kentry_ok _ ?E ?m (KAlign ?e ?k) =>
eapply (kalign_of segs E m e); [den_cbn; reflexivity | lia | norm_uz; first [assumption | lia] ]
| |- kentry_ok _ ?E ?m (KWr (SA ?base ?d) ?n) =>
let VALS := lazymatch E with Env (vals_ev ?V) _ => V end in
let bd := base_word VALS E base in
let za := zaddr_of bd d in
match goal with
| H : rw_cells segs m ?A ?cs |- _ =>
let k := addr_diff2 za A in
lazymatch k with 0%Z =>
eapply (kwr_of_rw segs E m base bd d A cs n H);
[ base_den | base_eq | cells_cbv; reflexivity | apply Z.ltb_lt; reflexivity ]
end
| ST : stk segs m ?lo ?hi |- _ =>
eapply (kwr_of_stk segs E m base bd lo hi d n ST); [ base_den | norm_uz; lia | lia | norm_uz; lia ]
end
| |- kentry_ok _ ?E ?m (KWord (SA ?base ?off) ?w ?v) =>
let VALS := lazymatch E with Env (vals_ev ?V) _ => V end in
let bd := base_word VALS E base in
let za := zaddr_of bd off in
match goal with
| H : rw_cells segs m ?A ?cs |- _ =>
let k := addr_diff2 za A in
let kn := eval vm_compute in (Z.to_nat k) in
let d := eval vm_compute in (off - k) in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
eapply (kword_of_rw segs E m base bd d A cs kn c0 w v _ H);
[ cells_cbv; reflexivity | base_den | base_eq | reflexivity
| cbn [cbytes]; rewrite <- ?cbytes_C8, <- ?cbytes_C4, <- ?cbytes_C2, <- ?cbytes_C1; reflexivity
| solve_den | w_bounds ]
end
| H : ro_cells segs m ?A ?cs |- _ =>
let k := addr_diff2 za A in
let kn := eval vm_compute in (Z.to_nat k) in
let d := eval vm_compute in (off - k) in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
eapply (kword_of_ro segs E m base bd d A cs kn c0 w v _ H);
[ cells_cbv; reflexivity | base_den | base_eq | reflexivity
| cbn [cbytes]; rewrite <- ?cbytes_C8, <- ?cbytes_C4, <- ?cbytes_C2, <- ?cbytes_C1; reflexivity
| solve_den | w_bounds ]
end
| H : bytes_at segs m ?A ?bs |- _ =>
let k := addr_diff2 za A in
lazymatch k with 0%Z =>
eapply (kword_of_bytes_at segs E m base bd off A bs w v _ H);
[ cbv delta [le8 le4 le2]; reflexivity | base_den | base_eq | solve_den | w_bounds ]
end
end
end.

Ltac prove_know_ok segs :=
repeat (apply Forall_cons; [ kentry_solve segs | ]); apply Forall_nil.

Definition segs_top (sl : list Segment) : Z :=
fold_right (fun s acc => Z.max acc (Z.of_N (seg_base s) + Z.of_N (seg_size s))) 0 sl.

Ltac kn_sp_range2 segs VALS acc :=
let x2 := lazymatch goal with |- evt _ _ (MS (mkR _ ?x2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) _ _ _ _ _ _) => x2 end in
let e2 := reify_W VALS x2 in
let base := lazymatch e2 with EAlu ALU_ADD ?b (ELit _) => b | _ => e2 end in
lazymatch base with
| EVar ?i =>
let spw := eval cbv beta iota delta [nth] in (nth i VALS (Z_to_bv 64 0)) in
let top := eval vm_compute in (segs_top segs) in
let ok := match goal with
| _ => let _ := match goal with _ =>
let H := fresh in
assert (H : top <= bv_unsigned spw <= 18446744073709551615) by (pose proof (u64_range spw); lia); clear H end in
constr:(true)
| _ => constr:(false)
end in
lazymatch ok with
| true => constr:((KRange (EVar i) top 18446744073709551615 :: acc)%list)
| false => acc
end
| _ => acc
end.

Ltac kn_ranges VALS i acc :=
lazymatch VALS with
| [] => acc
| ?w :: ?rest =>
let z := zterm_of_atom w in
let i' := constr:(S i) in
let acc' :=
match goal with
| H : (?lo <= z < ?hi)%Z |- _ =>
let lo' := zlit lo in let hi' := zlit hi in let h := eval vm_compute in (hi' - 1)%Z in
constr:((KRange (EVar i) lo' h :: acc)%list)
| H : (?lo <= z <= ?hi)%Z |- _ =>
let lo' := zlit lo in let hi' := zlit hi in constr:((KRange (EVar i) lo' hi' :: acc)%list)
| H : (?lo <= z)%Z, H' : (z < ?hi)%Z |- _ =>
let lo' := zlit lo in let hi' := zlit hi in let h := eval vm_compute in (hi' - 1)%Z in
constr:((KRange (EVar i) lo' h :: acc)%list)
| H : (?lo <= z)%Z, H' : (z <= ?hi)%Z |- _ =>
let lo' := zlit lo in let hi' := zlit hi in constr:((KRange (EVar i) lo' hi' :: acc)%list)
| _ => acc
end in
kn_ranges rest i' acc'
end.

Ltac word_ranges VALS :=
lazymatch VALS with
| [] => idtac
| ?w :: ?rest => (lazymatch w with Z_to_bv 64 _ => idtac | _ => try (pose proof (u64_range w)) end); word_ranges rest
end.

Ltac pose_bv_ranges :=
repeat match goal with
| |- context [@bv_unsigned ?n ?x] =>
lazymatch x with Z_to_bv _ _ => fail | _ => idtac end;
lazymatch goal with
| _ : (0 <= @bv_unsigned n x < _)%Z |- _ => fail
| _ => let H := fresh "BR" in
pose proof (bv_unsigned_in_range n x) as H; unfold bv_modulus in H;
let v := eval vm_compute in (2 ^ Z.of_N n)%Z in change (2 ^ Z.of_N n)%Z with v in H
end
end.

Ltac sc_cbn := cbv beta iota zeta delta [sc_denot flat estart elenZ elen adenot a_base a_off edenot ev eb vals_ev blobs_ev nth branch_taken].

Ltac sc_readbase :=
lazymatch goal with
| |- exists bs, ?f ?segs ?m ?a 1%nat = Some bs /\ Z_to_bv 64 (extz false 1 _) = Z_to_bv 64 (bv_unsigned ?b) =>
match goal with
| H : bytes_at segs m ?A ?bsrc |- _ =>
eapply (sc_readbase_byte segs m A bsrc _ b a H);
[ first [ eassumption | reflexivity | cbn; reflexivity ]
| cbv beta delta [QsRG.Mq0.v_addi]; pose_bv_ranges;
rewrite ?u64_of_Z by lia; unfold wa; f_equal; lia ]
end
end.

Ltac sc_solve :=
sc_cbn; den_norm;
try sc_readbase;
unfold bv_eqb, bv_ltu, bv_lts, bv_leu; cbn [negb];
pose_bv_ranges;
fold_lit_ux; rewrite ?u64_of_Z by lia; rewrite ?s64_of_Z by lia;
first [ lia
| solve_cond_rec
| match goal with |- _ /\ _ => repeat split; lia end ].

Ltac expose_regs :=
lazymatch goal with
| |- evt _ _ (MS (mkRv ?E ?sr) _ _ _ _ _ _) =>
let g i := eval vm_compute in (sr_get sr (Z_to_bv 5 i)) in
let e1 := g 1 in let e2 := g 2 in let e3 := g 3 in let e4 := g 4 in let e5 := g 5 in
let e6 := g 6 in let e7 := g 7 in let e8 := g 8 in let e9 := g 9 in let e10 := g 10 in
let e11 := g 11 in let e12 := g 12 in let e13 := g 13 in let e14 := g 14 in let e15 := g 15 in
let e16 := g 16 in let e17 := g 17 in let e18 := g 18 in let e19 := g 19 in let e20 := g 20 in
let e21 := g 21 in let e22 := g 22 in let e23 := g 23 in let e24 := g 24 in let e25 := g 25 in
let e26 := g 26 in let e27 := g 27 in let e28 := g 28 in let e29 := g 29 in let e30 := g 30 in
let e31 := g 31 in
change (mkRv E sr) with
(mkR (edenot E e1) (edenot E e2) (edenot E e3) (edenot E e4) (edenot E e5) (edenot E e6) (edenot E e7) (edenot E e8)
(edenot E e9) (edenot E e10) (edenot E e11) (edenot E e12) (edenot E e13) (edenot E e14) (edenot E e15) (edenot E e16)
(edenot E e17) (edenot E e18) (edenot E e19) (edenot E e20) (edenot E e21) (edenot E e22) (edenot E e23) (edenot E e24)
(edenot E e25) (edenot E e26) (edenot E e27) (edenot E e28) (edenot E e29) (edenot E e30) (edenot E e31))
end.

Ltac val_norm :=
den_norm;

rewrite ?QsjA.w_addw, ?QsjA.w_subw;

repeat (rewrite ext_val_sx_id by (first [ cbn; lia | cbn; pose_bv_ranges; rewrite ?u64_of_Z by lia; lia ]));
repeat (rewrite ext_val_zx_id by (cbn; pose_bv_ranges; rewrite ?u64_of_Z by lia; lia));
vnorm;
repeat (rewrite u64_of_Z by (pose_bv_ranges; lia));
rewrite ?swrap32_id by (pose_bv_ranges; lia).

Ltac innermost_write t :=
lazymatch t with
| write_to_mem ?m ?a ?bs =>
lazymatch m with
| write_to_mem _ _ _ => innermost_write m
| _ => t
end
end.

Ltac cell_of_wbytes bs :=
lazymatch bs with
| word_to_le_bytes 8 ?v => constr:(C8 v)
| word_to_le_bytes 4 ?v => constr:(C4 v)
| word_to_le_bytes 2 ?v => constr:(C2 v)
| word_to_le_bytes 1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
| le8 ?v => constr:(C8 v)
| le4 ?v => constr:(C4 v)
| le2 ?v => constr:(C2 v)
| [?b]%list => constr:(C1 b)
end.

Lemma w2le_1 : forall v : word, word_to_le_bytes 1 v = [Z_to_bv 8 (bv_unsigned v)]%list.
Proof. reflexivity. Qed.

Ltac fold_store1 segs m a bs :=
let za := lazymatch a with
| v_addi ?base ?off => zaddr_of base off
| Z_to_bv 64 ?z => z
| wa ?z => z
end in
let c' := cell_of_wbytes bs in
let n := eval cbv in (csize c') in
match goal with
| H : rw_cells segs m ?A ?cs0 |- _ =>
let k := addr_diff2 za A in
let kn := eval vm_compute in (Z.to_nat k) in
(lazymatch k with Zneg _ => fail | _ => idtac end);
split_for_access H segs m A cs0 kn n;
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let c := eval_cell_at cs kn in
lazymatch c with Some ?c0 =>
replace (write_to_mem m a bs) with (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c'))
by (f_equal; first [ reflexivity | unfold wa; f_equal; rewrite ?u64_of_Z by lia; lia | cbn [cbytes]; rewrite ?w2le_1; reflexivity ]);
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (mem_inv_store_cbytes segs m (wa (A + Z.of_nat kn)) c') in HI;
[ | exact I | apply (rw_cells_store_ok segs m A cs kn c0 _ H); [cells_cbv; reflexivity | reflexivity] ]
end;
let H' := fresh "CH" in
pose proof (rw_cells_write segs m A cs kn c0 c' H ltac:(cells_cbv; reflexivity) ltac:(reflexivity) I) as H';
clear H;
cbv beta iota zeta delta [cell_upd csize Nat.eqb Nat.sub] in H';
transport_chunks segs m (A + Z.of_nat kn)%Z (cbytes c');
footprint_after_store segs m (A + Z.of_nat kn)%Z (cbytes c');
let m' := fresh "m" in
remember (write_to_mem m (wa (A + Z.of_nat kn)) (cbytes c')) as m' eqn:Heqm;
clear Heqm; clear HB; try clear m; try rename H' into H
end
end.

Ltac chain_collect t acc n :=
lazymatch t with
| write_to_mem ?m (Z_to_bv 64 ?a) ?bs => chain_collect m constr:(@cons (Z * list byte) (a, bs) acc) constr:(S n)
| write_to_mem ?m (wa ?a) ?bs => chain_collect m constr:(@cons (Z * list byte) (a, bs) acc) constr:(S n)
| _ => constr:((t, acc, n))
end.

Ltac chain_descend t d :=
lazymatch d with
| O => t
| S ?d' => lazymatch t with write_to_mem ?m _ _ => chain_descend m d' end
end.

Ltac with_target segs m za tac :=
match goal with
| H : rw_cells segs m ?A ?cs |- _ =>
let k := addr_diff2 za A in
(lazymatch k with Zneg _ => fail | _ => idtac end);
let sz := eval vm_compute in (Z.of_nat (cells_size cs)) in
let inb := eval vm_compute in (Z.ltb k sz) in
(lazymatch inb with true => idtac end);
tac H A cs k
end.

Ltac batch_prefix segs m H A ws :=
lazymatch ws with
| ((?a, ?bs) :: ?rest)%list =>
match goal with
| _ =>
let k := addr_diff2 a A in
let _ := match goal with _ => lazymatch k with Zneg _ => fail | _ => idtac end end in
let cs := lazymatch type of H with rw_cells _ _ _ ?cs => cs end in
let sz := eval vm_compute in (Z.of_nat (cells_size cs)) in
let inb := eval vm_compute in (Z.ltb k sz) in
let _ := match goal with _ => lazymatch inb with true => idtac end end in
let kn := eval vm_compute in (Z.to_nat k) in
let c := cell_of_wbytes bs in
let r := batch_prefix segs m H A rest in
lazymatch r with
| (?pre, ?ts, ?n) => constr:((@cons (Z * list byte) (a, bs) pre, @cons wtag (@Some (nat * cell) (kn, c)) ts, S n))
end
| _ => constr:((@nil (Z * list byte), @nil wtag, O))
end
| _ => constr:((@nil (Z * list byte), @nil wtag, O))
end.

Ltac cells_apply_cbv :=
cbv beta iota zeta delta [cells_apply cb_split cb_split_ok cb_pieces cell_at cell_upd csize cells_size cell_wfb
Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add Nat.min Nat.max andb app tags_hull].

Ltac prove_off :=
first [ reflexivity
| apply off_eq; reflexivity | apply off_eq0; reflexivity
| apply off_eqA; reflexivity | apply off_eq00; reflexivity
| lia ].

Ltac prove_wmatch :=
cbn [wmatch];
repeat lazymatch goal with
| |- _ /\ _ => split
| |- True => exact I
| |- _ = _ + Z.of_nat ?k => let kz := eval vm_compute in (Z.of_nat k) in change (Z.of_nat k) with kz; prove_off
| |- _ = cbytes _ => cbn [cbytes]; rewrite ?w2le_1; reflexivity
end.

Ltac transport_batch segs m ws WIN l h :=
repeat match goal with
| Hb : bytes_at segs m ?A2 ?bs2 |- _ =>
first [ let D := fresh "D" in
assert (D : wdisj A2 (Z.of_nat (length bs2)) ws)
by (eapply (wdisj_of_hull ws l h); [exact WIN | lia | lia | simpl_sizes; slia]);
apply (fun X => bytes_at_apply segs ws m A2 bs2 X D) in Hb; clear D
| idtac "note: dropping hypothesis (not provably disjoint from the block's stores):" Hb; clear Hb ]
| Hb : rw_cells segs m ?A2 ?cs2 |- _ =>
first [ let D := fresh "D" in
assert (D : wdisj A2 (Z.of_nat (cells_size cs2)) ws)
by (eapply (wdisj_of_hull ws l h); [exact WIN | lia | lia | simpl_sizes; slia]);
apply (fun X => rw_cells_apply_frame segs ws m A2 cs2 X D) in Hb; clear D
| idtac "note: dropping hypothesis (not provably disjoint from the block's stores):" Hb; clear Hb ]
| Hb : ro_cells segs m ?A2 ?cs2 |- _ =>
first [ let D := fresh "D" in
assert (D : wdisj A2 (Z.of_nat (cells_size cs2)) ws)
by (eapply (wdisj_of_hull ws l h); [exact WIN | lia | lia | simpl_sizes; slia]);
apply (fun X => ro_cells_apply_frame segs ws m A2 cs2 X D) in Hb; clear D
| idtac "note: dropping hypothesis (not provably disjoint from the block's stores):" Hb; clear Hb ]
| Hb : wr_at segs m ?A2 ?n2 |- _ => apply (wr_at_apply segs ws m A2 n2) in Hb
| MU : munch ?Wq ?mq m |- _ =>
first [ apply (fun X => munch_apply ws Wq mq m l h X WIN) in MU; [ | lia | lia | cbn [inside]; lia ]
| fail 100 "batch store fold: block stores outside the declared footprint" ]
| WMo : wmono segs ?mq m |- _ => apply (wmono_apply segs ws mq m) in WMo
| STq : stk segs m ?loq ?hiq |- _ =>
first [ apply (fun X => stk_apply segs ws m loq hiq l h X WIN) in STq; [ | lia | lia ]
| fail 100 "batch store fold: cannot transport stk hypothesis" STq ]
end.

Ltac fold_batch1 segs :=
lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
let r := chain_collect mm constr:(@nil (Z * list byte)) O in
lazymatch r with
| (?m, ?wsall, ?nall) =>
lazymatch wsall with ((?a0, _) :: _)%list =>
with_target segs m a0 ltac:(fun H A cs k0 =>
let r2 := batch_prefix segs m H A wsall in
lazymatch r2 with
| (?ws, ?ts, ?n) =>
let d := eval vm_compute in (Nat.sub nall n) in
let sub := chain_descend mm d in
change sub with (apply_writes m ws);
let app := eval cbv beta iota zeta delta [cells_apply cb_split cb_split_ok cb_pieces cell_at cell_upd csize cells_size cell_wfb
Nat.eqb Nat.ltb Nat.leb Nat.sub Nat.add andb app] in (cells_apply cs ts) in
lazymatch app with
| Some ?cs' =>
let WM := fresh "WM" in
assert (WM : wmatch A (Z.of_nat (cells_size cs)) ws ts) by prove_wmatch;
let H' := fresh "CH" in
pose proof (rw_cells_apply segs ws ts m A cs cs' H WM ltac:(cells_apply_cbv; reflexivity)) as H';

let hl := eval cbv beta iota zeta delta [tags_hull csize Nat.min Nat.max Nat.add] in (tags_hull ts) in
lazymatch hl with
| Some (?lo, ?hi) =>
let loz := eval vm_compute in (Z.of_nat lo) in
let hiz := eval vm_compute in (Z.of_nat hi) in
let WIN := fresh "WIN" in
assert (WIN : writes_in ws (A + loz) (A + hiz))
by (change loz with (Z.of_nat lo); change hiz with (Z.of_nat hi);
apply (wmatch_hull ws ts A _ lo hi WM); [cells_apply_cbv; reflexivity | repeat constructor]);
let HB := fresh "HB" in
pose proof (rw_cells_bound segs m A cs H) as HB; cbn [cells_size csize Nat.add] in HB;
try lazymatch goal with
| HI : mem_inv segs m |- _ =>
apply (fun X => mem_inv_apply segs ws m A (Z.of_nat (cells_size cs)) (A + loz) (A + hiz) X
(rw_cells_wr_at segs m A cs H) WIN) in HI;
[ | lia | cbn [cells_size csize Nat.add]; lia ]
end;
clear H;
transport_batch segs m ws WIN (A + loz)%Z (A + hiz)%Z;
let m' := fresh "m" in let Heqm := fresh "Heqm" in
remember (apply_writes m ws) as m' eqn:Heqm;
clear Heqm WIN WM HB; try clear m; try rename H' into H
end
end
end)
end
end
end.

Ltac fold_log segs :=
change @wbytes with @write_to_mem;
cbv beta delta [QsRG.Mq0.v_addi];
rewrite ?unsigned_Z_to_bv_add;
repeat first
[ fold_batch1 segs
| lazymatch goal with
| |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
let w := innermost_write mm in
lazymatch w with write_to_mem ?m ?a ?bs => fold_store1 segs m a bs end
end ].

Lemma symb_block_k : forall segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2
(E : env) (M : word -> option byte) (F : bvmap 5 word) (fc : bv 32) R Q,
sym_exec segs fuel true stops scr (SS pc sr [] kn nx) [] = (ss', scs, scr') ->
carry (s_log ss') kn [] = (kn', scs2, hs2) ->
is_mkR R ->
regs_ok E sr R -> know_ok segs E M kn ->
(regs_ok E (s_regs ss') (mkRv E (s_regs ss')) ->
know_ok segs E (mem_denot E M (s_log ss')) kn' ->
log_flat E (s_log ss') ->
evt segs Q (MS (mkRv E (s_regs ss')) F (Z_to_bv 64 (s_pc ss')) fc None
(mem_denot E M (s_log ss')) (QsjA.seg_rom segs))) ->
scs_denot segs M E scs -> scs_denot segs M E scs2 ->
evt segs Q (MS R F (Z_to_bv 64 pc) fc None M (QsjA.seg_rom segs)).
Proof. intros. eapply symb_block; eassumption. Qed.

Ltac symb_run_core segs fuel stops scr extra :=
let m := goal_mem in
let V0 := collect_hyps constr:(@nil word) m in
let V1 := collect_regs V0 in
let V := eval cbn [app] in (V1 ++ extra)%list in
let nfresh := eval vm_compute in (length V1) in
let sr := build_sr V in
let kn0 := kn_hyps V m constr:(@nil kentry) in
let kn1 := kn_img segs m kn0 in
let kn2 := kn_sp_range2 segs V kn1 in
let kn := kn_ranges V O kn2 in
let nx := nfresh in
let E := constr:(Env (vals_ev V) (blobs_ev [])) in
lazymatch goal with
| |- evt _ ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None _ _) =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let c := eval vm_compute in (carry (s_log ss') kn []) in
lazymatch c with
| (?kn', ?scs2, ?hs2) =>
eapply (symb_block_k segs fuel stops scr pc sr kn nx ss' scs scr' kn' scs2 hs2 E m F fc R Q);
[ vm_cast_no_check (@eq_refl _ (ss', scs, scr'))
| vm_cast_no_check (@eq_refl _ (kn', scs2, hs2))
| apply is_mkR_mkR
| prove_regs_ok
| prove_know_ok segs
| let HR' := fresh "HRx" in let HK' := fresh "HKx" in let LF := fresh "LFx" in
intros HR' HK' LF; cbn [s_pc s_regs s_log] in HR', HK', LF |- *;
clear HR' HK' LF;
expose_regs;
cbv beta iota delta [mem_denot adenot a_base a_off edenot ev eb vals_ev blobs_ev nth];
val_norm;
fold_log segs
| split_foralls; word_ranges V; first [ sc_solve | match goal with |- ?g => idtac "symb_run: SIDE CONDITION LEFT OPEN:" g end ]
| split_foralls; word_ranges V; first [ sc_solve | match goal with |- ?g => idtac "symb_run: SIDE CONDITION LEFT OPEN:" g end ] ]
end
end
end.

Tactic Notation "symb_run" constr(fuel) constr(stops) constr(dirs) :=
let segs := goal_segs in symb_run_core segs fuel stops (SCR dirs [] []) constr:(@nil word).
Tactic Notation "symb_run" constr(fuel) constr(stops) constr(dirs) "extra" constr(extra) :=
let segs := goal_segs in symb_run_core segs fuel stops (SCR dirs [] []) extra.
Tactic Notation "symb_run" constr(fuel) constr(stops) constr(dirs) "extra" constr(extra) "hints" constr(hints) :=
let segs := goal_segs in symb_run_core segs fuel stops (SCR dirs [] hints) extra.

Ltac symb_show_core segs fuel stops scr extra :=
let m := goal_mem in
let V0 := collect_hyps constr:(@nil word) m in
let V1 := collect_regs V0 in
let V := eval cbn [app] in (V1 ++ extra)%list in
let sr := build_sr V in
let kn0 := kn_hyps V m constr:(@nil kentry) in
let kn1 := kn_img segs m kn0 in
let kn2 := kn_sp_range2 segs V kn1 in
let kn := kn_ranges V O kn2 in
let nx := eval vm_compute in (length V1) in
idtac "ATOMS:" V; idtac "KNOWLEDGE:" kn;
lazymatch goal with
| |- evt _ ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc None _ _) =>
let r := eval vm_compute in (sym_exec segs fuel true stops scr (SS pc sr [] kn nx) []) in
lazymatch r with
| (?ss', ?scs, ?scr') =>
let pc' := eval vm_compute in (s_pc ss') in
idtac "STOPPED AT:" pc'; idtac "REGS:" ss'; idtac "SIDE CONDITIONS:" scs; idtac "SCRIPT LEFT:" scr'
end
end.
Tactic Notation "symb_show" constr(fuel) constr(stops) constr(dirs) :=
let segs := goal_segs in symb_show_core segs fuel stops (SCR dirs [] []) constr:(@nil word).
Tactic Notation "symb_show" constr(fuel) constr(stops) constr(dirs) "extra" constr(extra) :=
let segs := goal_segs in symb_show_core segs fuel stops (SCR dirs [] []) extra.
