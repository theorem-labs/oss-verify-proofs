(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-11: made from the released t_48 subtree of Main5Both.v (Section Tree5, its t_1..t_48 and r_4..r_47 definitions) and the hole tables and shapes they name from Main5AsanDefs.v, inside Module M5RelB as data for the tree collector. *)
(* Main5Both's released t_48 subtree as plain data, so that the tree collector (TreeColB.tcol) can walk it: the
   t_1..t_48 / r_4..r_47 definitions of the released Main5Both.v (Section Tree5, verbatim) and the r-free hole tables
   and shapes they name (verbatim from the released Main5AsanDefs.v), inside Module M5RelB so that they do not
   clash with the per-r names of Main5BothDefs.v. *)
From Stdlib Require Import ZArith NArith List Bool.
From OSSVerify.Proofs.coturn.FuzzStunClient.lib.Asan Require Import AxSymExec3 AsanPlan AsanPlanSound AsanMainLib AsanShape MainGlueDefsB MainGlueB ItabBoth W0BLib W0BStates1 W0BStates2 W0BPlans.
Import ListNotations. Import AX2. Import AP.
Open Scope Z_scope.
Module M5RelB.
Definition rsh_1 : shape := SCase (EBlob true 8 1 1) 9223372036854775807 (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)) (SCase (EBlob true 8 1 1) 9223372036854775807 (SExit 2) (SExit 0)).
Definition rsh_2 : shape := SEmitP 1 [SPLit [48]; SPLit [10]] (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))) (SCase (EAlu Instr.ALU_OR (EAlu Instr.ALU_SRL (EMd Instr.M_MUL (ELit 144115188075855872) (EBlob true 8 1 1)) (ELit 49)) (EBlob false 8 0 1)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 0 (SExit 0) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 1 (SEmitP 1 [SPLit [48; 10]] (SExit 0)) (SCase (EAlu Instr.ALU_AND (EBlob false 8 2 1) (ELit 3)) 2 (SEmitP 1 [SPLit [48; 10; 48; 10]] (SExit 0)) (SEmitP 1 [SPLit [48; 10; 48; 10; 48; 10]] (SExit 0)))))))))).
Definition HT_3 : list (nat * (nat * acs)) := [(10%nat, (2%nat, AR0_s))].
Definition HR_4 : list (nat * (shape * acs)) := [(26%nat, (SNil, REP_s))].
Definition HR_5 : list (nat * (shape * acs)) := [(2001%nat, (rsh_1, H2001)); (2007%nat, (rsh_1, H2007)); (2100%nat, (rsh_2, H2100))].
Definition HR_6 : list (nat * (shape * acs)) := [(2003%nat, (rsh_1, H2003)); (2009%nat, (rsh_1, H2009)); (2101%nat, (rsh_2, H2101))].
Definition HR_7 : list (nat * (shape * acs)) := [(2002%nat, (rsh_1, H2002)); (2008%nat, (rsh_1, H2008)); (2100%nat, (rsh_2, H2100))].
Definition HR_8 : list (nat * (shape * acs)) := [(2011%nat, (rsh_1, HSEC_N)); (2102%nat, (rsh_2, HSEC_S))].
Definition t_1 : mtree := (MLeaf 2%nat leaf_s).
Definition t_2 : mtree := (MLeaf 2%nat leaf_v).
Definition t_3 : mtree := (MLeaf 2%nat p0z7).
Definition r_4 : rtree := (RLeaf t_k30).
Definition r_5 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_4).
Definition r_6 : rtree := (RLeaf t_d30lt).
Definition r_7 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_6).
Definition r_8 : rtree := (RLeaf t_k31lt).
Definition r_9 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_8).
Definition r_10 : rtree := (RLeaf t_d31lt).
Definition r_11 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_10).
Definition r_12 : rtree := (RLeaf tsl).
Definition r_13 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 1, 64512)]) r_12).
Definition t_14 : mtree := (MPreS 2%nat p0lt6 HR_5 [(2001%nat, r_7); (2007%nat, r_11); (2100%nat, r_13)]).
Definition r_15 : rtree := (RLeaf t_k30eq).
Definition r_16 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_15).
Definition r_17 : rtree := (RLeaf td30eq).
Definition r_18 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_17).
Definition r_19 : rtree := (RLeaf tk31eq).
Definition r_20 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_19).
Definition r_21 : rtree := (RLeaf td31eq).
Definition r_22 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_21).
Definition r_23 : rtree := (RLeaf tse6).
Definition r_24 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 5889, 7936)]) r_23).
Definition t_25 : mtree := (MPreS 2%nat p0eq6 HR_6 [(2003%nat, r_18); (2009%nat, r_22); (2101%nat, r_24)]).
Definition r_26 : rtree := (RLeaf td30gt).
Definition r_27 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_26).
Definition r_28 : rtree := (RLeaf tk31gt).
Definition r_29 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_28).
Definition r_30 : rtree := (RLeaf td31gt).
Definition r_31 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_30).
Definition t_32 : mtree := (MPreS 2%nat p0gt6 HR_7 [(2002%nat, r_27); (2008%nat, r_31); (2100%nat, r_13)]).
Definition r_33 : rtree := (RLeaf tn_sec).
Definition r_34 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_33).
Definition r_35 : rtree := (RLeaf tssec).
Definition r_36 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2); (QFlen, QMIN, 65535); (QRoom, 64513, 65529)]) r_35).
Definition t_37 : mtree := (MPreS 2%nat p0sec6 HR_8 [(2011%nat, r_34); (2102%nat, r_36)]).
Definition t_38 : mtree := (MEmpty 2%nat).
Definition t_39 : mtree := (MSplit QRoom 65529 t_37 t_38).
Definition t_40 : mtree := (MSplit QRoom 64512 t_32 t_39).
Definition t_41 : mtree := (MSplit QRoom 7936 t_25 t_40).
Definition t_42 : mtree := (MSplit QRoom 5888 t_14 t_41).
Definition t_43 : mtree := (MSplit QRoom 0 t_3 t_42).
Definition t_44 : mtree := (MSplit QRoom (-1) t_2 t_43).
Definition t_45 : mtree := (MSplit QFlen 5 t_1 t_44).
Definition r_46 : rtree := (RLeaf rep26).
Definition r_47 : rtree := (RClass ([(QLook, 4, 4); (QArgc, 2, 2)]) r_46).
Definition t_48 : mtree := (MPreX 1%nat w0r HT_3 [(10%nat, t_45)] HR_4 [(26%nat, r_47)]).
End M5RelB.

(* Pieces, so that the collection of the subtree can run in parallel files (M5ColB*.v): [mkeep keep t] keeps the
   left branch at chain depth d of the MSplit chain t when [keep d] and puts [MEmpty 2] elsewhere (a branch the
   collector passes over at no cost), so each piece is collected under exactly the classes the whole chain gives it;
   [pick d t] reads the left branch at depth d back. *)
Fixpoint mkeep (keep : nat -> bool) (d : nat) (t : mtree) : mtree :=
  match t with
  | MSplit q mid le gt => MSplit q mid (if keep d then le else MEmpty 2%nat) (mkeep keep (S d) gt)
  | _ => MEmpty 2%nat
  end.
Fixpoint pick (d : nat) (t : mtree) : mtree :=
  match d, t with
  | O, MSplit _ _ le _ => le
  | S d', MSplit _ _ _ gt => pick d' gt
  | _, _ => MEmpty 2%nat
  end.
