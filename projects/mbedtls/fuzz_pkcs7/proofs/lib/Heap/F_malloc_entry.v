(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import Tac Image ZBridge SysStep  ITree Nodes Decode Arr.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import SFModel.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import F_syscalls MallocRep F_malloc_free F_malloc_fast F_malloc_enframe MallocTree MallocFacts_A MallocKit_A.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import STree Malloc MallocCtrl Monad Prog.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Heap Require Import Malloc_fp.
Import ListNotations.
Open Scope Z_scope.

Ltac shw := match goal with |- evt _ _ (MS ?R _ ?pc _ _ _ _) => idtac "PC" pc; idtac "REGS" R end.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_F_malloc_entry () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "stc_q"; "Corelib.Init.Datatypes.andb"; "Stdlib.ZArith.BinInt.Z.leb"; "Stdlib.ZArith.BinInt.Z.ltb"; "Stdlib.ZArith.BinInt.Z.add"; "OSSVerify.KrLib.Heap.Malloc.size_class"; "Corelib.Init.Datatypes.orb"; "Stdlib.ZArith.BinInt.Z.log2"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.lt"; "OSSVerify.KrLib.Heap.Malloc.MMAP_THRESHOLD"; "OSSVerify.KrLib.Heap.Malloc.size_to_class"; "Stdlib.ZArith.BinInt.Z.mul"; "Stdlib.ZArith.BinInt.Z.div"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Logic.ex"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Datatypes.list"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Logic.eq"; "OSSVerify.KrLib.Lib.MState.MS"; "OSSVerify.KrLib.Lib.Frame.mkR"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "OSSVerify.KrLib.Heap.MallocRep.wz"; "Corelib.Init.Datatypes.None"; "OSSVerify.KrLib.Lib.PropExec.seg_rom"; "OSSVerify.KrLib.Heap.F_syscalls.asegs"; "OSSVerify.KrLib.Lib.Step.rw_cells"; "Corelib.Init.Datatypes.cons"; "OSSVerify.KrLib.Lib.Cells.cell"; "OSSVerify.KrLib.Lib.Cells.CB"; "OSSVerify.KrLib.Lib.Cells.C8"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Datatypes.length"; "OSSVerify.KrLib.Lib.Frame.stk"; "OSSVerify.KrLib.Lib.Frame.munch"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Stdlib.ZArith.BinInt.Z.sub"; "OSSVerify.KrLib.Lib.Frame.wmono"; "OSSVerify.KrLib.Lib.Mem.mem_inv"].


(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma srliw_small a k : 0 <= a < 2^31 -> 0 <= k -> bv_swrap 32 (Z.shiftr (bv_wrap 32 a) k) = Z.shiftr a k.
Proof.
  intros Ha Hk. change (bv_wrap 32 a) with (a mod 2^32). rewrite Z.mod_small by lia.
  apply swrap32_small. rewrite Z.shiftr_div_pow2 by lia.
  pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk). split; [apply Z.le_trans with 0; [lia| apply Z.div_pos; lia]|].
  apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.

Lemma lor_small n a b : 0 <= n -> 0 <= a < 2^n -> 0 <= b < 2^n -> 0 <= Z.lor a b < 2^n.
Proof.
  intros Hn Ha Hb. pose proof (proj2 (Z.lor_nonneg a b) ltac:(lia)) as NN. split; [exact NN|].
  destruct (Z.eq_dec a 0) as [->|A0]; [rewrite Z.lor_0_l; lia|].
  destruct (Z.eq_dec b 0) as [->|B0]; [rewrite Z.lor_0_r; lia|].
  assert (P : 0 < Z.lor a b).
  { destruct (Z.eq_dec (Z.lor a b) 0) as [E|NE]; [apply zb_lor_eq0 in E; lia|]. lia. }
  apply (proj2 (Z.log2_lt_pow2 (Z.lor a b) n P)).
  rewrite Z.log2_lor by lia. apply Z.max_lub_lt.
  - apply (proj1 (Z.log2_lt_pow2 a n ltac:(lia))). lia.
  - apply (proj1 (Z.log2_lt_pow2 b n ltac:(lia))). lia.
Qed.

Lemma shiftr_small n a k : 0 <= a < 2^n -> 0 <= k -> 0 <= Z.shiftr a k < 2^n.
Proof.
  intros Ha Hk. rewrite Z.shiftr_div_pow2 by lia. pose proof (Z.pow_pos_nonneg 2 k ltac:(lia) Hk).
  split; [apply Z.div_pos; lia|]. apply Z.div_lt_upper_bound; [lia|]. nia.
Qed.


(* [comment removed for export] *)
Definition stc_q (q : Z) : Z :=
  if q <? 10 then q else
    let x := q + 1 in
    let i := 4 * Z.log2 x - 4 in
    let i := if size_class (i + 1) <? x then i + 2 else i in
    if size_class i <? x then i + 1 else i.
Definition stc_fn (q : Z) : bool := ltac2:(CDefT.buildp (gd_tbl_F_malloc_entry ()) "Zsc,$0.(1.O1.)(2.(2.(2.(3.=R1.)(4.R1.+30.))(3.(5.O1.+1.)(6.R1.)))(7.(4.O1.+:.)(2.(3.+3.(8.(5.O1.+1.)))(3.(8.(5.O1.+1.))+<.))))")
(* [comment removed for export] *).
Lemma stc_check_true : forallb stc_fn (zseq 0 8191) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma size_to_class_q n : 0 <= n -> size_to_class n = stc_q ((n + 3) / 16).
Proof.
  intros Hn. unfold size_to_class, stc_q, IB, clz32.
  replace (Z.shiftr (n + 4 - 1) 4) with ((n + 3) / 16) by (rewrite Z.shiftr_div_pow2 by lia; change (2 ^ 4) with 16; f_equal; lia).
  set (q := (n + 3) / 16). cbv zeta.
  replace ((28 - (31 - Z.log2 (q + 1))) * 4 + 8) with (4 * Z.log2 (q + 1) - 4) by lia.
  reflexivity.
Qed.

Lemma size_to_class_props n : ltac2:(CDefT.buildp (gd_tbl_F_malloc_entry ()) "P,(9.(:.=O1.)(;.O1.$<.))(9.(9.(:.=(=.O1.))(;.(=.O1.)+30.))(9.(:.(5.O1.+4.)(>.+10.(6.(=.O1.))))P,(:.+:.(?.(5.O1.+3.)+10.))(9.(:.+3.(8.(5.(?.(5.O1.+3.)+10.)+1.)))(:.(8.(5.(?.(5.O1.+3.)+10.)+1.))+<.))))")
(* [comment removed for export] *).
Proof.
  intros Hn. unfold MMAP_THRESHOLD in Hn. rewrite size_to_class_q by lia.
  assert (Q : 0 <= (n + 3) / 16 < 8191) by (Z.div_mod_to_equations; lia).
  pose proof (forallb_zseq stc_fn 0 8191 ((n + 3) / 16) stc_check_true ltac:(lia) ltac:(lia)) as X. unfold stc_fn in X. cbv zeta in X.
  apply andb_prop in X. destruct X as [X X4]. apply andb_prop in X. destruct X as [X X3]. apply andb_prop in X. destruct X as [X1 X2].
  apply Z.leb_le in X1. apply Z.ltb_lt in X2. apply Z.leb_le in X3.
  split; [lia|]. split; [Z.div_mod_to_equations; lia|].
  intros HQ. apply orb_prop in X4. destruct X4 as [X4|X4]; [apply Z.ltb_lt in X4; lia|].
  apply andb_prop in X4. destruct X4 as [X5 X6]. apply Z.leb_le in X5. apply Z.leb_le in X6. lia.
Qed.

Definition entry_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t0 t1 t2 a1 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32)
   (lo : Z) (m : mem) (n : Z) : machine_state -> Prop := ltac2:(CDefT.buildp (gd_tbl_F_malloc_entry ()) "Lms',$10.(11.(12.&40.)La2,(12.&40.)(11.(12.&40.)La3,(12.&40.)(11.(12.&40.)La4,(12.&40.)(11.(13.(12.&8.))Ljunk,(13.(12.&8.))(11.P,(12.&40.)(14.(12.&8.))Lm',P,(12.&40.)(14.(12.&8.))(9.(15.$10.R6.(16.(17.O1?.(18.&40.(5.(19.&40.O1>.)-40.))O1=.O1<.O?.O>.O=.(1:.O1.)O1:.(18.&40.O1.)O<.R5.R4.R3.(18.&40.(=.O1.))O;.O:.O19.O18.O17.O16.O15.O14.O13.O12.O11.O10.O9.O8.O7.O6.)O5.(18.&40.+16>88.)O4.(1;.(12.&40.))R1.(1<.$1=.)))(9.(1>.$1=.R1.(5.(19.&40.O1>.)-40.)(1?.$20.(21.#30.R2.)(1?.$20.(22.O1;.)(1?.$20.(22.O1?.)(23.$20.)))))(9.(15.$24.(25.(12.&8.)R2.)#30.)(9.(26.$1=.R1.O3.(5.(19.&40.O1>.)-40.))(9.(27.(1?.(28.$0.$0.)(29.$0.$0.(2:.(19.&40.O1>.)+40.)(19.&40.O1>.))(23.(28.$0.$0.)))O2.R1.)(9.(2;.$1=.O2.R1.)(2<.$1=.R1.))))))))))))")
(* [comment removed for export] *).


