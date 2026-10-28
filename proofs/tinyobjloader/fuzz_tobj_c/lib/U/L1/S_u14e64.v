From Stdlib Require Import ZArith NArith List Bool PArith.
From stdpp Require Import bitvector.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw Require Import Safety.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Fw3 Require Import SymState SymStep SymSoundR.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.Lib Require Import SumConv.
From OssFuzzTheorems.Proofs.tinyobjloader.fuzz_tobj_c.lib.U Require Import Init.
Import ListNotations.
Close Scope bv_scope.
Open Scope Z_scope.

Module BinitAddr.
  Definition bi_entry : Z := 0x14e64.
  Definition bi_ret : Z := 0x150a8.
End BinitAddr.
Import BinitAddr.

Definition bvB : sv := SVar 12.

Definition bpc (o : Z) (w : Z) (v : Z) : cell := mkCell (SLit o) w (SLit v).
Definition vcells (o e : Z) : list cell := [bpc o 8 0; bpc (o + 8) 8 0; bpc (o + 16) 8 0; bpc (o + 24) 8 e].
Fixpoint vrun (o : Z) (es : list Z) : list cell :=
  match es with [] => [] | e :: r => vcells o e ++ vrun (o + 32) r end.

Definition bobj (lo hi : Z) (cells : list cell) : sobj := mkObj bvB (SLit lo) (SLit hi) cells DUnknown.

Definition bi_ranges : list (Z * Z) := [(120, 312); (320, 480); (496, 880); (900, 908); (936, 1256)].

Definition bi_pre_objs : list sobj := map (fun r => bobj (fst r) (snd r) []) bi_ranges.

Definition bi_post_objs : list sobj :=
  [bobj 120 312 (vrun 120 [4; 4; 4; 4; 4; 4]);
   bobj 320 480 (vrun 320 [1168; 8; 4; 24; 128]);
   bobj 496 880 (vrun 496 [12; 4; 4; 4; 12; 4; 12; 12; 4; 4; 1; 4]);
   bobj 900 908 [bpc 900 4 0; bpc 904 4 0];
   bobj 936 1256 (vrun 936 [4; 12; 4; 4; 12; 12; 12; 56; 48; 128])].

Definition bi_facts : list sprop := [SPAlign 12 3].

Definition Pre_bi : sstate := mkSS bi_entry pre_regs pre_fregs FcsrFrm0 None bi_pre_objs bi_facts NF false.

Definition P_bi : sstate :=
  mkSS bi_ret
    (setregs (post_regs NF) [(11%nat, SLit 4); (12%nat, SLit 128); (13%nat, SLit 12); (14%nat, SLit 56); (15%nat, SLit 48)])
    pre_fregs FcsrFrm0 None bi_post_objs bi_facts NPOST false.

Definition Posts_bi : list leaf := [mkLeaf P_bi RsSymJump].

Definition builder_init_sum_stmt_U : Prop :=
  forall ok K rho, ok_frame segsU ok K ->
    triple segsU ok (SP segsU K Pre_bi rho) (LQ segsU K NF rho Posts_bi).

Definition builder_init_sum_ex_stmt_U : Prop :=
  forall K rho, etriple segsU (SP segsU K Pre_bi rho) (LQ segsU K NF rho Posts_bi).
