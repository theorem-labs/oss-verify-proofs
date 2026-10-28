(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec Shape.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import Amb CatExec CatSim SeqExec StoreOk ShapeX SymExec SymExec2 SymExec2Sound SymRun SymDrive SymDriveX BBFrame MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_target_pre.
Import ListNotations.
Open Scope bv_scope.
Import SX2. Import SX2S.
#[local] Existing Instance PropExec.fx0.

#[local] Abbreviation RSEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_read_base () : Init.string Init.list := ["Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "stdpp.bitvector.definitions.bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdEntry"; "Corelib.Init.Datatypes.pair"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.State.FdChannel"; "Corelib.Init.Datatypes.nil"; "Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "Stdlib.ZArith.BinInt.Z.sub"; "stdpp.bitvector.definitions.bv_unsigned"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.kentry"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KImg"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWord"; "LA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.ELit"; "mbx"; "MBA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.EVar"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KZero"; "GMA"; "Corelib.Init.Logic.and"; "Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_reserved"; "LinuxProcessSemantics.LinuxProcessSem.Run.segments_reserved"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.source_alloc_limit"; "LinuxProcessSemantics.LinuxProcessSem.State.map_has"; "LinuxProcessSemantics.LinuxProcessSem.State.vm_maps"; "Corelib.Lists.ListDef.Forall"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Datatypes.snd"; "Stdlib.ZArith.BinInt.Z.pow"; "Corelib.Init.Datatypes.fst"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.length"; "LinuxProcessSemantics.LinuxProcessSem.State.live_bytes"; "Corelib.Init.Logic.ex"; "Stdlib.Lists.List.In"; "Corelib.Init.Logic.not"; "RocqVerifyHarness.AgentSubmission.U.U_target_pre.seps"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.expr"; "J"; "spx"; "gmx"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KAlign"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KRange"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KWr"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.SA"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.KDisj"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.env"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "Corelib.Init.Peano.lt"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "Corelib.Lists.ListDef.nth"; "all_regs"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2.SX2.edenot"; "RocqVerifyHarness.AgentSubmission.BB.SymExec2Sound.SX2S.regs_ok"].


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition fds_std : list (word * FdEntry) := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(0.(1.(2.&40.)$3.)(4.(2.&40.)$3.(5.&40.=)(6.(5.&40.=)))(0.(1.(2.&40.)$3.)(4.(2.&40.)$3.(5.&40.+1.)(6.(5.&40.+1.)))(0.(1.(2.&40.)$3.)(4.(2.&40.)$3.(5.&40.+2.)(6.(5.&40.+2.)))(7.(1.(2.&40.)$3.)))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition fds_file (path : list byte) (off : word) : list (word * FdEntry) :=
  (Z_to_bv 64 3, FdFile path off) :: fds_std.




(* [comment removed for export] *)
Definition mem_eq_outside (M M' : word -> option byte) (rs : list (word * Z)) : Prop :=
  forall a, outside a rs -> M' a = M a.




(* [comment removed for export] *)


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition stack_writable (M : word -> option byte) (sp0 : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "Pd,$8.Pm,$9.P,(:.=R2.)P,(:.(;.R3.(<.R2.))+800000.)(=.$>.(?.$10.O2.(5.&40.(;.(11.(12.&40.O1.)+800000.)R4.))R3.)$13.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition group_writable (M : word -> option byte) (gm : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "Pd,$8.Pm,$9.P,(:.=R2.)P,(:.(;.R3.(<.R2.))+11000.)(=.$>.(?.$10.O2.(5.&40.(;.(12.&40.O1.)R4.))R3.)$13.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition meta_writable (M : word -> option byte) (mb : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "Pd,$8.Pm,$9.P,(:.=R2.)P,(:.(;.R3.(<.R2.))+1000.)(=.$>.(?.$10.O2.(5.&40.(;.(;.(12.&40.O1.)+1000.)R4.))R3.)$13.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition LA (a : Z) : saddr := SA (ELit 0) a.          (* [comment removed for export] *)
Definition MBA (k : Z) : saddr := SA (EVar 2) k.         (* [comment removed for export] *)
Definition GMA (k : Z) : saddr := SA (EVar 3) k.         (* [comment removed for export] *)
Definition mbx (k : Z) : expr := EAlu ALU_ADD (EVar 2) (ELit k).

Definition kn_M1 : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(0.$14.(15.+10000.+4<000.)(0.$14.(16.(17.+7=330.)#8.(18.=))(0.$14.(16.(17.+7=353.)#1.(18.=))(0.$14.(16.(17.+7=380.)#8.(18.+1000.))(0.$14.(16.(17.+7=3<0.)#4.(18.=))(0.$14.(16.(17.+7=3<8.)#8.(18.=))(0.$14.(16.(17.+7=3=0.)#4.(18.+1.))(0.$14.(16.(17.+7=3=4.)#4.(18.+1.))(0.$14.(16.(17.+7=3=8.)#8.(18.=))(0.$14.(16.(17.+7=3>0.)#8.(19.+1040.))(0.$14.(16.(17.+7=3>8.)#8.(18.+64.))(0.$14.(16.(17.+7=3?0.)#8.(18.=))(0.$14.(16.(17.+7=400.)#8.(19.+1000.))(0.$14.(16.(17.+7=408.)#8.(19.+1000.))(0.$14.(16.(17.+7=410.)#8.(19.+2000.))(0.$14.(16.(17.+7=578.)#8.(19.+1018.))(0.$14.(16.(17.+7=6?8.)#8.(18.+1.))(0.$14.(16.(17.+7=758.)#1.(18.+1.))(0.$14.(16.(1:.+1000.)#8.(18.=))(0.$14.(16.(1:.+1008.)#8.(18.=))(0.$14.(16.(1:.+1010.)#4.(18.+65.))(0.$14.(16.(1:.+1018.)#8.(19.+1018.))(0.$14.(16.(1:.+1020.)#8.(19.+1018.))(0.$14.(16.(1:.+1028.)#8.(1;.#3.))(0.$14.(16.(1:.+1030.)#4.(18.=))(0.$14.(16.(1:.+1034.)#4.(18.=))(0.$14.(16.(1:.+1038.)#8.(18.+11;20.))(0.$14.(1<.(1:.+1040.)(18.+?<0.))(0.$14.(16.(1=.=)#8.(19.+1018.))(0.$14.(16.(1=.+8.)#1.(18.=))(0.$14.(1<.(1=.+9.)(18.+4.))(0.$14.(16.(1=.+=.)#1.(18.+>0.))(0.$14.(16.(1=.+>.)#2.(18.+1.))(0.$14.(1<.(1=.+10.)(18.+<.))(0.$14.(16.(1=.+1<.)#1.(18.=))(0.$14.(16.(1=.+1=.)#1.(18.+:0.))(0.$14.(16.(1=.+1>.)#2.(18.+1.))(0.$14.(16.(1=.+10020.)#1.(18.=))(0.$14.(1<.(1=.+10021.)(18.+?=6.))(0.$14.(16.(1=.+17<;3.)#1.(18.=))(0.$14.(16.(1=.+17<;4.)#4.(18.+?=<.))(0.$14.(1<.(1=.+17<;8.)(18.+4.))(7.$14.)))))))))))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).             (* [comment removed for export] *)

Record read_pre (sp0 p1 mb gm : word) (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_PRE {
  (* [comment removed for export] *)
  rp_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rp_gp : getr R 3 = Z_to_bv 64 0x10800;
  rp_tp : getr R 4 = Z_to_bv 64 0x5d0c8;
  rp_s0 : getr R 8 = Z_to_bv 64 2;
  rp_a0 : getr R 10 = Z_to_bv 64 (bv_unsigned gm + 32);        (* [comment removed for export] *)
  rp_s2 : getr R 18 = p1;                                      (* [comment removed for export] *)
  rp_s4 : getr R 20 = Z_to_bv 64 3;                            (* [comment removed for export] *)
  rp_s5 : getr R 21 = Z_to_bv 64 65536;                        (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_sp0 : (0x7fff80000000 <= bv_unsigned sp0 <= 0x800000000000)%Z /\ (bv_unsigned sp0 mod 16 = 0)%Z;
  rp_p1  : (0x7fff80000000 <= bv_unsigned p1 <= 0x800000400000)%Z;
  rp_b   : (0x1000 <= bv_unsigned mb)%Z /\ (bv_unsigned mb + 8192 <= 0x7fff7f800000)%Z
           /\ (bv_unsigned mb mod 4096 = 0)%Z;
  rp_b_img : (bv_unsigned mb + 8192 <= 0x10000 \/ 0x7e000 <= bv_unsigned mb)%Z;
           (* [comment removed for export] *)
  rp_gm  : (0x7e000 <= bv_unsigned gm)%Z /\ (bv_unsigned gm + 69632 <= 0x7fff7f800000)%Z
           /\ (bv_unsigned gm mod 4096 = 0)%Z;
  rp_gm_b : (bv_unsigned mb + 8192 <= bv_unsigned gm \/ bv_unsigned gm + 69632 <= bv_unsigned mb + 4096)%Z;
           (* [comment removed for export] *)
  (* [comment removed for export] *)
  rp_stack : stack_writable M sp0;
  rp_group : group_writable M gm;
  rp_meta  : meta_writable M mb;
  (* [comment removed for export] *)
  rp_errno : exists e : word, rdn RSEGS M (Z_to_bv 64 0x5d024) 4 = Some (word_to_le_bytes 4 e);
  (* [comment removed for export] *)
  rp_malloc : forall (x0 x1 x4 x5 x6 x7 : word) (extra : list word) (ebs : list (list byte)),
      know_ok RSEGS (Env (vals_ev ([x0; x1; mb; gm; x4; x5; x6; x7] ++ extra)) (blobs_ev ebs)) M kn_M1
}.

(* [comment removed for export] *)
Definition model_pre {AMB : Amb} (path : list byte) (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word) : Model :=
  mkModelC (fds_file path (Z_to_bv 64 0)) VM stdin0 fs0 None (Some tid) None.
Definition model_post {AMB : Amb} (VM : VmMaps) (stdin0 : InputStream) (fs0 : Fs) (tid : word) : Model :=
  mkModelC fds_std VM stdin0 fs0 None (Some tid) None.

(* [comment removed for export] *)
Definition vm_pre (VM : VmMaps) (mb gm : word) : Prop := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(1>.(=.(1?.(1.(2.&40.)(2.&40.)))(20.O3.)(21.$10.))(1>.(=.$8.(22.O3.)$23.)(1>.(=.$>.(24.(25.O3.)O1.(5.&40.+11000.))$13.)(1>.(26.(1.(2.&40.)(2.&40.))Lp,(1.(2.&40.)(2.&40.))(1>.(1>.(27.=(12.&40.(28.(2.&40.)(2.&40.)R1.)))(:.(12.&40.(28.(2.&40.)(2.&40.)R1.))(29.+2.+1>.)))(:.(;.(12.&40.(2:.(2.&40.)(2.&40.)R1.))(12.&40.(28.(2.&40.)(2.&40.)R1.)))(29.+2.+40.)))(25.O3.))(1>.(2;.(2<.(1.(2.&40.)(2.&40.))(25.O3.))#8.)(1>.(:.(2=.(25.O3.))(29.+2.+14.))(1>.(2>.(1.(2.&40.)(2.&40.))Lp,(1.(2.&40.)(2.&40.))(1>.(2?.(1.(2.&40.)(2.&40.))R1.(25.O3.))(1>.(30.(=.(2.&40.)(2:.(2.&40.)(2.&40.)R1.)O1.))(1>.(:.(12.&40.(2:.(2.&40.)(2.&40.)R1.))(;.(12.&40.O2.)+1000.))(:.(;.(12.&40.O2.)+2000.)(;.(12.&40.(2:.(2.&40.)(2.&40.)R1.))(12.&40.(28.(2.&40.)(2.&40.)R1.))))))))(31.(25.O3.)))))))))")
(* [comment removed for export] *).   (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition read_regions0 (sp0 gm : word) (L : Z) : list (word * Z) :=
  [(Z_to_bv 64 (bv_unsigned sp0 - 8388608), 8388496%Z); (Z_to_bv 64 (bv_unsigned gm + 32), L)].

Record read_post0 (sp0 p1 gm : word) (content : list byte)
       (R0 : bvmap 5 word) (M0 : word -> option byte)
       (R : bvmap 5 word) (M : word -> option byte) : Prop := READ_POST0 {
  rq_sp : getr R 2 = Z_to_bv 64 (bv_unsigned sp0 - 128);
  rq_gp : getr R 3 = Z_to_bv 64 0x10800;
  rq_tp : getr R 4 = Z_to_bv 64 0x5d0c8;
  rq_s0 : getr R 8 = Z_to_bv 64 2;
  rq_s1 : getr R 9 = Z_to_bv 64 (bv_unsigned gm + 32);         (* [comment removed for export] *)
  rq_s2 : getr R 18 = p1;
  rq_s3 : getr R 19 = Z_to_bv 64 (Z.of_nat (length content));  (* [comment removed for export] *)
  rq_s4 : getr R 20 = Z_to_bv 64 3;
  rq_s5 : getr R 21 = Z_to_bv 64 65536;                         (* [comment removed for export] *)
  rq_s6 : getr R 22 = Z_to_bv 64 (bv_unsigned gm + 32);         (* [comment removed for export] *)
  rq_keep : forall r : reg, In r [23; 24; 25; 26; 27]%bv -> getr R r = getr R0 r;   (* [comment removed for export] *)
  (* [comment removed for export] *)
  rq_frame : mem_eq_outside M0 M (read_regions0 sp0 gm (Z.of_nat (length content)));
  rq_grows : mem_grows M0 M;
  rq_content : rdn RSEGS M (Z_to_bv 64 (bv_unsigned gm + 32)) (length content) = Some content;
  rq_stack : stack_writable M sp0;
  rq_group : group_writable M gm }.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition valsr (sp0 p1 b gm : word) (L : Z) (R : bvmap 5 word) : list word :=
  [sp0; p1; b; gm; Z_to_bv 64 L; Z_to_bv 64 0; Z_to_bv 64 0; Z_to_bv 64 0] ++ junk_vals R.
Definition ENVr (vals : list word) (content : list byte) : env := Env (vals_ev vals) (blobs_ev [content]).

Definition spx (k : Z) : expr := EAlu ALU_ADD (EVar 0) (ELit k).
Definition gmx (k : Z) : expr := EAlu ALU_ADD (EVar 3) (ELit k).
Definition J (i : nat) : expr := EVar (8 + i).

Definition sr_RE : list expr := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(0.$32.(18.=)(0.$32.(33.#1.)(0.$32.(34.-80.)(0.$32.(18.+10800.)(0.$32.(18.+5=0<8.)(0.$32.(33.#5.)(0.$32.(33.#6.)(0.$32.(33.#7.)(0.$32.(18.+2.)(0.$32.(33.#9.)(0.$32.(35.+20.)(0.$32.(33.#;.)(0.$32.(33.#<.)(0.$32.(33.#=.)(0.$32.(33.#>.)(0.$32.(33.#?.)(0.$32.(33.#10.)(0.$32.(33.#11.)(0.$32.(1;.#1.)(0.$32.(33.#13.)(0.$32.(18.+3.)(0.$32.(18.+10000.)(0.$32.(33.#16.)(0.$32.(33.#17.)(0.$32.(33.#18.)(0.$32.(33.#19.)(0.$32.(33.#1:.)(0.$32.(33.#1;.)(0.$32.(33.#1<.)(0.$32.(33.#1=.)(0.$32.(33.#1>.)(0.$32.(33.#1?.)(7.$32.)))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

(* [comment removed for export] *)
Definition kn_RE_base : list kentry := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(0.$14.(36.(1;.#0.)+10.)(0.$14.(37.(1;.#0.)+7???80000000.+800000000000.)(0.$14.(38.(39.(1;.#0.)-800000.)+800000.)(0.$14.(36.(1;.#3.)+1000.)(0.$14.(37.(1;.#3.)+7>000.+7???7?7>?000.)(0.$14.(38.(39.(1;.#3.)=)+11000.)(0.$14.(3:.(39.(1;.#0.)-800000.)+800000.(39.(1;.#3.)=)+11000.)(0.$14.(37.(1;.#1.)+7???80000000.+800000400000.)(7.$14.)))))))))")
(* [comment removed for export] *).
Definition kn_RE (Llo Lhi : Z) : list kentry := kn_RE_base ++ [KRange (EVar 4) Llo Lhi].

Definition all_regs : list reg := ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "(0.(2.&5.)(3;.&5.=$3<.)(0.(2.&5.)(3;.&5.+1.$3<.)(0.(2.&5.)(3;.&5.+2.$3<.)(0.(2.&5.)(3;.&5.+3.$3<.)(0.(2.&5.)(3;.&5.+4.$3<.)(0.(2.&5.)(3;.&5.+5.$3<.)(0.(2.&5.)(3;.&5.+6.$3<.)(0.(2.&5.)(3;.&5.+7.$3<.)(0.(2.&5.)(3;.&5.+8.$3<.)(0.(2.&5.)(3;.&5.+9.$3<.)(0.(2.&5.)(3;.&5.+:.$3<.)(0.(2.&5.)(3;.&5.+;.$3<.)(0.(2.&5.)(3;.&5.+<.$3<.)(0.(2.&5.)(3;.&5.+=.$3<.)(0.(2.&5.)(3;.&5.+>.$3<.)(0.(2.&5.)(3;.&5.+?.$3<.)(0.(2.&5.)(3;.&5.+10.$3<.)(0.(2.&5.)(3;.&5.+11.$3<.)(0.(2.&5.)(3;.&5.+12.$3<.)(0.(2.&5.)(3;.&5.+13.$3<.)(0.(2.&5.)(3;.&5.+14.$3<.)(0.(2.&5.)(3;.&5.+15.$3<.)(0.(2.&5.)(3;.&5.+16.$3<.)(0.(2.&5.)(3;.&5.+17.$3<.)(0.(2.&5.)(3;.&5.+18.$3<.)(0.(2.&5.)(3;.&5.+19.$3<.)(0.(2.&5.)(3;.&5.+1:.$3<.)(0.(2.&5.)(3;.&5.+1;.$3<.)(0.(2.&5.)(3;.&5.+1<.$3<.)(0.(2.&5.)(3;.&5.+1=.$3<.)(0.(2.&5.)(3;.&5.+1>.$3<.)(0.(2.&5.)(3;.&5.+1?.$3<.)(7.(2.&5.))))))))))))))))))))))))))))))))))")
(* [comment removed for export] *).

Lemma nth_all_regs : forall n, (n < 32)%nat -> nth n all_regs 0%bv = Z_to_bv 5 (Z.of_nat n).
Proof.
  intros n Hn.
  destruct n as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|n]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia]; apply bv_eq; reflexivity.
Qed.

Lemma regs_ok_by_index : ltac2:(CDefT.buildp (gd_tbl_P_read_base ()) "PE,$3=.Psr,(1?.$32.)PR,(3>.&5.(2.&40.))P,Pi,$9.P,(3?.R1.#20.)(=.(2.&40.)(40.R3.(41.(2.&5.)R2.$42.(3;.&5.=$3<.)))(43.R5.(41.$32.R2.R4.(18.=))))(44.R4.R3.R2.)")
(* [comment removed for export] *).
Proof.
  intros E sr R H r. unfold sr_get. destruct (bv_eqb r 0) eqn:Hr0.
  - assert (r = 0%bv) by (apply bv_eq; unfold bv_eqb in Hr0; lia). subst r. cbn [edenot]. reflexivity.
  - pose proof (H (ridx r) (ridx_range r)) as Hx. rewrite nth_all_regs in Hx by apply ridx_range.
    rewrite ridx_roundtrip in Hx. exact Hx.
Qed.

Section EntrySym.
  Variables (sp0 p1 b gm : word) (L : Z) (R : bvmap 5 word) (M : word -> option byte) (content : list byte).
  Hypothesis RP : read_pre sp0 p1 b gm R M.
  Let vals := valsr sp0 p1 b gm L R.
  Let E := ENVr vals content.

            
    
  
  End EntrySym.
