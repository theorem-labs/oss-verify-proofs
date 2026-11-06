(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import ExitSim PropExec CatSim.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
Import ListNotations.
Open Scope bv_scope.
From OSSVerify.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_CatExec () : Init.string Init.list := ["Corelib.Init.Datatypes.list"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.Segment"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "Corelib.Init.Datatypes.nat"; "stdpp.bitvector.definitions.bv"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_rom"; "OSSVerify.KrLib.ABoot.PropExec.seg_rom"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes_aux"; "OSSVerify.KrLib.ABoot.PropExec.rdn"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_mem"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_read_bytes"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_to_nat"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "WithFP.wbytes"; "Stdlib.ZArith.BinInt.Z.pow"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.or"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "Corelib.Init.Datatypes.Some"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Instr.instr"; "Corelib.Numbers.BinNums.Z"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ8"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "OSSVerify.KrLib.ABoot.PropExec.v_addi"; "OSSVerify.KrLib.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.bv_signed"; "Corelib.Init.Datatypes.true"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "OSSVerify.KrLib.ABoot.PropExec.mkst"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "LinuxProcessSemantics.LinuxProcessSem.MemImageType.PhdrInfo"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.EntryDraw"; "Stdlib.ZArith.BinInt.Z.sub"; "LinuxProcessSemantics.LinuxProcessSem.State.stack_max_size"; "OSSVerify.KrLib.ABoot.PropExec.wrap_mem"; "Corelib.Init.Datatypes.None"; "Corelib.Init.Peano.lt"; "Stdlib.Lists.List.flat_map"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.word_le8"; "Corelib.Init.Datatypes.app"; "Corelib.Lists.ListDef.firstn"; "Corelib.Lists.ListDef.nth"; "stdpp.bitvector.definitions.Z_to_bv"; "Corelib.Lists.ListDef.skipn"; "Corelib.Init.Datatypes.S"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.flatten_strings"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.fst"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.string_addrs"; "stdpp.bitvector.definitions.bv_add"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.nat_to_word"; "OSSVerify.KrLib.ABoot.PropExec.total_arg_bytes_nat"; "WithFP.cat_argv_ptr"; "WithFP.cat_string_base"; "LinuxProcessSemantics.LinuxProcessSem.BvBase.len_word"; "WithFP.cat_env_base"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.auxv_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.at_random_ptr"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.build_stack_bytes"; "LinuxProcessSemantics.LinuxProcessSem.StackLayout.stack_to_mem"; "LinuxProcessSemantics.LinuxProcessSem.Run.entry_stack_image"; "Corelib.Init.Nat.add"; "Corelib.Init.Nat.mul"; "WithFP.cat_struct_prefix"; "WithFP.cat_struct_size"; "Corelib.Init.Peano.le"; "LinuxProcessSemantics.LinuxProcessSem.Run.valid_argv"; "LinuxProcessSemantics.LinuxProcessSem.Fs.path_eqb"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Uapi.dot_path"; "LinuxProcessSemantics.LinuxProcessSem.Sys.Fs.Open.openat_plain_name"; "Corelib.Lists.ListDef.Forall"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.Build_machine_state"; "OSSVerify.KrLib.ABoot.PropExec.fp_regs"; "OSSVerify.KrLib.ABoot.PropExec.fp_csr"; "LinuxProcessSemantics.LinuxProcessSem.Run.advance_past_svc"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.set_gpr0"; "OSSVerify.KrLib.ABoot.PropExec.regupd"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_gpr"; "WithFP.pend"; "OSSVerify.KrLib.ABoot.CatSim.to_wexit"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.ms_svc_pending"; "OSSVerify.KrLib.ABoot.ExitSim.is_exit_no"; "LinuxProcessSemantics.Riscv.Sem.reg_get"].


Section WithFP.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma ms_read_bytes_aux_rdn : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pms,$2.Pn,$3.Paddr,(4.&40.)P,(5.P,(4.&40.)(6.(4.&8.))(7.R3.)(8.R4.))(5.(6.(0.(4.&8.)))(9.R4.R2.R3.)(:.R5.(;.R4.)R2.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs ms n. induction n as [|n IH]; intros addr Hrom; [reflexivity|].
  cbn [ms_read_bytes_aux rdn]. unfold ms_read_byte. rewrite Hrom.
  destruct (ms_mem ms addr) as [b|].
  - rewrite IH by exact Hrom. reflexivity.
  - unfold seg_rom. destruct (memory_read segs addr 1) as [[|b r]|];
      try reflexivity; rewrite IH by exact Hrom; reflexivity.
Qed.

#[using="Type"] Lemma ms_read_bytes_rdn : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pms,$2.Paddr,(4.&40.)Plen,(4.&40.)P,(5.P,(4.&40.)(6.(4.&8.))(7.R3.)(8.R4.))(5.(6.(0.(4.&8.)))(<.R4.R3.R2.)(:.R5.(;.R4.)R3.(=.R2.)))")
(* [comment removed for export] *).
Proof. intros. unfold ms_read_bytes. apply ms_read_bytes_aux_rdn; assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Fixpoint wbytes (m : word -> option byte) (addr : word) (bs : list byte)
    : word -> option byte :=
  match bs with
  | [] => m
  | b :: rest => wbytes (fun a => if bv_eqb a addr then Some b else m a) (addr+1) rest
  end.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_above : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pbs,(0.(4.&8.))Pm,P,(4.&40.)(6.(4.&8.))Paddr,(4.&40.)Px,(4.&40.)P,(>.(?.(10.&40.R2.)(11.(12.(4.&8.)R4.)))(10.&40.R1.))(5.(6.(4.&8.))(13.R4.R3.R5.R2.)A1.R4.R2.)")
(* [comment removed for export] *).
Proof.
  induction bs as [|b rest IH]; intros m addr x Hle; [reflexivity|].
  cbn [wbytes length] in *.
  pose proof (u64_range x) as Hx.
  assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
    by (apply u_add1; lia).
  rewrite IH by lia.
  cbv beta.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  rewrite Hne. reflexivity.
Qed.

#[using="Type"] Lemma rdn_wbytes_disjoint : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pbs,(0.(4.&8.))Pm,P,(4.&40.)(6.(4.&8.))Paddr,(4.&40.)Pa,(4.&40.)Pn,$3.P,(>.(?.(10.&40.R3.)(11.(12.(4.&8.)R5.)))(10.&40.R2.))P,(>.(?.(10.&40.R3.)(11.R2.))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R8.(13.R6.R5.R7.)R4.R3.)(:.R8.R6.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs bs m addr a n Hle Hnw. apply rdn_ext; [exact Hnw|].
  intros x Hx. apply wbytes_above. lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma wbytes_below : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pbs,(0.(4.&8.))Pm,P,(4.&40.)(6.(4.&8.))Paddr,(4.&40.)Px,(4.&40.)P,(>.(?.(10.&40.R2.)(11.(12.(4.&8.)R4.)))(14.+2.+40.))P,(15.(10.&40.R2.)(10.&40.R3.))(5.(6.(4.&8.))(13.R5.R4.R6.R3.)A1.R5.R3.)")
(* [comment removed for export] *).
Proof.
  induction bs as [|b rest IH]; intros m addr x Hnw Hlt; [reflexivity|].
  cbn [wbytes length] in *.
  assert (Hne : bv_eqb x addr = false)
    by (unfold bv_eqb; apply Z.eqb_neq; lia).
  destruct rest as [|b' rest'].
  - cbn [wbytes]. rewrite Hne. reflexivity.
  - assert (Hu1 : bv_unsigned (addr + 1) = (bv_unsigned addr + 1)%Z)
      by (apply u_add1; cbn [length] in Hnw; lia).
    rewrite IH by lia.
    cbv beta. rewrite Hne. reflexivity.
Qed.

#[using="Type"] Lemma rdn_wbytes_below : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pbs,(0.(4.&8.))Pm,P,(4.&40.)(6.(4.&8.))Paddr,(4.&40.)Pa,(4.&40.)Pn,$3.P,(>.(?.(10.&40.R2.)(11.R1.))(10.&40.R3.))P,(>.(?.(10.&40.R4.)(11.(12.(4.&8.)R6.)))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R8.(13.R6.R5.R7.)R4.R3.)(:.R8.R6.R4.R3.))")
(* [comment removed for export] *).
Proof.
  intros segs bs m addr a n Hle Hnw.
  pose proof (u64_range addr) as Ha.
  apply rdn_ext; [lia|].
  intros x Hx. apply wbytes_below; [exact Hnw|lia].
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma rdn_wbytes_out : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pbs,(0.(4.&8.))Pm,P,(4.&40.)(6.(4.&8.))Paddr,(4.&40.)Pa,(4.&40.)Pn,$3.P,(16.(>.(?.(10.&40.R2.)(11.R1.))(10.&40.R3.))(>.(?.(10.&40.R3.)(11.(12.(4.&8.)R5.)))(10.&40.R2.)))P,(>.(?.(10.&40.R3.)(11.R2.))(14.+2.+40.))P,(>.(?.(10.&40.R5.)(11.(12.(4.&8.)R7.)))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R9.(13.R7.R6.R8.)R5.R4.)(:.R9.R7.R5.R4.))")
(* [comment removed for export] *).
Proof.
  intros segs bs m addr a n [Hb|Hd] Hnw Hnw'.
  - apply rdn_wbytes_below; [exact Hb | exact Hnw'].
  - apply rdn_wbytes_disjoint; [exact Hd | exact Hnw].
Qed.

#[using="Type"] Lemma length_Z_to_le_bytes : forall n z, length (Z_to_le_bytes n z) = n.
Proof.
  induction n as [|n IH]; intro z; [reflexivity|].
  cbn [Z_to_le_bytes length]. rewrite IH. reflexivity.
Qed.

#[using="Type"] Lemma length_N_to_le_bytes : forall n (v : word), length (word_to_le_bytes n v) = n.
Proof. intros. unfold word_to_le_bytes. apply length_Z_to_le_bytes. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma write_to_mem_wbytes : forall bs (m : word -> option byte) (addr : word),
  write_to_mem m addr bs = wbytes m addr bs.
Proof.
  induction bs as [|b rest IH]; intros m addr; [reflexivity|].
  cbn [write_to_mem wbytes]. apply IH.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma step_sd : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pregs,(17.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(6.(4.&8.))Prom,P,(4.&40.)(6.(4.&8.))Pw,(4.&20.)Prs1,(4.&5.)Prs2,(4.&5.)Pimm,(4.&<.)P,(5.(6.(4.&20.))(18.R9.R7.)(19.(4.&20.)R4.))P,(5.$1:.(1;.R5.)$1<.)P,(5.(6.(1=.$1>.$1?.))(20.R6.)(19.(1=.$1>.$1?.)(21.$1>.$1?.(22.$23.R5.R4.R3.)+4.)))P,(5.$1:.(24.R<.R9.(25.(26.R;.R6.)(27.&<.R4.))#8.)$28.)(29.(0.(4.&8.))Lbs,(0.(4.&8.))(2:.(5.$3.(12.(4.&8.)R1.)#8.)(5.(2;.$2.)(2<.R>.(2=.Vfx,R=.R<.R;.R:.))(2>.$2.(2=.Vfx,R=.(25.R<.+4.)(13.R;.(25.(26.R=.R8.)(27.&<.R6.))R1.)R:.)))))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom w rs1 rs2 imm Hfetch Hecall Hdecode Hok.
  exists (word_to_le_bytes 8 (getr regs rs2)). split; [reflexivity|].
  step_pipeline Hfetch Hecall Hdecode.
  unfold getr; rewrite ?bv_eqb0_is_x0.
  unfold getr in Hok; rewrite ?bv_eqb0_is_x0 in Hok.
  rewrite b_addsext.
  rewrite Hok; cbv beta iota.
  rewrite write_to_mem_wbytes, b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma stack_max_size_val : stack_max_size = 8388608%Z.
Proof. vm_compute. reflexivity. Qed.

#[using="Type"] Lemma wrap_mem_below : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psp,(4.&40.)Pargv,(0.(0.(4.&8.)))Penvp,(0.(0.(4.&8.)))Paddr,(4.&40.)Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(15.(10.&40.R4.)(31.(10.&40.R7.)$32.))(5.(6.(4.&8.))(33.R9.R8.R7.R6.R4.R3.R2.R5.)(34.(4.&8.)))")
(* [comment removed for export] *).
Proof.
  intros ph sp argv envp addr uid hw rnd Hlt.
  pose proof stack_max_size_val as Hsms.
  unfold wrap_mem, stack_to_mem.
  assert (Hsp : Z.leb (bv_unsigned sp) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hsp.
  assert (Hgate : Z.leb (bv_unsigned sp - stack_max_size) (bv_unsigned addr) = false)
    by (apply Z.leb_gt; lia).
  rewrite Hgate. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

#[using="Type"] Lemma flat_map_app' : forall {A B : Type} (f : A -> list B) l1 l2,
  flat_map f (l1 ++ l2) = flat_map f l1 ++ flat_map f l2.
Proof.
  intros A B f l1 l2. induction l1 as [|x xs IH]; cbn; [reflexivity|].
  rewrite IH, app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma skipn_nth : forall {A : Type} (l : list A) k d, (k < length l)%nat ->
  skipn k l = nth k l d :: skipn (S k) l.
Proof.
  induction l as [|x xs IH]; intros k d Hk; [cbn in Hk; lia|].
  destruct k as [|k']; [reflexivity|].
  cbn [skipn nth]. apply IH. cbn in Hk; lia.
Qed.

#[using="Type"] Lemma flat_map_split : forall {A B : Type} (f : A -> list B) l k d, (k < length l)%nat ->
  flat_map f l = flat_map f (firstn k l) ++ f (nth k l d) ++ flat_map f (skipn (S k) l).
Proof.
  intros A B f l k d Hk.
  rewrite <- (firstn_skipn k l) at 1.
  rewrite flat_map_app'.
  rewrite (skipn_nth l k d Hk). reflexivity.
Qed.

#[using="Type"] Lemma flat_map_le8_decomp : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pl,(0.(4.&40.))Pk,$3.P,(35.R1.(12.(4.&40.)R2.))(5.(0.(4.&8.))(36.(4.&40.)(4.&8.)$37.R3.)(38.(4.&8.)(36.(4.&40.)(4.&8.)$37.(39.(4.&40.)R2.R3.))(38.(4.&8.)(37.(3:.(4.&40.)R2.R3.(3;.&40.=)))(36.(4.&40.)(4.&8.)$37.(3<.(4.&40.)(3=.R2.)R3.)))))")
(* [comment removed for export] *).
Proof. intros l k Hk. apply (flat_map_split word_le8 l k (Z_to_bv 64 0) Hk). Qed.

#[using="Type"] Lemma flatten_strings_decomp : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pstrs,(0.(0.(4.&8.)))Pk,$3.P,(35.R1.(12.(0.(4.&8.))R2.))(5.(0.(4.&8.))(3>.R3.)(38.(4.&8.)(3>.(39.(0.(4.&8.))R2.R3.))(38.(4.&8.)(38.(4.&8.)(3:.(0.(4.&8.))R2.R3.(3?.(4.&8.)))(40.(4.&8.)(3;.&8.=)(3?.(4.&8.))))(3>.(3<.(0.(4.&8.))(3=.R2.)R3.)))))")
(* [comment removed for export] *).
Proof.
  intros strs k Hk.
  apply (flat_map_split (fun s => s ++ [Z_to_bv 8 0]) strs k [] Hk).
Qed.

#[using="Type"] Lemma total_arg_bytes_cons : forall s l,
  total_arg_bytes_nat (s :: l) = (length s + 1 + total_arg_bytes_nat l)%nat.
Proof. reflexivity. Qed.

#[using="Type"] Lemma total_arg_bytes_firstn_le : forall k l,
  (total_arg_bytes_nat (firstn k l) <= total_arg_bytes_nat l)%nat.
Proof.
  induction k as [|k IH]; intros l.
  - change (total_arg_bytes_nat (firstn 0 l)) with 0%nat. lia.
  - destruct l as [|s rest]; [cbn; lia|].
    cbn [firstn]. rewrite !total_arg_bytes_cons. specialize (IH rest). lia.
Qed.

#[using="Type"] Lemma natN_le : forall n m, (n <= m)%nat -> (N.of_nat n <= N.of_nat m)%N.
Proof. intros n m H. lia. Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma of_nat_131071 : Z.of_nat 131071 = 131071%Z.
Proof. vm_compute. reflexivity. Qed.
#[using="Type"] Lemma of_nat_2097152 : Z.of_nat 2097152 = 2097152%Z.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cat_struct_size (av ev : list (list byte)) : nat :=
  (8 + (length av + 1) * 8 + (length ev + 1) * 8 + auxv_size)%nat.  (* [comment removed for export] *)

Definition cat_string_base (sp : word) (av ev : list (list byte)) : word :=
  sp + nat_to_word (cat_struct_size av ev).

Definition cat_env_base (sp : word) (av ev : list (list byte)) : word :=
  cat_string_base sp av ev + nat_to_word (total_arg_bytes_nat av).

(* [comment removed for export] *)
Definition cat_argv_ptr (sp : word) (av ev : list (list byte)) (k : nat) : word :=
  nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0).

#[using="Type"] Lemma nth_string_addrs : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pstrs,(0.(0.(4.&8.)))Pbase,(4.&40.)Pk,$3.P,(35.R1.(12.(0.(4.&8.))R3.))(5.(4.&40.)(3:.(4.&40.)R2.(41.(0.(4.&40.))(4.&40.)(42.R3.R4.))(3;.&40.=))(43.&40.R3.(44.(45.(39.(0.(4.&8.))R2.R4.)))))")
(* [comment removed for export] *).
Proof.
  induction strs as [|s rest IH]; intros base k Hk; [cbn in Hk; lia|].
  rewrite string_addrs_fst_structure.
  destruct k as [|k'].
  - cbn [nth firstn]. change (total_arg_bytes_nat []) with 0%nat.
    rewrite word_add_0. reflexivity.
  - cbn [nth]. rewrite (IH (base + len_word s + 1) k' ltac:(cbn in Hk; lia)).
    cbn [firstn]. rewrite total_arg_bytes_cons.
    rewrite len_word_nat, word1_nat, !nat_to_word_add_merge.
    f_equal. f_equal. lia.
Qed.

#[using="Type"] Lemma cat_argv_ptr_offset : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.P,(35.R1.(12.(0.(4.&8.))R3.))(5.(4.&40.)(46.R5.R4.R3.R2.)(43.&40.(47.R5.R4.R3.)(44.(45.(39.(0.(4.&8.))R2.R4.)))))")
(* [comment removed for export] *).
Proof. intros. unfold cat_argv_ptr. apply nth_string_addrs. assumption. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition cat_struct_prefix (ph : PhdrInfo) (sp : word) (av ev : list (list byte))
    (uid : word) (hw : word) : list byte := ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "(38.(4.&8.)(37.(48.(0.(4.&8.))O4.))(38.(4.&8.)(36.(4.&40.)(4.&8.)$37.(41.(0.(4.&40.))(4.&40.)(42.(47.O5.O4.O3.)O4.)))(38.(4.&8.)(37.(3;.&40.=))(38.(4.&8.)(36.(4.&40.)(4.&8.)$37.(41.(0.(4.&40.))(4.&40.)(42.(49.O5.O4.O3.)O3.)))(38.(4.&8.)(37.(3;.&40.=))(4:.O6.(4;.O5.O4.O3.)O2.O1.))))))")
(* [comment removed for export] *).

#[using="Type"] Lemma length_cat_struct_prefix : forall ph sp av ev uid hw,
  length (cat_struct_prefix ph sp av ev uid hw) = cat_struct_size av ev.
Proof.
  intros ph sp av ev uid hw. unfold cat_struct_prefix, cat_struct_size.
  rewrite !length_app, !length_flat_map_le8, !length_string_addrs_fst,
    !length_n_to_le_8, length_auxv_bytes.
  lia.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bsb_argv_prefix : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.(29.(0.(4.&8.))Ltail,(0.(4.&8.))(5.(0.(4.&8.))(4<.R8.R7.R6.R5.R4.R3.R2.)(38.(4.&8.)(37.(48.(0.(4.&8.))R6.))(38.(4.&8.)(36.(4.&40.)(4.&8.)$37.(41.(0.(4.&40.))(4.&40.)(42.(47.R7.R6.R5.)R6.)))R1.))))")
(* [comment removed for export] *).
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bsb_ptr_k : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(35.R4.(12.(0.(4.&8.))R6.))(29.(0.(4.&8.))Lpost,(0.(4.&8.))(5.(0.(4.&8.))(4<.R:.R9.R8.R7.R5.R4.R3.)(38.(4.&8.)(38.(4.&8.)(37.(48.(0.(4.&8.))R8.))(36.(4.&40.)(4.&8.)$37.(39.(4.&40.)R6.(41.(0.(4.&40.))(4.&40.)(42.(47.R9.R8.R7.)R8.)))))(38.(4.&8.)(37.(3:.(4.&40.)R6.(41.(0.(4.&40.))(4.&40.)(42.(47.R9.R8.R7.)R8.))(3;.&40.=)))R1.))))")
(* [comment removed for export] *).
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_argv_prefix ph sp av ev uid hw rnd) as [tail E].
  assert (Hk' : (k < length (fst (string_addrs (cat_string_base sp av ev) av)))%nat)
    by (rewrite length_string_addrs_fst; exact Hk).
  rewrite (flat_map_le8_decomp _ k Hk') in E.
  eexists. rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma read_argv_ptr_k : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psegs,(0.$1.)Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(35.R4.(12.(0.(4.&8.))R6.))P,(15.(?.(10.&40.R8.)(11.(12.(4.&8.)(4<.R:.R8.R7.R6.R4.R3.R2.))))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R:.(4=.R9.(4>.R;.R9.R8.R7.R5.R4.R3.))(43.&40.R9.(44.(4?.#8.(50.#8.R6.))))#8.)(19.(0.(4.&8.))(37.(46.R9.R8.R7.R6.))))")
(* [comment removed for export] *).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_ptr_k ph sp av ev k uid hw rnd Hk) as [post E].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    (word_le8 (nth k (fst (string_addrs (cat_string_base sp av ev) av)) (Z_to_bv 64 0)))
    post 8%nat E (length_n_to_le_8 _) Hnw) as H'.
  assert (Hlen : length (word_le8 (len_word av)
      ++ flat_map word_le8 (firstn k (fst (string_addrs (cat_string_base sp av ev) av))))
    = (8 + 8 * k)%nat).
  { rewrite length_app, length_n_to_le_8, length_flat_map_le8, firstn_length_le;
      [reflexivity | rewrite length_string_addrs_fst; lia]. }
  rewrite Hlen in H'.
  rewrite H'. unfold cat_argv_ptr. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma bsb_strings_split : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.(29.(0.(4.&8.))Ltail,(0.(4.&8.))(5.(0.(4.&8.))(4<.R8.R7.R6.R5.R4.R3.R2.)(38.(4.&8.)(51.R8.R7.R6.R5.R4.R3.)(38.(4.&8.)(3>.R6.)R1.))))")
(* [comment removed for export] *).
Proof.
  intros ph sp av ev uid hw rnd. unfold build_stack_bytes, cat_struct_prefix, cat_env_base, cat_string_base.
  rewrite (string_addrs_pair av). cbv beta iota.
  rewrite (string_addrs_pair ev). cbv beta iota.
  eexists. rewrite <- !app_assoc. reflexivity.
Qed.

#[using="Type"] Lemma bsb_byte_k : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(35.R4.(12.(0.(4.&8.))R6.))(29.(0.(4.&8.))Lpre,(0.(4.&8.))(29.(0.(4.&8.))Lpost,(0.(4.&8.))(2:.(5.(0.(4.&8.))(4<.R;.R:.R9.R8.R6.R5.R4.)(38.(4.&8.)R2.(38.(4.&8.)(38.(4.&8.)(3:.(0.(4.&8.))R7.R9.(3?.(4.&8.)))(40.(4.&8.)(3;.&8.=)(3?.(4.&8.))))R1.)))(5.$3.(12.(4.&8.)R2.)(4?.(52.R9.R8.)(45.(39.(0.(4.&8.))R7.R9.)))))))")
(* [comment removed for export] *).
Proof.
  intros ph sp av ev k uid hw rnd Hk.
  destruct (bsb_strings_split ph sp av ev uid hw rnd) as [tail E].
  rewrite (flatten_strings_decomp av k Hk) in E.
  exists (cat_struct_prefix ph sp av ev uid hw ++ flatten_strings (firstn k av)).
  eexists.
  split.
  - rewrite E. rewrite <- !app_assoc. reflexivity.
  - rewrite length_app, length_cat_struct_prefix, length_flatten_strings. reflexivity.
Qed.

#[using="Type"] Lemma read_argv_byte_k : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psegs,(0.$1.)Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.Pj,$3.Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(35.R5.(12.(0.(4.&8.))R7.))P,(53.R5.(12.(4.&8.)(3:.(0.(4.&8.))R6.R8.(3?.(4.&8.)))))P,(15.(?.(10.&40.R:.)(11.(12.(4.&8.)(4<.R<.R:.R9.R8.R5.R4.R3.))))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R<.(4=.R;.(4>.R=.R;.R:.R9.R6.R5.R4.))(43.&40.(46.R;.R:.R9.R8.)(44.R7.))#1.)(19.(0.(4.&8.))(40.(4.&8.)(3:.(4.&8.)R7.(38.(4.&8.)(3:.(0.(4.&8.))R8.R:.(3?.(4.&8.)))(40.(4.&8.)(3;.&8.=)(3?.(4.&8.))))(3;.&8.=))(3?.(4.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros ph segs sp av ev k j uid hw rnd Hk Hj Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_byte_at_image segs ph sp av ev uid hw rnd
    pre (nth k av [] ++ [Z_to_bv 8 0]) post j E) as H'.
  rewrite Hlen in H'.
  replace (cat_argv_ptr sp av ev k + nat_to_word j)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av) + j)).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite !nat_to_word_add_merge. f_equal. f_equal. lia. }
  apply H'; [rewrite length_app; cbn [length]; lia | exact Hnw].
Qed.

#[using="Type"] Lemma read_argv_str_k : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pph,$2?.Psegs,(0.$1.)Psp,(4.&40.)Pav,(0.(0.(4.&8.)))Pev,(0.(0.(4.&8.)))Pk,$3.Puid,(4.&40.)Phw,(4.&40.)Prnd,$30.P,(35.R4.(12.(0.(4.&8.))R6.))P,(15.(?.(10.&40.R8.)(11.(12.(4.&8.)(4<.R:.R8.R7.R6.R4.R3.R2.))))(14.+2.+40.))(5.(6.(0.(4.&8.)))(:.R:.(4=.R9.(4>.R;.R9.R8.R7.R5.R4.R3.))(46.R9.R8.R7.R6.)(12.(4.&8.)(3:.(0.(4.&8.))R6.R8.(3?.(4.&8.)))))(19.(0.(4.&8.))(3:.(0.(4.&8.))R6.R8.(3?.(4.&8.)))))")
(* [comment removed for export] *).
Proof.
  intros ph segs sp av ev k uid hw rnd Hk Hnw.
  destruct (bsb_byte_k ph sp av ev k uid hw rnd Hk) as [pre [post [E Hlen]]].
  pose proof (read_at_offset_image segs ph sp av ev uid hw rnd
    pre (nth k av []) ([Z_to_bv 8 0] ++ post) (length (nth k av []))) as H.
  rewrite Hlen in H.
  replace (cat_argv_ptr sp av ev k)
    with (sp + nat_to_word (cat_struct_size av ev + total_arg_bytes_nat (firstn k av))).
  2:{ rewrite (cat_argv_ptr_offset sp av ev k Hk). unfold cat_string_base.
      rewrite nat_to_word_add_merge. reflexivity. }
  apply H; [ | reflexivity | exact Hnw].
  rewrite E. rewrite <- !app_assoc. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition byte_at (s : list byte) (k : nat) : byte :=
  nth k (s ++ [Z_to_bv 8 0]) (Z_to_bv 8 0).

#[using="Type"] Lemma nth_lt_byte_at : forall s j, (j < length s)%nat ->
  byte_at s j = nth j s (Z_to_bv 8 0).
Proof. intros s j Hj. unfold byte_at. apply app_nth1. exact Hj. Qed.

#[using="Type"] Lemma byte_at_len : forall s, byte_at s (length s) = Z_to_bv 8 0.
Proof.
  intros s. unfold byte_at. rewrite app_nth2 by lia.
  rewrite Nat.sub_diag. reflexivity.
Qed.

#[using="Type"] Lemma byte_at_nz : forall s j, ~ In (Z_to_bv 8 0) s -> (j < length s)%nat ->
  byte_at s j <> Z_to_bv 8 0.
Proof.
  intros s j Hnz Hj Hc.
  apply Hnz. rewrite <- Hc. rewrite nth_lt_byte_at by exact Hj.
  apply nth_In. exact Hj.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma byte_at_bound : forall s j, (bv_unsigned (byte_at s j) < 256)%Z.
Proof. intros s j. unfold byte_at. apply nth_app0_bound. Qed.

#[using="Type"] Lemma valid_argv_len : forall av, valid_argv av ->
  (Z.of_nat (length av) <= 1024)%Z.
Proof. intros av [Hlen _]. lia. Qed.

#[using="Type"] Lemma valid_argv_nonempty : forall av, valid_argv av -> (1 <= length av)%nat.
Proof. intros av [Hlen _]. lia. Qed.

#[using="Type"] Lemma valid_argv_str_len : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pav,(0.(0.(4.&8.)))Pk,$3.P,(54.R2.)P,(35.R2.(12.(0.(4.&8.))R3.))(>.(11.(12.(4.&8.)(3:.(0.(4.&8.))R3.R4.(3?.(4.&8.)))))+1????.)")
(* [comment removed for export] *).
Proof.
  intros av k [_ [_ [Hstr _]]] Hk.
  rewrite Forall_forall in Hstr.
  specialize (Hstr _ (nth_In av [] Hk)). exact Hstr.
Qed.

#[using="Type"] Lemma valid_argv_str_nz : forall av k, valid_argv av -> (k < length av)%nat ->
  ~ In (Z_to_bv 8 0) (nth k av []).
Proof.
  intros av k [_ [_ [_ [Hnz _]]]] Hk.
  rewrite Forall_forall in Hnz. apply Hnz. apply nth_In. exact Hk.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma valid_argv_str_plain : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pav,(0.(0.(4.&8.)))Pk,$3.P,(54.R2.)P,(35.(3=.R2.)(12.(0.(4.&8.))R3.))P,(5.$1:.(55.(3:.(0.(4.&8.))(3=.R3.)R4.(3?.(4.&8.)))$56.)$1<.)(5.$1:.(57.(3:.(0.(4.&8.))(3=.R4.)R5.(3?.(4.&8.))))$28.)")
(* [comment removed for export] *).
Proof.
  intros av k [_ [_ [_ [_ Hpl]]]] Hk Hdot.
  assert (Hnth : nth (S k) av [] = nth k (tl av) []).
  { destruct av as [|a av']; [cbn in Hk; lia | reflexivity]. }
  assert (Hk' : (k < length (tl av))%nat).
  { destruct av as [|a av']; cbn in *; lia. }
  rewrite Forall_forall in Hpl.
  destruct (Hpl _ (nth_In (tl av) [] Hk')) as [Hsl Hdd].
  rewrite Hnth in Hdot |- *.
  unfold openat_plain_name, path_is_dirref.
  rewrite Hdot, Hsl, Hdd. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma valid_argv_str_bytes : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pav,(0.(0.(4.&8.)))Pk,$3.P,(54.R2.)P,(35.R2.(12.(0.(4.&8.))R3.))(58.(4.&8.)Lb,(4.&8.)(15.(10.&8.R1.)+100.)(3:.(0.(4.&8.))R3.R4.(3?.(4.&8.))))")
(* [comment removed for export] *).
Proof.
  intros av k _ _. apply Forall_forall. intros b _. apply u8_range.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
#[using="Type"] Lemma v_addi_pred : forall x : word, v_addi (x + 1) (-1) = x.
Proof.
  intro x. apply bv_eq. unfold v_addi.
  rewrite Z_to_bv_unsigned, bv_add_unsigned.
  change (bv_unsigned (1 : word)) with 1%Z.
  rewrite bv_wrap_add_idemp_l.
  replace (bv_unsigned x + 1 + -1)%Z with (bv_unsigned x) by lia.
  apply bv_wrap_bv_unsigned.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition pend (regs : bvmap 5 word) (pc : word) (mem rom : word -> option byte)
    : machine_state := ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "(59.O4.(5:.Vfx,)O3.(19.(4.&40.)(3;.&40.+40.))(34.(4.&40.))(5;.Vfx,)O2.O1.)")
(* [comment removed for export] *).

(* [comment removed for export] *)
#[using="Type"] Lemma adv_set : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Pregs,(17.&5.(4.&40.))Ppc,(4.&40.)Psv,(6.(4.&40.))Pmem,P,(4.&40.)(6.(4.&8.))Prom,P,(4.&40.)(6.(4.&8.))Pv,(4.&40.)(5.$2.(5<.(5=.(59.R6.(5:.Vfx,)R5.R4.(34.(4.&40.))(5;.Vfx,)R3.R2.)R1.))(2=.Vfx,(5>.R6.(5?.&5.+:.$60.)R1.)(25.R5.+4.)R3.R2.))")
(* [comment removed for export] *).
Proof.
  intros regs pc sv mem rom v.
  unfold advance_past_svc, set_gpr0, RiscvSemantics.set_reg, ms_pc.
  rewrite bv_eqb_neq by (intro Hc; apply bv_eq in Hc; cbv in Hc; discriminate).
  cbv beta iota.
  cbn [ms_regs ms_pc_val ms_svc_pending ms_resv ms_mem ms_rom].
  unfold mkst, regupd.
  rewrite b_npc4. reflexivity.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tw_write_gen : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pregs,(17.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(6.(4.&8.))Prom,P,(4.&40.)(6.(4.&8.))Pbuf,(0.(4.&8.))Pbufs,(0.(0.(4.&8.)))Pcode,(4.&40.)P,(5.(4.&40.)(61.(62.R7.R6.R5.R4.)#0.)(3;.&40.+1.))P,(5.(6.(0.(4.&8.)))(<.(62.R8.R7.R6.R5.)(61.(62.R8.R7.R6.R5.)#1.)(61.(62.R8.R7.R6.R5.)#2.))(19.(0.(4.&8.))R4.))P,(53.#1.(12.(4.&8.)R5.))P,Pn,$3.P,(53.#1.R1.)P,(53.R2.(12.(4.&8.)R8.))(63.R>.(2=.Vfx,(5>.R=.(5?.&5.+:.$60.)(48.(4.&8.)(39.(4.&8.)R3.R9.)))(25.R<.+4.)R;.R:.)R8.R7.)(63.R<.(62.R;.R:.R9.R8.)(40.(0.(4.&8.))R7.R6.)R5.)")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom buf bufs code Hg0 Hr Hnb Hcont.
  eapply tw_write;
    [reflexivity | reflexivity | exact Hg0 | exact Hr | exact Hnb | ].
  intros n Hn1 Hn2. unfold pend. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tw_exit0 : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pms,$2.Px8,(4.&40.)P,(5.(6.(4.&40.))(64.R2.)(19.(4.&40.)R1.))P,(65.R2.)P,(5.(4.&40.)(61.R4.#0.)(3;.&40.=))(63.R6.R5.(3?.(0.(4.&8.)))(3;.&40.=))")
(* [comment removed for export] *).
Proof.
  intros segs ms x8 Hsvc Hex Hg0.
  assert (Hc : bv_and (ms_gpr ms 0) (Z_to_bv 64 255) = Z_to_bv 64 0).
  { rewrite Hg0. apply bv_eq.
    rewrite bv_and_unsigned, !Z_to_bv_unsigned. reflexivity. }
  rewrite <- Hc. eapply tw_exit; eassumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tw_write_rec : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pregs,(17.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(6.(4.&8.))Prom,P,(4.&40.)(6.(4.&8.))Pbuf,(0.(4.&8.))Pbufs,(0.(0.(4.&8.)))Pcode,(4.&40.)P,(5.$1?.(10.&40.(26.R7.(5?.&5.+11.$60.)))+40.)P,(5.(4.&40.)(66.R8.(5?.&5.+:.$60.))(3;.&40.+1.))P,(5.(6.(0.(4.&8.)))(<.(59.R9.(5:.Vfx,)R8.(19.(4.&40.)(26.R9.(5?.&5.+11.$60.)))(34.(4.&40.))(5;.Vfx,)R7.R6.)(66.R9.(5?.&5.+;.$60.))(66.R9.(5?.&5.+<.$60.)))(19.(0.(4.&8.))R5.))P,(53.#1.(12.(4.&8.)R6.))P,Pn,$3.P,(53.#1.R1.)P,(53.R2.(12.(4.&8.)R9.))(63.R?.(2=.Vfx,(5>.R>.(5?.&5.+:.$60.)(48.(4.&8.)(39.(4.&8.)R3.R:.)))(25.R=.+4.)R<.R;.)R9.R8.)(63.R=.(59.R<.(5:.Vfx,)R;.(19.(4.&40.)(26.R<.(5?.&5.+11.$60.)))(34.(4.&40.))(5;.Vfx,)R:.R9.)(40.(0.(4.&8.))R8.R7.)R6.)")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom buf bufs code H17 H10 Hr Hnb Hcont.
  eapply tw_write.
  - cbn [ms_svc_pending]. reflexivity.
  - exact H17.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_0. exact H10.
  - unfold ms_gpr. cbn [ms_regs]. rewrite arg_reg_1, arg_reg_2. exact Hr.
  - exact Hnb.
  - intros n Hn1 Hn2. rewrite adv_set. apply Hcont; assumption.
Qed.

(* [comment removed for export] *)
#[using="Type"] Lemma tw_exit_rec : ltac2:(CDefT.buildp (gd_tbl_CatExec ()) "Psegs,(0.$1.)Pregs,(17.&5.(4.&40.))Ppc,(4.&40.)Pmem,P,(4.&40.)(6.(4.&8.))Prom,P,(4.&40.)(6.(4.&8.))P,(5.$1?.(10.&40.(26.R4.(5?.&5.+11.$60.)))+5=.)P,(5.(4.&40.)(66.R5.(5?.&5.+:.$60.))(3;.&40.=))(63.R7.(59.R6.(5:.Vfx,)R5.(19.(4.&40.)(26.R6.(5?.&5.+11.$60.)))(34.(4.&40.))(5;.Vfx,)R4.R3.)(3?.(0.(4.&8.)))(3;.&40.=))")
(* [comment removed for export] *).
Proof.
  intros segs regs pc mem rom H17 H10.
  eapply tw_exit0.
  - cbn [ms_svc_pending]. reflexivity.
  - left. exact H17.
  - unfold ms_gpr. cbn [ms_regs].
    rewrite arg_reg_0. exact H10.
Qed.
End WithFP.
