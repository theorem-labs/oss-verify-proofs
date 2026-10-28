(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import AsanUbsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.ABoot Require Import
  PropExec CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim RefMemcpyLib.
Local Instance asanreflect_fx : PropExec.FPState := PropExec.fx0.   (* [comment removed for export] *)
Import ListNotations.
Open Scope bv_scope.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_AsanMemcpyBase () : Init.string Init.list := ["Corelib.Numbers.BinNums.Z"; "Corelib.Init.Datatypes.nat"; "Corelib.Init.Logic.and"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "Corelib.Init.Datatypes.list"; "stdpp.bitvector.definitions.bv"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.rdn"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_both.M.loaded_segments"; "MC.memk"; "RocqVerifyHarness.AgentSubmission.ABoot.Hoare.at_"; "Corelib.Init.Datatypes.Some"; "MC.sb_"; "Corelib.Init.Datatypes.cons"; "MC.b_"; "Corelib.Init.Datatypes.nil"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.ABoot.CatExec.wbytes"; "Corelib.Init.Peano.le"; "Corelib.Init.Datatypes.app"; "Corelib.Init.Nat.sub"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_or"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_slli"; "RocqVerifyHarness.AgentSubmission.ABoot.RefMemcpyLib.LWv"; "Stdlib.ZArith.BinInt.Z.sub"; "Stdlib.ZArith.BinInt.Z.mul"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_srliw"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.fetch_word"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.is_ecall"; "Corelib.Init.Datatypes.false"; "Corelib.Init.Datatypes.prod"; "LinuxProcessSemantics.Riscv.Instr.instr"; "LinuxProcessSemantics.Riscv.DecodeC.decode_any"; "Corelib.Init.Datatypes.pair"; "LinuxProcessSemantics.Riscv.Instr.Store"; "LinuxProcessSemantics.Riscv.Instr.SZ1"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.getr"; "stdpp.bitvector.definitions.bv_signed"; "stdpp.bitvector.definitions.Z_to_bv"; "stdpp.bitvector.definitions.bv_unsigned"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_result"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.machine_state"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.step"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.mkst"; "asanreflect_fx"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.MachineOk"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_addi"; "LinuxProcessSemantics.Riscv.Instr.SZ4"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_srli"; "Stdlib.ZArith.BinInt.Z.lt"; "Stdlib.ZArith.BinInt.Z.pow"; "RocqVerifyHarness.AgentSubmission.ABoot.PropExec.v_andi"; "Stdlib.ZArith.BinInt.Z.land"; "Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.modulo"].


Abbreviation ASEGS := AsanUbsan.M.loaded_segments.

(* [comment removed for export] *)
Record mcH (mem0 : word -> option byte) (dst src : word) (n : Z) (bs : list byte) : Prop := MCH {
  Hn : (0 <= n < 2 ^ 64)%Z;
  Hlen : length bs = Z.to_nat n;
  Hsrc : rdn ASEGS mem0 src (length bs) = Some bs;
  Hdst : store_ok ASEGS mem0 dst (length bs) = true;
  Hdisj : (bv_unsigned dst + n <= bv_unsigned src \/ bv_unsigned src + n <= bv_unsigned dst)%Z;
  Hnws : (bv_unsigned src + n < 2 ^ 64)%Z;
  Hnwd : (bv_unsigned dst + n < 2 ^ 64)%Z }.

Section MC.
  Variable mem0 : word -> option byte.
  Variables dst src : word.
  Variable n : Z.
  Variable bs : list byte.
  Hypothesis HOK : mcH mem0 dst src n bs.

  Let Hn := Hn _ _ _ _ _ HOK.
  Let Hlen := Hlen _ _ _ _ _ HOK.
  Let Hsrc := Hsrc _ _ _ _ _ HOK.
  Let Hdst := Hdst _ _ _ _ _ HOK.
  Let Hdisj := Hdisj _ _ _ _ _ HOK.
  Let Hnws := Hnws _ _ _ _ _ HOK.
  Let Hnwd := Hnwd _ _ _ _ _ HOK.

  (* [comment removed for export] *)
  Definition memk (k : Z) : word -> option byte := wbytes mem0 dst (firstn (Z.to_nat k) bs).
  (* [comment removed for export] *)
  Definition sb_ (j : Z) (m : nat) : list byte := sub bs (Z.to_nat j) m.
  (* [comment removed for export] *)
  Definition b_ (j : Z) : byte := nth (Z.to_nat j) bs (Z_to_bv 8 0).

  #[using="mem0 dst src HOK Hn Hlen"] Lemma lenZ : Z.of_nat (length bs) = n.
  Proof. rewrite Hlen. lia. Qed.

  #[using="Type"] Lemma memk_0 : memk 0 = mem0.
  Proof. reflexivity. Qed.

  #[using="src HOK Hlen"] Lemma memk_n : memk n = wbytes mem0 dst bs.
  Proof. unfold memk. rewrite <- Hlen, firstn_all. reflexivity. Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_len : forall j m, (0 <= j)%Z -> (j + Z.of_nat m <= n)%Z -> length (sb_ j m) = m.
  Proof. intros j m Hj Hm. unfold sb_. apply sub_length. rewrite Hlen. lia. Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn Hlen Hsrc Hdisj Hnws Hnwd"] Lemma rd_src : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pk,$0.Pj,$0.Pm,$1.P,(2.(3.=R3.)(3.R3.Vn,))P,(3.=R3.)P,(3.(4.R4.(5.R3.))Vn,)(6.(7.(8.(9.&8.)))(:.$;.(<.R6.)(=.Vsrc,R5.)R4.)(>.(8.(9.&8.))(?.R5.R4.)))")
(* [comment removed for export] *).
  Proof.
    intros k j m Hk Hj Hm. unfold memk, sb_.
    pose proof (u64_range src). pose proof (u64_range dst).
    destruct m as [|m'].
    { cbn. unfold sub. cbn. reflexivity. }
    rewrite rdn_wbytes_out.
    - replace (at_ src j) with (at_ src (Z.of_nat (Z.to_nat j))) by (f_equal; lia).
      apply (rdn_sub ASEGS mem0 (length bs)); [exact Hsrc | rewrite Hlen; lia].
    - rewrite length_firstn, Hlen, at_u; lia.
    - rewrite at_u; lia.
    - rewrite length_firstn, Hlen. lia.
  Qed.

  #[using="HOK Hn Hlen Hsrc Hdisj Hnws Hnwd"] Lemma rd_src1 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pk,$0.Pj,$0.P,(2.(3.=R2.)(3.R2.Vn,))P,(3.=R2.)P,(3.(4.R3.+1.)Vn,)(6.(7.(8.(9.&8.)))(:.$;.(<.R5.)(=.Vsrc,R4.)#1.)(>.(8.(9.&8.))(10.(9.&8.)(11.R4.)(12.(9.&8.)))))")
(* [comment removed for export] *).
  Proof.
    intros k j Hk Hj H1. rewrite (rd_src k j 1) by lia. unfold sb_, b_.
    rewrite sub_nth; [reflexivity | rewrite Hlen; lia].
  Qed.

  (* [comment removed for export] *)
  #[using="src HOK Hn Hlen Hdst Hnwd"] Lemma wr_dst : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pk,$0.Pj,$0.Pm,$1.P,(3.=R2.)P,(3.(4.R3.(5.R2.))Vn,)(6.$13.(14.$;.(<.R5.)(=.Vdst,R4.)R3.)$15.)")
(* [comment removed for export] *).
  Proof.
    intros k j m Hj Hm. unfold memk.
    apply (store_ok_at ASEGS mem0 dst (length bs)); try assumption; rewrite ?lenZ; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="src HOK Hn Hlen"] Lemma memk_extend : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pk,$0.Pl,(8.(9.&8.))Pm,$1.P,(3.=R3.)P,(3.(4.R4.(5.R2.))Vn,)P,(6.(8.(9.&8.))R4.(?.R5.R3.))(6.P,(9.&40.)(7.(9.&8.))(16.(<.R6.)(=.Vdst,R6.)R5.)(<.(4.R6.(5.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros k l m Hk Hm ->. unfold memk, sb_.
    replace (at_ dst k) with (at_ dst (Z.of_nat (Z.to_nat k))) by (f_equal; lia).
    rewrite wbytes_extend' by (rewrite Hlen; lia). f_equal. f_equal. lia.
  Qed.

  #[using="src HOK Hn Hlen"] Lemma memk_extend1 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pk,$0.Pb,(9.&8.)P,(3.=R2.)P,(3.(4.R3.+1.)Vn,)P,(6.(9.&8.)R3.(11.R4.))(6.P,(9.&40.)(7.(9.&8.))(16.(<.R5.)(=.Vdst,R5.)(10.(9.&8.)R4.(12.(9.&8.))))(<.(4.R5.+1.)))")
(* [comment removed for export] *).
  Proof.
    intros k b Hk H1 ->.
    replace (k + 1)%Z with (k + Z.of_nat 1)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 1) 1); try lia; [|reflexivity].
    unfold sb_, b_. rewrite sub_nth by (rewrite Hlen; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="mem0 dst src n HOK Hn Hlen"] Lemma sb4_split : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pq,$1.P,(3.=R2.)P,(17.R2.#4.)(6.(8.(9.&8.))(?.R4.#4.)(18.(9.&8.)(?.R4.R3.)(?.(4.R4.(5.R3.))(19.#4.R3.))))")
(* [comment removed for export] *).
  Proof.
    intros j q Hj Hq. unfold sb_.
    replace 4%nat with (q + (4 - q))%nat at 1 by lia. rewrite sub_split. f_equal. f_equal. lia.
  Qed.

  #[using="mem0 dst src n HOK Hn Hlen"] Lemma skipn_sb : forall j (q m : nat), (0 <= j)%Z ->
      skipn q (sb_ j m) = sb_ (j + Z.of_nat q) (m - q).
  Proof.
    intros j q m Hj. unfold sb_, sub. rewrite skipn_firstn_comm, <- skipn_add. f_equal. f_equal. lia.
  Qed.

  #[using="mem0 dst src n HOK Hn Hlen"] Lemma firstn_sb : forall j (q m : nat), (q <= m)%nat -> firstn q (sb_ j m) = sb_ j q.
  Proof. intros j q m Hq. unfold sb_, sub. rewrite firstn_firstn. f_equal. lia. Qed.

  (* [comment removed for export] *)
  #[using="mem0 dst src HOK Hn Hlen"] Lemma merge_sb : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pq,$1.Pv,(9.&40.)P,(3.=R3.)P,(3.(4.R4.+8.)Vn,)P,(2.(17.#1.R4.)(17.R4.#3.))P,(6.(9.&40.)R4.(1:.(1;.(1<.(?.(4.R6.+4.)#4.))(1=.+20.(1>.+8.(5.R5.))))(1?.(1<.(?.R6.#4.))(1>.+8.(5.R5.)))))(6.(8.(9.&8.))(20.#4.R5.)(?.(4.R7.(5.R6.))#4.))")
(* [comment removed for export] *).
  Proof.
    intros j q v Hj H8 Hq Hv.
    rewrite (sw_bytes_merge (sb_ j 4) (sb_ (j + 4) 4) q v); try (apply sb_len; lia); try assumption.
    rewrite skipn_sb, firstn_sb by lia.
    rewrite (sb4_split (j + Z.of_nat q) (4 - q)) by lia.
    f_equal. f_equal; lia.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma merge_sb' : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pq,$1.Pv,(9.&40.)P,(3.=R3.)P,(3.(4.R4.+8.)Vn,)P,(2.(17.#1.R4.)(17.R4.#3.))P,(6.(9.&40.)R4.(1:.(1?.(1<.(?.R6.#4.))(1>.+8.(5.R5.)))(1;.(1<.(?.(4.R6.+4.)#4.))(1=.+20.(1>.+8.(5.R5.))))))(6.(8.(9.&8.))(20.#4.R5.)(?.(4.R7.(5.R6.))#4.))")
(* [comment removed for export] *).
  Proof.
    intros j q v Hj H8 Hq ->. apply merge_sb; try lia. unfold v_or. f_equal. apply Z.lor_comm.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)

  (* [comment removed for export] *)
  #[using="HOK Hn Hlen Hsrc Hdisj Hnws Hnwd"] Lemma mc_lbu : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ1 false rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 1 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LBv (b_ j))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj1.
    eapply step_lbu; [exact Hf | exact He | exact Hd |].
    rewrite Hrs, at_addi, Hj. apply rd_src1; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK Hn Hlen Hsrc Hdisj Hnws Hnwd"] Lemma mc_lw : forall regs pc rom w rd rs (imm : bv 12) k j0 j,
    fetch_word ASEGS pc = Some w -> is_ecall w = false ->
    decode_any w = Some (Load SZ4 true rd rs imm, 4%Z) ->
    getr regs rs = at_ src j0 -> (j0 + bv_signed imm = j)%Z ->
    (0 <= k <= n)%Z -> (0 <= j)%Z -> (j + 4 <= n)%Z ->
    RiscvSemantics.step ASEGS (mkst regs pc (memk k) rom) =
    MachineOk (mkst (if bv_eqb rd 0 then regs else regupd regs rd (LWv (sb_ j 4))) (v_addi pc 4) (memk k) rom).
  Proof.
    intros regs pc rom w rd rs imm k j0 j Hf He Hd Hrs Hj Hk Hj0 Hj4.
    eapply step_lw; [exact Hf | exact He | exact Hd | |].
    - rewrite Hrs, at_addi, Hj. apply (rd_src k j 4); lia.
    - symmetry. apply u_lez4. apply sb_len; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="src HOK Hn Hlen Hdst Hnwd"] Lemma mc_sb : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pregs,(21.&5.(9.&40.))Ppc,(9.&40.)Prom,P,(9.&40.)(7.(9.&8.))Pw,(9.&20.)Prs1,(9.&5.)Prs2,(9.&5.)Pimm,(9.&<.)Pk,$0.Pk0,$0.Pv,(9.&40.)P,(6.(7.(9.&20.))(22.$;.R9.)(>.(9.&20.)R7.))P,(6.$13.(23.R8.)$24.)P,(6.(7.(25.$26.$0.))(27.R9.)(>.(25.$26.$0.)(28.$26.$0.(29.$2:.R8.R7.R6.)+4.)))P,(6.(9.&40.)(2;.R=.R9.)(=.Vdst,R5.))P,(6.$0.(4.R6.(2<.&<.R8.))R7.)P,(6.(9.&40.)(2;.R?.R:.)R6.)P,(6.(9.&8.)(2=.&8.(2>.&40.R7.))(11.R9.))P,(3.=R:.)P,(3.(4.R;.+1.)Vn,)(6.(2?.$30.)(31.$;.(32.$33.R13.R12.(<.R<.)R11.))(34.$30.(32.$33.R13.(35.R12.+4.)(<.(4.R<.+1.))R11.)))")
(* [comment removed for export] *).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk1.
    rewrite <- (memk_extend1 k (b_ k)) by (lia || reflexivity).
    eapply MmapSim.step_sb_at; [exact Hf | exact He | exact Hd | | exact Hrs2 | exact Hb |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="src HOK Hn Hlen Hdst Hnwd"] Lemma mc_sw : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pregs,(21.&5.(9.&40.))Ppc,(9.&40.)Prom,P,(9.&40.)(7.(9.&8.))Pw,(9.&20.)Prs1,(9.&5.)Prs2,(9.&5.)Pimm,(9.&<.)Pk,$0.Pk0,$0.Pv,(9.&40.)P,(6.(7.(9.&20.))(22.$;.R9.)(>.(9.&20.)R7.))P,(6.$13.(23.R8.)$24.)P,(6.(7.(25.$26.$0.))(27.R9.)(>.(25.$26.$0.)(28.$26.$0.(29.$36.R8.R7.R6.)+4.)))P,(6.(9.&40.)(2;.R=.R9.)(=.Vdst,R5.))P,(6.$0.(4.R6.(2<.&<.R8.))R7.)P,(6.(9.&40.)(2;.R?.R:.)R6.)P,(6.(8.(9.&8.))(20.#4.R7.)(?.R9.#4.))P,(3.=R:.)P,(3.(4.R;.+4.)Vn,)(6.(2?.$30.)(31.$;.(32.$33.R13.R12.(<.R<.)R11.))(34.$30.(32.$33.R13.(35.R12.+4.)(<.(4.R<.+4.))R11.)))")
(* [comment removed for export] *).
  Proof.
    intros regs pc rom w rs1 rs2 imm k k0 v Hf He Hd Hrs1 Hk Hrs2 Hb Hk0 Hk4.
    replace (k + 4)%Z with (k + Z.of_nat 4)%Z by lia.
    rewrite <- (memk_extend k (sb_ k 4) 4) by (lia || reflexivity).
    rewrite <- Hb.
    eapply step_sw_at; [exact Hf | exact He | exact Hd | | exact Hrs2 |].
    - rewrite Hrs1, at_addi, Hk. reflexivity.
    - apply wr_dst; lia.
  Qed.

  (* [comment removed for export] *)
  #[using="mem0 dst src HOK Hn Hlen"] Lemma sw_val_plain : forall k, (0 <= k)%Z -> (k + 4 <= n)%Z ->
    word_to_le_bytes 4 (LWv (sb_ k 4)) = sb_ k 4.
  Proof. intros k Hk H4. apply sw_bytes_LWv. apply sb_len; lia. Qed.

  (* [comment removed for export] *)
  #[using="Type"] Lemma sb_val_plain : forall k, Z_to_bv 8 (bv_unsigned (LBv (b_ k))) = b_ k.
  Proof. intros k. apply sb_byte_LBv. Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_val_srli : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pq,$1.P,(3.=R2.)P,(3.(4.R3.+4.)Vn,)P,(17.R3.#3.)(6.(9.&8.)(2=.&8.(2>.&40.(37.(1<.(?.R5.#4.))(1>.+8.(5.R4.)))))(11.(4.R5.(5.R4.))))")
(* [comment removed for export] *).
  Proof.
    intros j q Hj H4 Hq. rewrite sb_byte_srli_LWv; [| apply sb_len; lia | exact Hq].
    unfold sb_, b_, sub.
    rewrite nth_firstn. replace (q <? 4)%nat with true by (symmetry; apply Nat.ltb_lt; lia).
    rewrite nth_skipn. f_equal. lia.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_val_word0 : forall j, (0 <= j)%Z -> (j + 4 <= n)%Z ->
    Z_to_bv 8 (bv_unsigned (LWv (sb_ j 4))) = b_ j.
  Proof.
    intros j Hj H4.
    pose proof (sb_val_srli j 0 Hj H4 ltac:(lia)) as E.
    rewrite Z.add_0_r in E. rewrite <- E. f_equal. f_equal.
    unfold v_srli. rewrite Z.mul_0_r, Z.shiftr_0_r. symmetry. apply Z_to_bv_bv_unsigned.
  Qed.

  (* [comment removed for export] *)
  #[using="mem0 dst src HOK Hn Hlen"] Lemma merge_s16 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pv,(9.&40.)Pj1,$0.Pj2,$0.Pk,$0.P,(6.(9.&40.)R4.(1:.(1;.(1<.(?.R2.#4.))+10.)(1?.(1<.(?.R3.#4.))+10.)))P,(6.$0.R3.(4.R4.+4.))P,(6.$0.R3.(4.R5.+2.))P,(3.=R6.)P,(3.(4.R7.+8.)Vn,)(6.(8.(9.&8.))(20.#4.R9.)(?.R6.#4.))")
(* [comment removed for export] *).
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 2)%Z with (j1 + Z.of_nat 2)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma merge_s8 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pv,(9.&40.)Pj1,$0.Pj2,$0.Pk,$0.P,(6.(9.&40.)R4.(1:.(1;.(1<.(?.R2.#4.))+18.)(1?.(1<.(?.R3.#4.))+8.)))P,(6.$0.R3.(4.R4.+4.))P,(6.$0.R3.(4.R5.+1.))P,(3.=R6.)P,(3.(4.R7.+8.)Vn,)(6.(8.(9.&8.))(20.#4.R9.)(?.R6.#4.))")
(* [comment removed for export] *).
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 1)%Z with (j1 + Z.of_nat 1)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma merge_s24 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pv,(9.&40.)Pj1,$0.Pj2,$0.Pk,$0.P,(6.(9.&40.)R4.(1:.(1;.(1<.(?.R2.#4.))+8.)(1?.(1<.(?.R3.#4.))+18.)))P,(6.$0.R3.(4.R4.+4.))P,(6.$0.R3.(4.R5.+3.))P,(3.=R6.)P,(3.(4.R7.+8.)Vn,)(6.(8.(9.&8.))(20.#4.R9.)(?.R6.#4.))")
(* [comment removed for export] *).
  Proof.
    intros v j1 j2 k -> -> -> Hj H8.
    replace (j1 + 3)%Z with (j1 + Z.of_nat 3)%Z by lia. apply merge_sb; try lia. reflexivity.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_val_srli8 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pk,$0.P,(3.=R2.)P,(3.(4.R3.+4.)Vn,)P,(6.$0.R3.(4.R4.+1.))(6.(9.&8.)(2=.&8.(2>.&40.(37.(1<.(?.R5.#4.))+8.)))(11.R4.))")
(* [comment removed for export] *).
  Proof.
    intros j k Hj H4 ->. replace (j + 1)%Z with (j + Z.of_nat 1)%Z by lia.
    rewrite <- (sb_val_srli j 1) by lia. reflexivity.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_val_srli16 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pk,$0.P,(3.=R2.)P,(3.(4.R3.+4.)Vn,)P,(6.$0.R3.(4.R4.+2.))(6.(9.&8.)(2=.&8.(2>.&40.(37.(1<.(?.R5.#4.))+10.)))(11.R4.))")
(* [comment removed for export] *).
  Proof.
    intros j k Hj H4 ->. replace (j + 2)%Z with (j + Z.of_nat 2)%Z by lia.
    rewrite <- (sb_val_srli j 2) by lia. reflexivity.
  Qed.

  #[using="mem0 dst src HOK Hn Hlen"] Lemma sb_val_word0' : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pj,$0.Pk,$0.P,(3.=R2.)P,(3.(4.R3.+4.)Vn,)P,(6.$0.R3.R4.)(6.(9.&8.)(2=.&8.(2>.&40.(1<.(?.R5.#4.))))(11.R4.))")
(* [comment removed for export] *).
  Proof. intros j k Hj H4 ->. apply sb_val_word0; lia. Qed.

End MC.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac rwH :=
  repeat match goal with
         | H : getr ?rg ?i = _ |- context [getr ?rg ?i] => rewrite !H
         end.

(* [comment removed for export] *)
Ltac unorm :=
  repeat match goal with
         | |- context [bv_unsigned (Z_to_bv 64 ?z)] =>
             lazymatch z with context [Z_to_bv 64 _] => fail | _ => rewrite (u_Z2bv z) by lia end
         end.

(* [comment removed for export] *)
Ltac mnorm := gres; imm_norm; rewrite ?v_addi_0; rwH; rewrite ?at_addi; vals_lit.

(* [comment removed for export] *)
Ltac cond_lia :=
  rwH; unfold c_ltu, c_eq, bv_ltu, bv_eqb; imm_norm; unorm;
  first [ apply Z.ltb_lt | apply Z.ltb_ge | apply Z.eqb_eq | apply Z.eqb_neq ]; lia.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma u_andi : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Px,(9.&40.)Pimm,$0.P,(2.(3.=R1.)(38.R1.(39.+2.+40.)))(6.$0.(2>.&40.(3:.R3.R2.))(3;.(2>.&40.R3.)R2.))")
(* [comment removed for export] *).
Proof.
  intros x imm Hi. unfold v_andi. rewrite Z_to_bv_unsigned.
  replace (bv_wrap 64 imm) with imm by (symmetry; apply bv_wrap_small; change (bv_modulus 64) with (2^64)%Z; lia).
  apply bv_wrap_small. change (bv_modulus 64) with (2^64)%Z. apply Z_land_range; [apply u64_range|lia].
Qed.

Lemma land_3 : forall a, (0 <= a)%Z -> Z.land a 3 = (a mod 4)%Z.
Proof. intros a Ha. change 3%Z with (Z.ones 2). rewrite Z.land_ones by lia. reflexivity. Qed.

Lemma land_1 : forall a, (0 <= a)%Z -> Z.land a 1 = (a mod 2)%Z.
Proof. intros a Ha. change 1%Z with (Z.ones 1). rewrite Z.land_ones by lia. reflexivity. Qed.

(* [comment removed for export] *)
Lemma bits_lt32 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pm,$0.P,(2.(3.=R1.)(38.R1.+20.))(2.(3<.(6.$0.(3;.R2.+10.)=)(6.$0.(3;.R2.+10.)+10.))(2.(3<.(6.$0.(3;.R2.+8.)=)(6.$0.(3;.R2.+8.)+8.))(2.(3<.(6.$0.(3;.R2.+4.)=)(6.$0.(3;.R2.+4.)+4.))(2.(3<.(6.$0.(3;.R2.+2.)=)(6.$0.(3;.R2.+2.)+2.))(2.(3<.(6.$0.(3;.R2.+1.)=)(6.$0.(3;.R2.+1.)+1.))(6.$0.R2.(4.(4.(4.(4.(3;.R2.+10.)(3;.R2.+8.))(3;.R2.+4.))(3;.R2.+2.))(3;.R2.+1.))))))))")
(* [comment removed for export] *).
Proof.
  intros m Hm.
  assert (E : exists k : nat, m = Z.of_nat k /\ (k < 32)%nat).
  { exists (Z.to_nat m). split; lia. }
  destruct E as (k & -> & Hk).
  do 32 (destruct k as [|k]; [vm_compute; intuition lia|]). lia.
Qed.

Lemma at_mod4 : ltac2:(CDefT.buildp (gd_tbl_AsanMemcpyBase ()) "Pa,(9.&40.)Pd,$0.P,(2.(3.=(4.(2>.&40.R2.)R1.))(38.(4.(2>.&40.R2.)R1.)(39.+2.+40.)))(6.$0.(3=.(2>.&40.(=.R3.R2.))+4.)(3=.(4.(2>.&40.R3.)R2.)+4.))")
(* [comment removed for export] *).
Proof. intros a d H. rewrite at_u by lia. reflexivity. Qed.
