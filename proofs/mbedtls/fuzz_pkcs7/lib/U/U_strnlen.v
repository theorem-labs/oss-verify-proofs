(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
From OssFuzzTheorems.mbedtls.fuzz_pkcs7.images Require Import Ubsan.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import PropExec.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.BB Require Import CatExec CatSim SeqExec StepTac Hoare StoreOk WalkTac MmapSim BBFrame MemcpyLib.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.U Require Import U_memcpy_base U_memchr U_code_43000_43c04.
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require Import DietDestruct.   (* [comment removed for export] *)
Import ListNotations.
#[local] Existing Instance PropExec.fx0.
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
From OssFuzzTheorems.Proofs.mbedtls.fuzz_pkcs7.lib.Lib Require CDefT.
From Ltac2 Require Ltac2.
Ltac2 gd_tbl_P_strnlen () : Init.string Init.list := ["Corelib.Init.Logic.or"; "Stdlib.ZArith.BinInt.Z.le"; "Stdlib.ZArith.BinInt.Z.add"; "stdpp.bitvector.definitions.bv_unsigned"; "Stdlib.ZArith.BinInt.Z.of_nat"; "Corelib.Init.Datatypes.length"; "stdpp.bitvector.definitions.bv"; "Stdlib.ZArith.BinInt.Z.sub"; "RocqVerifyHarness.AgentSubmission.BB.CatExec.wbytes"; "stdpp.bitvector.definitions.Z_to_bv"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.word_to_le_bytes"; "Stdlib.ZArith.BinInt.Z.lt"; "Corelib.Init.Logic.eq"; "Corelib.Init.Datatypes.option"; "SNL.mem1"; "LinuxProcessSemantics.Riscv.Prelude.bvmap"; "RocqVerifyHarness.AgentSubmission.BB.Hoare.ret_ok"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.getr"; "stdpp.bitvector.definitions.BV"; "Corelib.Init.Logic.I"; "Corelib.Init.Logic.ex"; "Corelib.Init.Logic.and"; "RocqVerifyHarness.AgentSubmission.Lib.Shape.msteps"; "RocqVerifyHarness.ProcessOversight.Tgt_fuzz_pkcs7_ubsan.M.loaded_segments"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.mkst"; "RocqVerifyHarness.AgentSubmission.Lib.PropExec.fx0"; "RocqVerifyHarness.AgentSubmission.BB.MemcpyLib.keeps_cs"; "Corelib.Init.Datatypes.list"; "Corelib.Numbers.BinNums.Z"; "RocqVerifyHarness.AgentSubmission.U.U_memchr.mchrH"; "Corelib.Init.Datatypes.bool"; "LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics.store_ok"; "Corelib.Init.Datatypes.true"; "RocqVerifyHarness.AgentSubmission.BB.BBFrame.frame_mod"; "Corelib.Init.Datatypes.cons"; "Corelib.Init.Datatypes.prod"; "Corelib.Init.Datatypes.pair"; "Corelib.Init.Datatypes.nil"].


Section SNL.
  Variable mem : word -> option byte.
  Variables s sp : word.
  Variable buf : list byte.
  Variables K n : Z.
  Variable rom : word -> option byte.
  Hypothesis HOK : mchrH mem s buf K n.
  Hypothesis HsK : (0 < bv_unsigned s + K)%Z.
  Hypothesis Hstk : store_ok RSEGS mem (Z_to_bv 64 (bv_unsigned sp - 32)) 32 = true.
  Hypothesis Hspr : (0x10c58 <= bv_unsigned sp - 32)%Z.
  Hypothesis Hdisj : ltac2:(CDefT.buildp (gd_tbl_P_strnlen ()) "(0.(1.(2.(3.&40.Vs,)(4.(5.(6.&8.)Vbuf,)))(7.(3.&40.Vsp,)+20.))(1.(3.&40.Vsp,)(3.&40.Vs,)))")
(* [comment removed for export] *).

  #[local] Notation usp := (bv_unsigned sp).
  #[local] Notation W8 v := (word_to_le_bytes 8 v).

  (* [comment removed for export] *)
  Definition mem1 (ra s0 s1 : word) : word -> option byte := ltac2:(CDefT.buildp (gd_tbl_P_strnlen ()) "(8.(8.(8.Vmem,(9.&40.(7.(3.&40.Vsp,)+8.))(:.#8.O3.))(9.&40.(7.(3.&40.Vsp,)+10.))(:.#8.O2.))(9.&40.(7.(3.&40.Vsp,)+18.))(:.#8.O1.))")
(* [comment removed for export] *).

  #[using="Type"] Lemma lenW8 : forall v : word, length (W8 v) = 8%nat.
  Proof. intros v. apply length_N_to_le_bytes. Qed.

  #[using="Hspr"] Lemma mem1_out : ltac2:(CDefT.buildp (gd_tbl_P_strnlen ()) "Pra,(6.&40.)Ps0,(6.&40.)Ps1,(6.&40.)Pa,(6.&40.)P,(0.(;.(3.&40.R1.)(7.(3.&40.Vsp,)+18.))(1.(3.&40.Vsp,)(3.&40.R1.)))(<.(=.(6.&8.))(>.R5.R4.R3.R2.)A1.Vmem,R2.)")
(* [comment removed for export] *).
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1 a Ha. pose proof (u64_range sp). unfold mem1.
    rewrite !wbytes_outside; rewrite ?lenW8; unfold in_rng; u_norm; try lia; reflexivity.
  Qed.

  (* [comment removed for export] *)
  #[using="HOK HsK Hspr Hdisj"] Lemma HOK1 : forall ra s0 s1, mchrH (mem1 ra s0 s1) s buf K n.
  Proof.
    intros ra s0 s1. pose proof (u64_range sp). pose proof (u64_range s). destruct HOK. split; try assumption.
    - rewrite <- Hbuf. apply rdn_ext; [lia|]. intros x Hx. apply mem1_out. lia.
    - intros i Hi. rewrite mem1_out; [apply Hro; exact Hi | u_norm; lia].
  Qed.

  #[using="Hspr"] Lemma frame1 : forall ra s0 s1, frame_mod mem (mem1 ra s0 s1) [(Z_to_bv 64 (usp - 32), 32%Z)].
  Proof.
    clear HOK HsK Hstk Hdisj. intros ra s0 s1. pose proof (u64_range sp). split.
    - intros a [Ha _]. unfold in_rng in Ha. revert Ha. u_norm. intros Ha. apply mem1_out. lia.
    - unfold mem1. eapply mem_grows_trans; [| apply wbytes_grows].
      eapply mem_grows_trans; [| apply wbytes_grows]. apply wbytes_grows.
  Qed.

  (* [comment removed for export] *)
  #[using="Hspr"] Lemma rd_ra : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 8)) 8 = Some (W8 ra).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  #[using="Hspr"] Lemma rd_s0 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 16)) 8 = Some (W8 s0).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1.
    rewrite rdn_wbytes_out by (rewrite ?lenW8; u_norm; lia).
    apply rdn_wbytes_hit8. u_norm. lia.
  Qed.
  #[using="Hspr"] Lemma rd_s1 : forall ra s0 s1, rdn RSEGS (mem1 ra s0 s1) (Z_to_bv 64 (usp - 24)) 8 = Some (W8 s1).
  Proof.
    clear HOK HsK Hstk Hdisj. intros. pose proof (u64_range sp). unfold mem1. apply rdn_wbytes_hit8. u_norm. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac okstk :=
    repeat (eapply store_ok_mono; [apply wbytes_grows|]);
    eapply (store_ok_sub RSEGS mem (Z_to_bv 64 (usp - 32)) _ 32 8);
      [u_norm; lia | exact Hstk | u_norm; lia | u_norm; cbn; lia].

  Ltac kept_cs := cbv [callee_saved In]; tauto.

  (* [comment removed for export] *)
  Ltac msd F D aa :=
    chain_step; [reflexivity
      | eapply step_sd_at with (a := aa);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH; unfold v_addi; unorm; f_equal; lia
        | gres; rwH; reflexivity
        | okstk ]
      | step_simpl]; vnorm.
  (* [comment removed for export] *)
  Ltac mld8 F D vv RD :=
    chain_step; [reflexivity
      | eapply step_ld with (v := vv);
        [exact F | reflexivity | exact D
        | gres; imm_norm; rwH;
          lazymatch goal with |- rdn _ _ ?a _ = _ =>
            lazymatch type of RD with rdn _ _ ?c _ = _ =>
              replace a with c by (unfold v_addi; unorm; f_equal; lia) end end;
          exact RD
        | apply bytes_le_to_Z_8 ]
      | step_simpl]; vnorm.

  #[using="buf HOK HsK Hstk Hspr Hdisj"] Lemma strnlen_run : ltac2:(CDefT.buildp (gd_tbl_P_strnlen ()) "Pregs,(?.&5.(6.&40.))Pret,(6.&40.)P,(10.R1.)P,(<.(6.&40.)(11.R3.(12.&5.+1.$13.))R2.)P,(<.(6.&40.)(11.R4.(12.&5.+2.$13.))Vsp,)P,(<.(6.&40.)(11.R5.(12.&5.+:.$13.))Vs,)P,(<.(6.&40.)(11.R6.(12.&5.+;.$13.))(9.&40.Vn,))(14.(?.&5.(6.&40.))Lregs',(?.&5.(6.&40.))(15.(16.$17.(18.$19.R8.(12.&40.+46?3<.$13.)Vmem,Vrom,)(18.$19.R1.R7.(>.R7.(11.R8.(12.&5.+8.$13.))(11.R8.(12.&5.+9.$13.)))Vrom,))(15.(1:.R8.R1.)(<.(6.&40.)(11.R1.(12.&5.+:.$13.))(9.&40.VK,)))))")
(* [comment removed for export] *).
  Proof.
    intros regs ret Hret H1 H2 H10 H11.
    pose proof (u64_range sp) as Hsp. pose proof (u64_range s) as Hs.
    pose proof (KL _ _ _ _ _ HOK) as HKL.
    destruct HOK as [Hbuf Hwin Hnw HK0 _ _ HKn Hn64 Hro].
    set (s0 := getr regs 8). set (s1 := getr regs 9).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x46944 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 1 = (0x46f60 : word) /\ getr r 2 = Z_to_bv 64 (usp - 32)
                       /\ getr r 8 = Z_to_bv 64 n /\ getr r 9 = s
                       /\ getr r 10 = s /\ getr r 11 = Z_to_bv 64 0 /\ getr r 12 = Z_to_bv 64 n
                       /\ (forall x : reg, In x callee_saved -> x <> 1 -> x <> 2 -> x <> 8 -> x <> 9 -> getr r x = getr regs x))).
    { eexists. split.
      - stepiv F_437f0 D_437f0 (Z_to_bv 64 (usp - 32))
          ltac:(gres; imm_norm; rwH; unfold v_addi; f_equal; lia).   (* [comment removed for export] *)
        msd F_437f4 D_437f4 (Z_to_bv 64 (usp - 8)).                 (* [comment removed for export] *)
        msd F_437f8 D_437f8 (Z_to_bv 64 (usp - 16)).                (* [comment removed for export] *)
        msd F_437fc D_437fc (Z_to_bv 64 (usp - 24)).                (* [comment removed for export] *)
        stepn F_43800 D_43800.                                       (* [comment removed for export] *)
        stepn F_43804 D_43804.                                       (* [comment removed for export] *)
        stepn F_43808 D_43808.                                       (* [comment removed for export] *)
        stepn F_4380c D_4380c.                                       (* [comment removed for export] *)
        stepn F_43810 D_43810.                                       (* [comment removed for export] *)
        rwH. fold s0 s1. unfold mem1. apply mst_refl.
      - cbv beta. repeat split; gres; rwH; try reflexivity; try bveq.
        intros x Hx N1 N2 N8 N9. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [first [ exfalso; match goal with N : ?a <> ?a |- _ => apply N; reflexivity end
                 | gres; reflexivity ] |]).
        destruct Hx. }
    cbv beta. (intros r1 dd_H; ddestruct dd_H as (R1 & R2 & R8 & R9 & R10 & R11 & R12 & RK)).
    (* [comment removed for export] *)
    eapply (runs_trans RSEGS _ (fun r => mkst r (0x46f60 : word) (mem1 ret s0 s1) rom)
             (fun r => getr r 10 = Z_to_bv 64 (bv_unsigned s + K) /\ keeps_cs r1 r)).
    { ddestruct (ref_memchr0 (mem1 ret s0 s1) s buf K n rom r1 (0x46f60 : word) (HOK1 ret s0 s1)
                  ltac:(apply ret_ok_even; reflexivity) R1 R10 R11 R12) as (r & RUN & KC & A10).
      exists r. split; [exact RUN | split; [exact A10 | exact KC]]. }
    cbv beta. intros r2 (A10 & KC).
    assert (S2 : getr r2 2 = Z_to_bv 64 (usp - 32)) by (rewrite (KC 2) by kept_cs; exact R2).
    assert (S9 : getr r2 9 = s) by (rewrite (KC 9) by kept_cs; exact R9).
    (* [comment removed for export] *)
    eexists. split.
    - stepb_ft F_43814 D_43814 ltac:(rwH; apply c_eq_neq; unorm; lia).  (* [comment removed for export] *)
      stepiv F_43818 D_43818 (Z_to_bv 64 K)
        ltac:(gres; rwH; unfold v_sub; unorm; f_equal; lia).          (* [comment removed for export] *)
      stepn F_4381c D_4381c.                                         (* [comment removed for export] *)
      mld8 F_43820 D_43820 ret (rd_ra ret s0 s1).                    (* [comment removed for export] *)
      mld8 F_43824 D_43824 s0 (rd_s0 ret s0 s1).                     (* [comment removed for export] *)
      mld8 F_43828 D_43828 s1 (rd_s1 ret s0 s1).                     (* [comment removed for export] *)
      stepiv F_4382c D_4382c sp
        ltac:(gres; imm_norm; rwH; unfold v_addi; unorm; rewrite <- (Z_to_bv_bv_unsigned 64 sp) at 2; f_equal; lia).
                                                                     (* [comment removed for export] *)
      stepret F_43830 D_43830 ret ltac:(reflexivity).
      apply mst_refl.
    - split.
      + intros x Hx. pose proof Hx as Hx'. cbv [callee_saved In] in Hx.
        repeat (destruct Hx as [<-|Hx];
          [ gres; subst s0 s1; first [ symmetry; assumption | reflexivity
                  | rewrite (KC _ Hx'); apply (RK _ Hx'); intros E; discriminate E ] |]).
        destruct Hx.
      + gres. reflexivity.
  Qed.
End SNL.

Theorem ref_strnlen : ltac2:(CDefT.buildp (gd_tbl_P_strnlen ()) "Pmem,P,(6.&40.)(=.(6.&8.))Ps,(6.&40.)Psp,(6.&40.)Pbuf,(1;.(6.&8.))PK,$1<.Pn,$1<.Prom,P,(6.&40.)(=.(6.&8.))Pregs,(?.&5.(6.&40.))Pret,(6.&40.)P,(1=.R9.R8.R6.R5.R4.)P,(;.=(2.(3.&40.R9.)R6.))P,(<.$1>.(1?.$17.R;.(9.&40.(7.(3.&40.R9.)+20.))#20.)$20.)P,(1.+10<58.(7.(3.&40.R:.)+20.))P,(0.(1.(2.(3.&40.R<.)(4.(5.(6.&8.)R:.)))(7.(3.&40.R;.)+20.))(1.(3.&40.R;.)(3.&40.R<.)))P,(10.R6.)P,(<.(6.&40.)(11.R8.(12.&5.+1.$13.))R7.)P,(<.(6.&40.)(11.R9.(12.&5.+2.$13.))R>.)P,(<.(6.&40.)(11.R:.(12.&5.+:.$13.))R10.)P,(<.(6.&40.)(11.R;.(12.&5.+;.$13.))(9.&40.R=.))(14.(?.&5.(6.&40.))Lregs',(?.&5.(6.&40.))(14.P,(6.&40.)(=.(6.&8.))Lmem',P,(6.&40.)(=.(6.&8.))(15.(16.$17.(18.$19.R>.(12.&40.+46?3<.$13.)R15.R?.)(18.$19.R2.R=.R1.R?.))(15.(1:.R>.R2.)(15.(<.(6.&40.)(11.R2.(12.&5.+:.$13.))(9.&40.R11.))(21.R15.R1.(22.(23.(6.&40.)$1<.)(24.(6.&40.)$1<.(9.&40.(7.(3.&40.R13.)+20.))+20.)(25.(23.(6.&40.)$1<.)))))))))")
(* [comment removed for export] *).
Proof.
  intros mem s sp buf K n rom regs ret HOK HsK Hstk Hspr Hdisj Hret H1 H2 H10 H11.
  ddestruct (strnlen_run mem s sp buf K n rom HOK HsK Hstk Hspr Hdisj regs ret Hret H1 H2 H10 H11)
    as (r & RUN & KC & A10).
  dexists r, (mem1 mem sp ret (getr regs 8) (getr regs 9)).
  split; [exact RUN | split; [exact KC | split; [exact A10 | apply frame1; exact Hspr]]].
Qed.
