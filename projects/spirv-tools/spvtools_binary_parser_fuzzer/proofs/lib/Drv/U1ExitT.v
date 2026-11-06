(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require BvWfKernel.

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.spirv_tools.spvtools_binary_parser_fuzzer.images Require Import Ubsan.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib Require Import PropExec CatExec CatSim SeqExec StoreOk MemSplit Hoare ShapeAlg ShapeLaws Nodes RefNodes SymExec3 SymExec3Sound SymRun3 SymDrive3 SRealizes SNodes.
From OSSVerify.Proofs.spirv_tools.spvtools_binary_parser_fuzzer.lib.Drv Require Import SymExecA SymExecASound U1StartInit S1SpecConsts U1StdioDefs U1StdioWrite U1ExitKn U1ExitDefs U1Exit S1KnCut3 U1ExitTDefs U1_code_d1054_d2138 U1_code_d6138_d7138.
#[global] Unset Lia Cache. #[global] Unset Nia Cache. #[global] Unset Nra Cache.
Import ListNotations. Open Scope bv_scope.
Import SX2. Import SX2S. Import SXA. Import SXAS.

Abbreviation SEGS := Ubsan.M.loaded_segments.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Record exit_pre_tp (w : Z) (pend : list byte) (regs : bvmap 5 word) (mem : word -> option byte)
       (model : Model) (code : word) : Prop := {
  etp_sp    : (0x100010000 <= bv_unsigned (getr regs 2) <= 0x800000000000)%Z;
  etp_sp16  : (bv_unsigned (getr regs 2) mod 16 = 0)%Z;
  etp_stack : store_ok SEGS mem (Z_to_bv 64 (bv_unsigned (getr regs 2) - EXIT_STACK)) (Z.to_nat EXIT_STACK) = true;
  etp_tp    : getr regs 4 = Z_to_bv 64 0x102418;
  etp_a0    : getr regs 10 = code;
  etp_tid   : exists tid, (1 <= tid < 4194304)%Z /\
               rdn SEGS mem (Z_to_bv 64 0x102370) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 tid));
  etp_locale : rdn SEGS mem (Z_to_bv 64 0x1023e8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x1226e0));
  etp_nlocks : rdn SEGS mem (Z_to_bv 64 0x1226ab) 1 = Some (word_to_le_bytes 1 (Z_to_bv 64 0));
  etp_cxx   : cxx_cells_t_ok mem;
  etp_clear : Forall (fun iv => img_clear mem (fst iv) (snd iv)) (exit_clear_common ++ exit_clear_tp);

  etp_o_flags : rdn SEGS mem (Z_to_bv 64 0xf00e8) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 5));
  etp_o_rpos  : rdn SEGS mem (Z_to_bv 64 0xf00f0) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  etp_o_rend  : rdn SEGS mem (Z_to_bv 64 0xf00f8) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0));
  etp_o_wend  : rdn SEGS mem (Z_to_bv 64 0xf0108) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123408));
  etp_o_wpos  : rdn SEGS mem (Z_to_bv 64 0xf0110) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 w));
  etp_o_wbase : rdn SEGS mem (Z_to_bv 64 0xf0120) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0x123008));
  etp_o_write : rdn SEGS mem (Z_to_bv 64 0xf0130) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 0xd70d4));
  etp_o_mode  : rdn SEGS mem (Z_to_bv 64 0xf0170) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));
  etp_o_lbf   : rdn SEGS mem (Z_to_bv 64 0xf0178) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 0xffffffff));

  etp_can   : exists can, rdn SEGS mem (Z_to_bv 64 0x122688) 8 = Some (word_to_le_bytes 8 can);

  etp_pend  : rdn SEGS mem (Z_to_bv 64 0x123008) (length pend) = Some pend;
  etp_plen  : Z.of_nat (length pend) = (w - 0x123008)%Z;

  etp_fd1   : fd_lookup (m_fds model) (Z_to_bv 64 1) = Some (FdChannel (Z_to_bv 64 1));
  etp_halt  : m_halted model = None;
  etp_lazy  : m_vm_lazy model = []
}.

Section ExitTP.
  Context {fx : FPState}.

  Definition vals1 (regs : bvmap 5 word) (tid : Z) (can : word) : list word :=
    [getr regs 2; Z_to_bv 64 tid; getr regs 10] ++ junk_vals regs ++ [can; 0; 0; 0; 0].

  Lemma vals1_len : forall regs tid can, length (vals1 regs tid can) = 40%nat.
  Proof. intros. reflexivity. Qed.

  Ltac kw_lit H := eapply (kword_lit_intro _ _ _ _ _ _ ); [cbn; lia | lia | cbn; lia | exact H | vm_compute; reflexivity].

  Ltac evl := lazy [edenot ev vals_ev vals1 junk_vals nth app map seq N.to_nat Pos.to_nat Pos.iter_op Nat.add length].

  Lemma tp_entry : forall w pend regs mem model code,
    exit_pre_tp w pend regs mem model code ->
    exists tid can,
      (1 <= tid < 4194304)%Z /\
      regs_ok (Env (vals_ev (vals1 regs tid can)) (fun _ => [])) sr_exit regs /\
      know_ok SEGS (Env (vals_ev (vals1 regs tid can)) (fun _ => [])) mem (kn_exit_tp w).
  Proof.
    intros w pend regs mem model code PRE.
    destruct (etp_tid _ _ _ _ _ _ PRE) as (tid & Htid & Hrtid).
    destruct (etp_can _ _ _ _ _ _ PRE) as (can & Hcan).
    exists tid, can. split; [exact Htid|].
    pose proof (etp_sp _ _ _ _ _ _ PRE) as Hsp. pose proof (etp_sp16 _ _ _ _ _ _ PRE) as Hal.
    set (E := Env (vals_ev (vals1 regs tid can)) (fun _ => [])).
    split.
    - apply regs_ok_by_index. intros i Hi.
      destruct i as [|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|[|i]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]]; [ .. | lia];
        cbn [nth sr_exit all_regs]; subst E; evl;
        first [ reflexivity | exact (etp_tp _ _ _ _ _ _ PRE) | f_equal; apply bv_eq; reflexivity ].
    - pose proof (etp_clear _ _ _ _ _ _ PRE) as HC. unfold exit_clear_common, exit_clear_tp, exit_clear_t0 in HC. cbn [app] in HC.
      repeat match type of HC with Forall _ (_ :: _) => apply Forall_cons_iff in HC; destruct HC as [? HC] end.
      cbn [fst snd] in *.
      pose proof (kn_cxx_t_ok E mem (etp_cxx _ _ _ _ _ _ PRE)) as HKC.
      unfold kn_exit_tp, kn_exit_common0, kn_tp_extra.
      unfold know_ok. rewrite !Forall_app. split; [|split; [exact HKC|]].
      all: repeat apply Forall_cons; try apply Forall_nil.
      all: try (apply kimg_intro; [lia | lia | assumption]).
      + cbn [kentry_ok]. subst E; evl. lia.
      + cbn [kentry_ok]. subst E; evl. split; [lia | exact Hal].
      + cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off]. subst E; evl.
        unfold EXIT_STACK. rewrite (u_small64 1024) by lia. split; [lia|]. intros d m Hd Hm.
        eapply store_ok_sub; [ | exact (etp_stack _ _ _ _ _ _ PRE) | | ]; unfold EXIT_STACK; rewrite ?u_small64 by lia;
          rewrite ?Z2Nat.id by lia; lia.
      + cbn [kentry_ok a_base a_off]. unfold flat, estart, elenZ. cbn [a_base a_off edenot].
        rewrite (u_small64 0) by lia. rewrite (u_small64 217088) by lia. split; [lia|]. intros d m Hd Hm.
        apply store_ok_of_all; [rewrite u_small64 by lia; lia|]. intros x Hx. rewrite u_small64 in Hx by lia.
        apply rw_wview. lia.
      + cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off]. subst E; evl.
        rewrite (u_small64 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. exact Hrtid.
      + cbn [kentry_ok]. subst E; evl. rewrite u_small64 by lia. lia.
      + kw_lit (etp_locale _ _ _ _ _ _ PRE).
      + kw_lit (etp_nlocks _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_flags _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_rpos _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_rend _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_wend _ _ _ _ _ _ PRE).
      +   apply kword_rdn_intro; [cbn; lia | lia | cbn; lia | exact (etp_o_wpos _ _ _ _ _ _ PRE)].
      + kw_lit (etp_o_wbase _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_write _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_mode _ _ _ _ _ _ PRE).
      + kw_lit (etp_o_lbf _ _ _ _ _ _ PRE).
      +   cbn [kentry_ok a_base a_off]. split; [lia|]. unfold flat, estart, adenot. cbn [a_base a_off]. subst E; evl.
        rewrite (u_small64 0) by lia. split; [lia|]. unfold v_addi. rewrite (u_small64 0) by lia. exact Hcan.
  Qed.

  Lemma edenot_sp_off : forall vals ebs k,
    edenot (Env (vals_ev vals) ebs) (EAlu ALU_ADD (EVar 0) (ELit k)) = Z_to_bv 64 (bv_unsigned (vals_ev vals 0) + k).
  Proof.
    intros vals ebs k. cbn [edenot ev]. rewrite alu_add. unfold v_add. apply bv_eq.
    rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. rewrite Zplus_mod_idemp_r. reflexivity.
  Qed.

  Ltac krd3 HK a n H :=
    lazymatch type of HK with know_ok ?segs ?Ee ?Mm ?kn =>
      let r := eval vm_compute in (SymDrive3.kread segs kn (ELit 0) a n) in
      lazymatch r with
      | Some ?v =>
        pose proof (SymDrive3.kread_rdn segs Ee Mm kn (ELit 0) a n v HK ltac:(vm_compute; reflexivity) ltac:(lia) ltac:(lia)
                     ltac:(unfold flat, estart; cbn [a_base a_off edenot]; rewrite (u_small64 0) by lia; lia)) as H;
        unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; rewrite (u_small64 0), Z.add_0_l in H by lia
      | None => fail "krd3: knowledge does not determine this read"
      end end.

End ExitTP.
