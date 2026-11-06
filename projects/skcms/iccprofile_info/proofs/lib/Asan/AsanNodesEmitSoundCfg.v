(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import FunctionalExtensionality.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import
  PropExec CatExec CatSim SeqExec StoreOk StepTac ShapeAlg SpinAlg AgentLib Hoare RefMemcpyLib
  AsanAcct AsanAcctShape.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AxSymExec3 AxSymExec3Sound AxSymRun3 AsanPlanCore AsanPlan AsanPlanSound.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanAcctNoLazy.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import ArgLoops AsanNodesArg.
Unset Nia Cache.  (* [comment removed for export] *)
Import ListNotations.
Import AX2. Import AX2S. Import APC. Import AP. Import APS. Import AN.
Unset Lia Cache.
Open Scope Z_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import AsanNodesArgSoundCfg.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Asan Require Import SpinAlgCfg AsanPlanSoundCfg.
From Stdlib Require Import Zify.
(* [comment removed for export] *)
Local Ltac el_lia_core := first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                                | Zify.zify; xlia zchecker ].
Local Ltac el_goal_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif el_goal_has_var then el_lia_core else first [ solve [clear; el_lia_core] | el_lia_core ].
Section WithFP1. Context {FP : PropExec.FPState}.
Section NodesArg.
  (* [comment removed for export] *)
  Variable SEGS : list Segment.
  Variable A : atable.
  Variable nx0 : nat.
  Variable LIMIT : Z.
  Variable SINV : env -> (word -> option byte) -> Prop.
  Variable argH : env -> word -> bool.
  Variable FS0 : Fs.Fs.
  Hypothesis SEGS_wx : wx_segs_nowrap SEGS.
  Hypothesis SEGS_in_hull : forall a : word, in_hull A (bv_unsigned a) = false -> find_segment SEGS (bv_unsigned a) 1 = None.
  Hypothesis HULL_ok : hull_ok A.
  Hypothesis argH_high : forall E (a : word), argH E a = true -> CEIL <= bv_unsigned a.
  Hypothesis argH_agree : forall E E' (a : word), env_agree nx0 E E' -> argH E a = argH E' a.
  Hypothesis SINV_frame : forall E M M', (forall a, argH E a = true -> M' a = M a) -> SINV E M -> SINV E M'.
  Hypothesis SINV_agree : forall E E' M, env_agree nx0 E E' -> SINV E M -> SINV E' M.
  Hypothesis NX0_sp : nx0_sp_ok nx0.   (* [comment removed for export] *)

  Let G : argtab := argtab_of A.

  (* [comment removed for export] *)
  Variables wi0 wi1 wi2 wi3 wi4 wi5 wi6 : bv 32.
  Hypothesis Xis : 0 <= g_istrlen G /\ g_istrlen G + 28 < 2 ^ 64.
  Hypothesis Fi0 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G)) = Some wi0.
  Hypothesis Fi1 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 4)) = Some wi1.
  Hypothesis Fi2 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 8)) = Some wi2.
  Hypothesis Fi3 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 12)) = Some wi3.
  Hypothesis Fi4 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 16)) = Some wi4.
  Hypothesis Fi5 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 20)) = Some wi5.
  Hypothesis Fi6 : fetch_word SEGS (Z_to_bv 64 (g_istrlen G + 24)) = Some wi6.
  Hypothesis Ei : is_ecall wi0 = false /\ is_ecall wi1 = false /\ is_ecall wi2 = false /\ is_ecall wi3 = false
                  /\ is_ecall wi4 = false /\ is_ecall wi5 = false /\ is_ecall wi6 = false.
  Hypothesis Di0 : decode_any wi0 = Some (OpImm ALU_ADD 11 0 0, 4%Z).
  Hypothesis Di1 : decode_any wi1 = Some (Op ALU_ADD 12 10 11, 4%Z).
  Hypothesis Di2 : decode_any wi2 = Some (Load SZ1 false 12 12 0, 4%Z).
  Hypothesis Di3 : decode_any wi3 = Some (OpImm ALU_ADD 11 11 1, 4%Z).
  Hypothesis Di4 : decode_any wi4 = Some (Branch BC_NE 12 0 8180, 4%Z).
  Hypothesis Di5 : decode_any wi5 = Some (OpImm ALU_ADD 10 11 4095, 4%Z).
  Hypothesis Di6 : decode_any wi6 = Some (Jalr 0 1 0, 4%Z).

  (* [comment removed for export] *)
  Variables usp STR0 TOP argc : Z.
  Variables argv0 argv1 : list byte.
  Let L0 : Z := Z.of_nat (length argv0).
  Let L1 : Z := Z.of_nat (length argv1).
  Let STR1 : Z := STR0 + L0 + 1.
  #[local] Notation STR := (AsanNodesArgSoundCfg.STR STR0 argv0).
  #[local] Notation ARG := (AsanNodesArgSoundCfg.ARG argv0 argv1).
  #[local] Notation LEN := (AsanNodesArgSoundCfg.LEN argv0 argv1).
  (* [comment removed for export] *)
  #[local] Notation arg_ok := (AsanNodesArgSoundCfg.arg_ok argc).

  Hypothesis Lay : 0x7fff80000000 <= usp /\ usp + 192 <= STR0 /\ STR0 + L0 + 1 <= TOP
                   /\ (2 <= argc -> STR1 + L1 + 1 <= TOP)
                   /\ TOP mod 8 = 0 /\ TOP + 16 <= 2 ^ 47 /\ L0 <= 131071 /\ L1 <= 131071 /\ 1 <= argc <= 1024.
  Hypothesis Hnz : forall i j, (j < length (ARG i))%nat -> bv_unsigned (byte_at (ARG i) j) <> 0.

  Hypothesis SINV_vals : forall E M, SINV E M ->
    uE E e_sp0 = usp /\ uE E e_str0 = STR0 /\ edenot E (EVar V_L0) = Z_to_bv 64 L0
    /\ edenot E (EVar V_ARGC) = Z_to_bv 64 argc /\ edenot E (EVar V_L1) = Z_to_bv 64 L1
    /\ eb E 1%nat = argv0 /\ eb E 2%nat = argv1.
  (* [comment removed for export] *)
  Hypothesis SINV_rd : forall E M (a : word), SINV E M -> STR0 <= bv_unsigned a < TOP -> exists b, M a = Some b.
  (* [comment removed for export] *)
  Hypothesis SINV_str : forall E M i j, SINV E M -> arg_ok i -> (j <= length (ARG i))%nat ->
    M (Z_to_bv 64 (STR i + Z.of_nat j)) = Some (byte_at (ARG i) j).

  #[local] Notation CSOK := (cs_ok SEGS A LIMIT SINV argH FS0) (only parsing).

  (* [comment removed for export] *)
  Hypothesis Gro_hull : img_lo A <= g_ro_lo G /\ g_ro_hi G <= img_hi A.

  (* [comment removed for export] *)
  Hypothesis STDIO : forall (H : word -> bool) regs mem model (su f wb wp fd : Z) (s l bufp bufsz can ret : word)
         (pending extra : list byte) (K : TSet),
    H_off_segments SEGS H -> lazy_all_hidden H model ->
    range_avoids H (Z_to_bv 64 (su - 112)) 112 -> range_avoids H (Z_to_bv 64 wb) (length pending) -> range_avoids H s (length extra) ->
    getr regs 2%bv = Z_to_bv 64 su -> getr regs 10%bv = Z_to_bv 64 f -> getr regs 11%bv = s -> getr regs 12%bv = l -> getr regs 1%bv = ret ->
    4294967296 + 112 <= su -> su <= 0x800000000000 ->
    store_ok SEGS mem (Z_to_bv 64 (su - 112)) 112 = true ->
    g_file_lo G <= f -> f + 232 <= g_file_hi G ->
    rdn SEGS mem (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wp)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 wb)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 120)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 fd)) ->
    rdn SEGS mem (Z_to_bv 64 (f + 88)) 8 = Some (word_to_le_bytes 8 bufp) ->
    rdn SEGS mem (Z_to_bv 64 (f + 96)) 8 = Some (word_to_le_bytes 8 bufsz) ->
    rdn SEGS mem (Z_to_bv 64 (g_canary_got G)) 8 = Some (word_to_le_bytes 8 (Z_to_bv 64 (g_canary G))) ->
    rdn SEGS mem (Z_to_bv 64 (g_canary G)) 8 = Some (word_to_le_bytes 8 can) ->
    0 < fd < 2147483648 ->
    fd_lookup (m_fds model) (Z_to_bv 64 fd) = Some (FdChannel (Z_to_bv 64 fd)) ->
    m_halted model = None ->
    0 <= wb <= wp -> wp <= 0x800000000000 -> wp - wb = Z.of_nat (length pending) -> bv_unsigned l = Z.of_nat (length extra) ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    Z.of_nat (length pending) + Z.of_nat (length extra) <= 2 ^ 30 ->
    (wp <= su - 112 \/ su <= wb) -> (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s) ->
    bv_unsigned s + bv_unsigned l <= 0x800000000000 ->
    rdn SEGS mem (Z_to_bv 64 wb) (length pending) = Some pending -> rdn SEGS mem s (length extra) = Some extra ->
    ret_ok ret -> K [] ->
    (forall regs' mem',
       getr regs' 10%bv = l -> getr regs' 2%bv = Z_to_bv 64 su -> getr regs' 1%bv = ret ->
       getr regs' 8%bv = getr regs 8%bv -> getr regs' 9%bv = getr regs 9%bv ->
       getr regs' 18%bv = getr regs 18%bv -> getr regs' 19%bv = getr regs 19%bv -> getr regs' 20%bv = getr regs 20%bv ->
       getr regs' 21%bv = getr regs 21%bv -> getr regs' 22%bv = getr regs 22%bv -> getr regs' 23%bv = getr regs 23%bv ->
       getr regs' 24%bv = getr regs 24%bv -> getr regs' 25%bv = getr regs 25%bv -> getr regs' 26%bv = getr regs 26%bv ->
       getr regs' 27%bv = getr regs 27%bv -> getr regs' 3%bv = getr regs 3%bv -> getr regs' 4%bv = getr regs 4%bv ->
       (forall x : word, ~ (su - 112 <= bv_unsigned x < su) -> ~ (f + 32 <= bv_unsigned x < f + 48) ->
                          ~ (f + 56 <= bv_unsigned x < f + 64) -> mem' x = mem x) ->
       mem_grows mem mem' ->
       rdn SEGS mem' (Z_to_bv 64 (f + 32)) 8 = Some (word_to_le_bytes 8 (v_add bufp bufsz)) ->
       rdn SEGS mem' (Z_to_bv 64 (f + 40)) 8 = Some (word_to_le_bytes 8 bufp) ->
       rdn SEGS mem' (Z_to_bv 64 (f + 56)) 8 = Some (word_to_le_bytes 8 bufp) ->
       srealizes_cfg SEGS (mkCfg (mkst regs' ret mem' (seg_rom SEGS)) model) K) ->
    srealizes_cfg SEGS (mkCfg (mkst regs (Z_to_bv 64 (g_stdio_write G)) mem (seg_rom SEGS)) model)
             (t_emit (map (WriteEv (Z_to_bv 64 fd)) (pending ++ extra)) K).
  Hypothesis Gfile : img_lo A <= g_file_lo G /\ g_file_hi G <= img_hi A /\ img_lo A <= g_canary_got G /\ g_canary_got G + 8 <= img_hi A
                     /\ img_lo A <= g_canary G /\ g_canary G + 8 <= img_hi A.

  (* [comment removed for export] *)
  #[local] Notation inr := (AsanNodesArgSoundCfg.inr).

  (* [comment removed for export] *)
  #[local] Notation adenot_abs0_i := (adenot_abs0 STR0 TOP argv0 argv1).
  #[local] Notation after_call_cs_ok_i := (after_call_cs_ok SEGS A nx0 LIMIT SINV argH FS0 argH_agree SINV_frame SINV_agree NX0_sp).
  #[local] Notation extra_pieces_sound_i := (extra_pieces_sound SEGS A SINV argH SEGS_in_hull HULL_ok argH_high usp STR0 TOP argc argv0 argv1 Lay SINV_vals SINV_str).
  #[local] Notation flat_abs0_i := (flat_abs0 STR0 TOP argv0 argv1).
  #[local] Notation kimg_cut_sound_i := (kimg_cut_sound SEGS usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation know_ok_havoc3_i := (know_ok_havoc3 SEGS A wi0 wi1 wi2 wi3 wi4 wi5 wi6 Xis Ei usp STR0 TOP argc argv0 argv1 Lay Gro_hull Gfile).
  #[local] Notation kread8e_rdn_i := (kread8e_rdn SEGS STR0 TOP argv0 argv1).
  #[local] Notation kreadZ_rdn_i := (kreadZ_rdn SEGS usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation kwritable_sound_i := (kwritable_sound SEGS usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation lazyH_off_segments_i := (lazyH_off_segments SEGS A LIMIT SINV argH FS0 SEGS_in_hull usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation off_lazy_avoids_i := (off_lazy_avoids SEGS A LIMIT SINV argH FS0 usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation off_lazy_sound_i := (off_lazy_sound SEGS A usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation alloc_top_e_sp0_i := (alloc_top_e_sp0 SEGS A LIMIT SINV argH FS0 usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation pieces_walk_sound_i := (pieces_walk_sound SEGS usp STR0 TOP argc argv0 argv1 Lay).
  #[local] Notation rdn_Mr_FULL_i := (rdn_Mr_FULL SEGS A argH SEGS_in_hull HULL_ok argH_high).
  #[local] Notation store_ok_Mr_FULL_i := (store_ok_Mr_FULL SEGS A argH).
  #[local] Notation store_ok_not_hid_i := (store_ok_not_hid SEGS A argH SEGS_in_hull HULL_ok argH_high).
  #[local] Notation emit_stmt' := (emit_stmt' SEGS A nx0 LIMIT SINV argH FS0).

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
  Theorem xe_sound : emit_stmt'.
  Proof.
    intros id args cs fd ps cs' E R FULL model T HC Hn HT Hk.
    unfold xe in Hn. destruct id as [|id]; [|discriminate]. rewrite node_stdio_write_eq in Hn. (* [comment removed for export] *) unfold node_stdio_write_ref in Hn. fold G in Hn.
    pose proof (co_know _ _ _ _ _ _ _ _ _ _ _ HC) as HK. pose proof (co_sinv _ _ _ _ _ _ _ _ _ _ _ HC) as HS.
    set (MR := Mr A argH E cs model FULL) in HK.
    destruct (ret_lit cs) as [ret|] eqn:Hret; [|discriminate].
    destruct (reg_lit cs 10) as [f|] eqn:H10; [|discriminate].
    destruct (negb (Z.eqb (pc cs) (g_stdio_write G) && Z.leb (g_file_lo G) f && Z.leb (f + 232) (g_file_hi G))) eqn:Hf; [discriminate|].
    apply negb_false_iff in Hf. apply andb_prop in Hf as [Hf Hfhi]. apply andb_prop in Hf as [Hpc Hflo].
    apply Z.eqb_eq in Hpc. apply Z.leb_le in Hflo. apply Z.leb_le in Hfhi.
    destruct (kreadZ SEGS (kn cs) (ELit 0) (f + 120) 4) as [fd'|] eqn:Hfd; [|discriminate].
    destruct (kread8e SEGS (kn cs) (ELit 0) (f + 40)) as [WP|] eqn:Hwp; [|discriminate].
    destruct (kread8e SEGS (kn cs) (ELit 0) (f + 56)) as [WB|] eqn:Hwb; [|discriminate].
    destruct (kread8e SEGS (kn cs) (ELit 0) (f + 88)) as [bufp|] eqn:Hbufp; [|discriminate].
    destruct (kread8e SEGS (kn cs) (ELit 0) (f + 96)) as [bufsz|] eqn:Hbufsz; [|discriminate].
    destruct (kreadZ SEGS (kn cs) (ELit 0) (g_canary_got G) 8) as [cg|] eqn:Hcg; [|discriminate].
    destruct (kread8e SEGS (kn cs) (ELit 0) (g_canary G)) as [canv|] eqn:Hcan; [|discriminate].
    set (spm := eaddz (reg cs 2) (-112)) in Hn.
    destruct (split_lit spm) as [qb qk] eqn:Hsq.
    destruct (pieces_walk SEGS PIECES_FUEL (kn cs) WB WP [] []) as [pend|] eqn:Hpend; [|discriminate].
    destruct (extra_pieces SEGS (kn cs) (reg cs 11) (reg cs 12)) as [extra|] eqn:Hextra; [|discriminate].
    destruct (xlo (kn cs) (reg cs 2)) as [splo|] eqn:Hsplo; [|discriminate].
    destruct (xhi (kn cs) (reg cs 2)) as [sphi|] eqn:Hsphi; [|discriminate].
    destruct (xhi (kn cs) (esub WP WB)) as [nphi|] eqn:Hnphi; [|discriminate].
    destruct (xhi (kn cs) (reg cs 12)) as [lhi|] eqn:Hlhi; [|discriminate].
    destruct (xhi (kn cs) (reg cs 11)) as [shi|] eqn:Hshi; [|discriminate].
    destruct (xlo (kn cs) WB) as [wblo|] eqn:Hwblo; [|discriminate].
    destruct (xhi (kn cs) WP) as [wphi|] eqn:Hwphi; [|discriminate].
    match type of Hn with (if ?c then _ else _) = _ => destruct c eqn:Hcond; [|discriminate] end.
    set (k0 := kimg_cut (kimg_cut (kn cs) (f + 32) 16) (f + 56) 8) in Hn.
    set (k1 := kn_havoc k0 qb qk (ELit 112)) in Hn.
    set (k2 := kn_havoc k1 (ELit 0) (f + 32) (ELit 16)) in Hn.
    set (k3 := kn_havoc k2 (ELit 0) (f + 56) (ELit 8)) in Hn.
    set (k4 := KWord (SA (ELit 0) (f + 32)) 8 (eadd bufp bufsz)
               :: KWord (SA (ELit 0) (f + 40)) 8 bufp :: KWord (SA (ELit 0) (f + 56)) 8 bufp :: k3) in Hn.
    destruct (after_call nx0 cs ret (Some (reg cs 12)) k4) as [csa|] eqn:Hac; [|discriminate].
    lazymatch type of Hn with Some (?a, ?b, ?c) = Some (fd, ps, cs') =>
      assert (Efd : fd = a) by congruence; assert (Eps : ps = b) by congruence; assert (Ecs : cs' = c) by congruence end.
    clear Hn. subst fd ps cs'.
    (* [comment removed for export] *)
    apply andb_prop in Hcond as [Hcond Vbufsz]. apply andb_prop in Hcond as [Hcond Vbufp].
    apply andb_prop in Hcond as [Hcond OFFs]. apply andb_prop in Hcond as [Hcond OFFw]. apply andb_prop in Hcond as [Hcond Hfr]. apply andb_prop in Hcond as [Hcond Hceil].
    apply andb_prop in Hcond as [Hcond Hds]. apply andb_prop in Hcond as [Hcond Hdw]. apply andb_prop in Hcond as [Hcond Hwbwp].
    apply andb_prop in Hcond as [Hcond Hsl64]. apply andb_prop in Hcond as [Hcond Hsphi']. apply andb_prop in Hcond as [Hcond Hsplo'].
    apply andb_prop in Hcond as [Hcond Hrw]. apply andb_prop in Hcond as [Hcond Hmax].
    apply andb_prop in Hcond as [Hcond Hwphi']. apply andb_prop in Hcond as [Hcond Hwblo'].
    apply andb_prop in Hcond as [Hfd12 Hcgv].
    apply Z.eqb_eq in Hcgv. apply Z.leb_le in Hwblo'. apply Z.leb_le in Hwphi'. apply Z.leb_le in Hmax.
    apply Z.leb_le in Hsplo'. apply Z.leb_le in Hsphi'. rename Hsl64 into Hsl64b. apply Z.leb_le in Hceil. unfold two64 in *.
    pose proof HULL_ok as HU; unfold hull_ok in HU. destruct Gfile as (Gf1 & Gf2 & Gf3 & Gf4 & Gf5 & Gf6). unfold KHI in HU.
    (* [comment removed for export] *)
    destruct (ret_lit_facts cs ret Hret) as (Hr1 & Hrr & Hre). unfold two64 in Hrr.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 1 HC ltac:(lia)) as R1. rewrite Hr1, edenot_lit in R1.
    destruct (reg_lit_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 10 f HC ltac:(lia) H10) as [R10 _].
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 2 HC ltac:(lia)) as R2.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 11 HC ltac:(lia)) as R11.
    pose proof (reg_sound SEGS A LIMIT SINV argH FS0 E cs R FULL model 12 HC ltac:(lia)) as R12.
    replace (Z_to_bv 5 (Z.of_nat 1)) with (1%bv : bv 5) in R1 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 2)) with (2%bv : bv 5) in R2 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 10)) with (10%bv : bv 5) in R10 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 11)) with (11%bv : bv 5) in R11 by (apply bv_eq; reflexivity).
    replace (Z_to_bv 5 (Z.of_nat 12)) with (12%bv : bv 5) in R12 by (apply bv_eq; reflexivity).
    assert (Hrok : ret_ok (Z_to_bv 64 ret)) by (apply ret_ok_even; rewrite u64_lit by lia; exact Hre).
    set (sp := edenot E (reg cs 2)) in *. set (su := bv_unsigned sp).
    set (s := edenot E (reg cs 11)) in *. set (l := edenot E (reg cs 12)) in *.
    pose proof (xlo_sound SEGS E MR (kn cs) _ _ HK Hsplo) as Hsplo2. fold sp su in Hsplo2.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hsphi) as Hsphi2. fold sp su in Hsphi2.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hshi) as Hshi2. fold s in Hshi2.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hlhi) as Hlhi2. fold l in Hlhi2.
    (* [comment removed for export] *)
    assert (Hsl64 : bv_unsigned s + bv_unsigned l <= 0x800000000000).
    { apply orb_prop in Hsl64b as [X|X]; [apply Z.leb_le in X; lia|].
      destruct (xhi (kn cs) (eadd (reg cs 11) (reg cs 12))) as [h|] eqn:Hh; [|discriminate X].
      apply andb_prop in X as [X1 X2]. apply Z.leb_le in X1. apply Z.ltb_lt in X2.
      pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hh) as Gsl.
      assert (Ue : bv_unsigned (edenot E (eadd (reg cs 11) (reg cs 12))) = (bv_unsigned s + bv_unsigned l) mod 2 ^ 64)
        by (unfold eadd; rewrite mkAlu_denot; apply u_add64).
      rewrite Ue in Gsl. rewrite Z.mod_small in Gsl by (pose proof (u64_range s); pose proof (u64_range l); lia). lia. }
    clear Hsl64b.
    pose proof (xlo_sound SEGS E MR (kn cs) _ _ HK Hwblo) as Hwblo2.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hwphi) as Hwphi2.
    pose proof (xhi_sound SEGS E MR (kn cs) _ _ HK Hnphi) as Hnphi2.
    pose proof (u64_range s) as Hsr. pose proof (u64_range sp) as Hspr. fold su in Hspr. pose proof (u64_range l) as Hlr.
    set (wb := bv_unsigned (edenot E WB)) in *. set (wp := bv_unsigned (edenot E WP)) in *.
    (* [comment removed for export] *)
    assert (Hspm : edenot E spm = Z_to_bv 64 (su - 112)).
    { subst spm. unfold eaddz. rewrite mkAlu_denot. fold sp. rewrite edenot_lit, alu_add. unfold v_add. apply bv_eq.
      rewrite !Z_to_bv_unsigned, !bv_wrap64_mod. fold su. rewrite Z.add_mod_idemp_r by lia. f_equal; lia. }
    pose proof (split_lit_denot E spm qb qk Hsq) as Hsqd. rewrite Hspm in Hsqd.
    (* [comment removed for export] *)
    destruct (SINV_vals E _ HS) as (Usp & _).
    assert (FR : usp - 8388608 <= su - 112).
    { pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK Hfr) as X. rewrite !xt_den_1 in X. rewrite Hspm, u64_lit in X by lia.
      unfold STK_OFF in X. unfold uE in Usp. lia. }
    pose proof (alloc_top_e_sp0_i E cs R FULL model HC) as AT. rewrite Usp in AT.
    destruct (kwritable_sound_i E MR (kn cs) (kn cs) qb qk 112 HK HK Hrw ltac:(lia)) as (Wst & W0 & Wnw).
    assert (Hq : estart E (SA qb qk) = su - 112).
    { unfold estart. cbn [a_base a_off]. apply (f_equal bv_unsigned) in Hsqd. rewrite !u64_lit in Hsqd by (unfold estart in W0, Wnw; cbn [a_base a_off] in W0, Wnw; lia). lia. }
    rewrite Hq in Wst. change (Z.to_nat 112) with 112%nat in Wst.
    (* [comment removed for export] *)
    assert (FL : forall off n, 0 <= off -> 0 <= n -> off + n <= img_hi A -> flat E (SA (ELit 0) off) n).
    { intros off n A0 B0 C0. apply flat_abs0_i; lia. }
    destruct (kreadZ_rdn_i E MR (kn cs) (ELit 0) (f + 120) 4 fd' HK Hfd ltac:(lia) ltac:(apply FL; lia)) as (Rfd & Hfdr & _).
    change (8 * Z.of_nat 4) with 32 in Hfdr.
    pose proof (kread8e_rdn_i E MR (kn cs) (ELit 0) (f + 40) WP HK Hwp ltac:(apply FL; lia)) as Rwp.
    pose proof (kread8e_rdn_i E MR (kn cs) (ELit 0) (f + 56) WB HK Hwb ltac:(apply FL; lia)) as Rwb.
    pose proof (kread8e_rdn_i E MR (kn cs) (ELit 0) (f + 88) bufp HK Hbufp ltac:(apply FL; lia)) as Rbufp.
    pose proof (kread8e_rdn_i E MR (kn cs) (ELit 0) (f + 96) bufsz HK Hbufsz ltac:(apply FL; lia)) as Rbufsz.
    destruct (kreadZ_rdn_i E MR (kn cs) (ELit 0) (g_canary_got G) 8 cg HK Hcg ltac:(lia) ltac:(apply FL; lia)) as (Rcg & _ & _).
    pose proof (kread8e_rdn_i E MR (kn cs) (ELit 0) (g_canary G) canv HK Hcan ltac:(apply FL; lia)) as Rcan.
    rewrite adenot_abs0_i in Rfd, Rwp, Rwb, Rbufp, Rbufsz, Rcg, Rcan by lia.
    apply (rdn_Mr_FULL_i E cs model FULL) in Rfd. apply (rdn_Mr_FULL_i E cs model FULL) in Rwp. apply (rdn_Mr_FULL_i E cs model FULL) in Rwb.
    apply (rdn_Mr_FULL_i E cs model FULL) in Rbufp. apply (rdn_Mr_FULL_i E cs model FULL) in Rbufsz.
    apply (rdn_Mr_FULL_i E cs model FULL) in Rcg. apply (rdn_Mr_FULL_i E cs model FULL) in Rcan.
    (* [comment removed for export] *)
    destruct (pieces_walk_sound_i E MR (kn cs) PIECES_FUEL WB WP [] [] pend wb [] HK Hpend eq_refl ltac:(lia)
                ltac:(cbn; unfold uE; lia) eq_refl) as (pendb & Epend & Rpend & Lpend).
    unfold uE in Lpend. fold wp in Lpend. cbn [length Z.of_nat] in Lpend |- *.
    pose proof (rdn_Mr_FULL_i E cs model FULL _ _ _ Rpend) as RpendF.
    (* [comment removed for export] *)
    destruct (extra_pieces_sound_i E cs model FULL (kn cs) (reg cs 11) (reg cs 12) extra HS HK Hextra)
      as (extrab & Eextra & Rextra & Lextra & Bextra & Cextra). fold s l in Rextra, Lextra, Bextra, Cextra.
    (* [comment removed for export] *)
    pose proof (lin_ge0_sound SEGS E MR (kn cs) _ _ HK Hwbwp) as Dwbwp. cbn [xt_den] in Dwbwp. fold wb wp in Dwbwp.
    assert (Dw : (wp <= su - 112 \/ su <= wb)%Z).
    { apply orb_prop in Hdw as [Hx|Hx]; apply (lin_ge0_sound SEGS E MR (kn cs)) in Hx; [|exact HK| |exact HK];
        cbn [xt_den] in Hx; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold sp su wb wp in Hx; lia. }
    assert (Ds : (bv_unsigned s + bv_unsigned l <= su - 112 \/ su <= bv_unsigned s)%Z).
    { apply orb_prop in Hds as [Hx|Hx]; apply (lin_ge0_sound SEGS E MR (kn cs)) in Hx; [|exact HK| |exact HK];
        cbn [xt_den] in Hx; rewrite ?Hspm in Hx; rewrite ?u64_lit in Hx by lia; fold s l sp su in Hx; lia. }
    (* [comment removed for export] *)
    assert (OFFw' : (img_lo A <= wb /\ wp <= img_hi A) \/ usp - 8388608 <= wb).
    { destruct (xhi (kn cs) (eadd WB (esub WP WB))) as [h1|] eqn:E1; [|unfold off_lazy in OFFw; rewrite E1 in OFFw; discriminate].
      pose proof (off_lazy_sound_i E MR (kn cs) WB (esub WP WB) h1 wblo HK OFFw E1 Hwblo) as X.
      unfold eadd, esub in X. rewrite !mkAlu_denot in X. cbn [edenot] in X. rewrite u_add64, u_sub64 in X. fold wb wp in X.
      rewrite (Z.mod_small (wp - wb)), Z.mod_small in X by lia. lia. }
    assert (OFFs' : extrab <> [] -> (img_lo A <= bv_unsigned s /\ bv_unsigned s + bv_unsigned l <= img_hi A) \/ usp - 8388608 <= bv_unsigned s).
    { intros Hne. assert (X : off_lazy A (kn cs) (reg cs 11) (reg cs 12) = true).
      { destruct (reg cs 12) as [z| | | | | | |]; try exact OFFs. destruct z as [|p|p]; try exact OFFs.
        exfalso. apply Hne. destruct extrab; [reflexivity|]. cbn [length] in Lextra. subst l. rewrite edenot_lit, u64_lit in Lextra by lia. lia. }
      destruct (xhi (kn cs) (eadd (reg cs 11) (reg cs 12))) as [h1|] eqn:E1; [|unfold off_lazy in X; rewrite E1 in X; discriminate].
      destruct (xlo (kn cs) (reg cs 11)) as [lo1|] eqn:E2; [|unfold off_lazy in X; rewrite E1, E2 in X; discriminate].
      pose proof (off_lazy_sound_i E MR (kn cs) (reg cs 11) (reg cs 12) h1 lo1 HK X E1 E2) as Y.
      unfold eadd in Y. rewrite mkAlu_denot in Y. cbn [edenot] in Y. rewrite u_add64 in Y. fold s l in Y.
      rewrite Z.mod_small in Y by lia. lia. }
    (* [comment removed for export] *)
    assert (FD : fd_lookup (m_fds model) (Z_to_bv 64 fd') = Some (FdChannel (Z_to_bv 64 fd'))).
    { assert (F12 : fd' = 1 \/ fd' = 2) by (apply orb_prop in Hfd12 as [X|X]; apply Z.eqb_eq in X; auto).
      pose proof (co_fds _ _ _ _ _ _ _ _ _ _ _ HC) as CF. unfold fds_ok in CF.
      destruct (a_fd cs) as [|kk ll oo|]; [| destruct CF as (pp & cc & CF & _) |];
        rewrite CF; destruct F12 as [-> | ->]; reflexivity. }
    assert (NP : Z.of_nat (length pendb) <= nphi).
    { unfold esub in Hnphi2. rewrite mkAlu_denot in Hnphi2. cbn [edenot] in Hnphi2. rewrite u_sub64 in Hnphi2. fold wb wp in Hnphi2.
      rewrite Z.mod_small in Hnphi2 by lia. lia. }
    (* [comment removed for export] *)
    unfold APSC.cfg_fp, cfg_of. rewrite Hpc. unfold Wp. rewrite flat_map_app. change (flat_map (piece_den E) pend) with (pbytes E pend).
    change (flat_map (piece_den E) extra) with (pbytes E extra). rewrite Epend, Eextra.
    eapply (STDIO (lazyH model) R FULL model su f wb wp fd' s l (edenot E bufp) (edenot E bufsz) (edenot E canv) (Z_to_bv 64 ret)
              pendb extrab T).
    - exact (lazyH_off_segments_i E cs R FULL model HC).
    - apply lazy_all_hidden_lazyH.
    - eapply (off_lazy_avoids_i E cs R FULL model); [exact HC | lia | change (Z.of_nat 112) with 112; lia | right; lia].
    - eapply (off_lazy_avoids_i E cs R FULL model); [exact HC | lia | lia | lia].
    - destruct extrab as [|b0 eb0].
      + intros kk Hkk. cbn in Hkk. lia.
      + rewrite <- (Z_to_bv_bv_unsigned 64 s). eapply (off_lazy_avoids_i E cs R FULL model); [exact HC | lia | lia |].
        specialize (OFFs' ltac:(discriminate)). lia.
    - rewrite R2. symmetry. apply Z_to_bv_bv_unsigned.
    - exact R10.
    - rewrite R11. reflexivity.
    - rewrite R12. reflexivity.
    - exact R1.
    - lia.
    - lia.
    - apply (store_ok_Mr_FULL_i E cs model FULL). exact Wst.
    - lia.
    - lia.
    - rewrite Rwp. unfold wp. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - rewrite Rwb. unfold wb. rewrite Z_to_bv_bv_unsigned. reflexivity.
    - exact Rfd.
    - exact Rbufp.
    - exact Rbufsz.
    - rewrite Rcg, Hcgv. reflexivity.
    - exact Rcan.
    - apply orb_prop in Hfd12 as [X|X]; apply Z.eqb_eq in X; subst; lia.
    - exact FD.
    - exact (co_halt _ _ _ _ _ _ _ _ _ _ _ HC).
    - lia.
    - lia.
    - lia.
    - exact Lextra.
    - lia.
    - lia.
    - exact Dw.
    - exact Ds.
    - lia.
    - exact RpendF.
    - exact Rextra.
    - exact Hrok.
    - exact HT.
    - (* [comment removed for export] *)
      intros R' M' G10 G2 G1 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27 G3 G4 Pagree Pgrows Pwend Pwpos Pwbase.
      set (MR' := Mr A argH E cs model M').
      (* [comment removed for export] *)
      assert (NH : forall x : word,
                (su - 112 <= bv_unsigned x < su \/ f + 32 <= bv_unsigned x < f + 48 \/ f + 56 <= bv_unsigned x < f + 64) ->
                hid A argH E cs model x = false).
      { intros x [Hx|[Hx|Hx]].
        - apply (store_ok_not_hid_i E cs model FULL). fold MR.
          apply (store_ok_sub SEGS MR (Z_to_bv 64 (su - 112)) x 112 1); [rewrite u64_lit by lia; change (Z.of_nat 112) with 112; lia | exact Wst | |];
            rewrite u64_lit by lia; [lia | change (Z.of_nat 112) with 112; change (Z.of_nat 1) with 1; lia].
        - apply (hid_hull A HULL_ok argH argH_high). unfold in_hull. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia.
        - apply (hid_hull A HULL_ok argH argH_high). unfold in_hull. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
      destruct (after_call_cs_ok_i cs csa E R FULL model ret (Some (reg cs 12)) k4 R' M' HC Hac) as (HC' & Hag' & Hpc').
      + apply kept_regs. intros kk Hin. cbn [In] in Hin.
        clear - Hin G2 R2 G3 G4 G8 G9 G18 G19 G20 G21 G22 G23 G24 G25 G26 G27.
        destruct Hin as [<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[<-|[]]]]]]]]]]]]]]]];
          lazymatch goal with |- getr R' (Z_to_bv 5 (Z.of_nat ?kk)) = _ =>
            first [ replace (Z_to_bv 5 (Z.of_nat kk)) with (2%bv : bv 5) by (apply bv_eq; reflexivity); rewrite G2, R2; apply Z_to_bv_bv_unsigned
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (3%bv : bv 5) by (apply bv_eq; reflexivity); exact G3
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (4%bv : bv 5) by (apply bv_eq; reflexivity); exact G4
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (8%bv : bv 5) by (apply bv_eq; reflexivity); exact G8
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (9%bv : bv 5) by (apply bv_eq; reflexivity); exact G9
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (18%bv : bv 5) by (apply bv_eq; reflexivity); exact G18
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (19%bv : bv 5) by (apply bv_eq; reflexivity); exact G19
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (20%bv : bv 5) by (apply bv_eq; reflexivity); exact G20
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (21%bv : bv 5) by (apply bv_eq; reflexivity); exact G21
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (22%bv : bv 5) by (apply bv_eq; reflexivity); exact G22
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (23%bv : bv 5) by (apply bv_eq; reflexivity); exact G23
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (24%bv : bv 5) by (apply bv_eq; reflexivity); exact G24
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (25%bv : bv 5) by (apply bv_eq; reflexivity); exact G25
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (26%bv : bv 5) by (apply bv_eq; reflexivity); exact G26
                  | replace (Z_to_bv 5 (Z.of_nat kk)) with (27%bv : bv 5) by (apply bv_eq; reflexivity); exact G27 ]
          end.
      + cbv beta iota. replace (Z_to_bv 5 10) with (10%bv : bv 5) by (apply bv_eq; reflexivity). rewrite G10. reflexivity.
      + (* [comment removed for export] *)
        fold MR'.
        assert (HK0 : know_ok SEGS E MR k0) by (subst k0; apply kimg_cut_sound_i, kimg_cut_sound_i, HK).
        assert (HK3 : know_ok SEGS E MR' k3).
        { subst k3 k2 k1. apply (know_ok_havoc3_i E MR MR' k0); [exact HK0 | | ].
          - intros x N1 N2 N3. unfold MR', MR, Mr, mrestrict. destruct (hid A argH E cs model x); [reflexivity|]. apply Pagree.
            + rewrite Hq, elenZ_lit in N1 by lia. lia.
            + unfold estart in N2. cbn [a_base a_off] in N2. rewrite edenot_lit, u64_lit, elenZ_lit in N2 by lia. lia.
            + unfold estart in N3. cbn [a_base a_off] in N3. rewrite edenot_lit, u64_lit, elenZ_lit in N3 by lia. lia.
          - intros x Hx. unfold MR', MR, Mr, mrestrict in *. destruct (hid A argH E cs model x); [exact Hx | exact (Pgrows x Hx)]. }
        subst k4.
        assert (RD8 : forall off v, f + 32 <= off -> off + 8 <= f + 64 ->
                  rdn SEGS M' (Z_to_bv 64 off) 8 = Some (word_to_le_bytes 8 v) ->
                  rdn SEGS MR' (adenot E (SA (ELit 0) off)) 8 = Some (word_to_le_bytes 8 v)).
        { intros off v O1 O2 RD. rewrite adenot_abs0_i by lia. rewrite <- RD. apply rdn_ext; [rewrite u64_lit by lia; change (Z.of_nat 8) with 8; lia|].
          intros x Hx. rewrite u64_lit in Hx by lia. change (Z.of_nat 8) with 8 in Hx. unfold MR', Mr, mrestrict.
          rewrite (hid_hull A HULL_ok argH argH_high); [reflexivity|]. unfold in_hull. apply andb_true_intro; split; [apply Z.leb_le | apply Z.ltb_lt]; lia. }
        repeat apply Forall_cons; [ | | | exact HK3]; cbn [kentry_ok]; (split; [lia|]); (split; [apply FL; lia|]).
        * unfold eadd. rewrite mkAlu_denot, alu_add. apply RD8; [lia | lia | exact Pwend].
        * apply RD8; [lia | lia | exact Pwpos].
        * apply RD8; [lia | lia | exact Pwbase].
      + (* [comment removed for export] *)
        intros a Ha. apply Pagree; intros Hx; rewrite (NH a) in Ha by lia; discriminate.
      + specialize (Hk (ext_call E (nxt cs) R') R' M' model Hag' HC' eq_refl).
        unfold APSC.cfg_fp, cfg_of in Hk. rewrite Hpc' in Hk. exact Hk.
  Qed.
End NodesArg.
End WithFP1.

