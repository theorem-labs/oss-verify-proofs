(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* Modified by Theorem Labs, 2026-10: the generic part of proofs/cgif/cgif_file_fuzzer/lib/YC1i.v for libreac/fuzz_disco's program walk (ceil, alias_srlw_sll, req_size_pos', PTR, Bspan, region_kept_at1) over fuzz_disco's listing; cgif's create_byte_list_block walk is left out; module paths changed. *)
(* Modified by Theorem Labs, 2026-11: made from proofs/libreac/fuzz_disco/lib/A/Prog/YC1i.v, with its module paths and module names changed; 76 of its 111 lines of code are new or changed and 34 lines of the source are left out. *)
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require YZ00.
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YK11 YK0h YK0i YK14 YK1b YK1a YK15 YK18 YK0s.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YP0m YP0e YP09 YP02 YP0l YP0k YP06 YP03 YP04 YP0g YP01 YP0i YCbn.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaTable PaSym.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3v YI04 YI09 YI08 YI0s YI00 YI0m.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YG0v.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YK04 YA0i YA0n YA0o YCbm YA0q.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import
YG00 YG0a YG01 YG0f YG0n YG0d YCbq.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YN3u.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaRun PaShadow DiscoSyms DiscoList DiscoPa.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import PaJournal DiscoPaLib YC1g YC1h YC81 YC4b DiscoFrame YC88.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import DiscoBase.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Reusable Require Import YM05 YI16.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve ReacDiscoTableObserve_C.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require ReacDiscoTableObserve_M.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog Require Import ReacDiscoTableObserve_X.
From OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog Require disco_table_c reac_disco_table_observe_c reac_disco_table_observe.
Module DTC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.disco_table_c.
Module RDOC := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe_c.
Module RDO := OSSVerify.Proofs.libreac.fuzz_disco.lib.Prog.reac_disco_table_observe.
Module TM := OSSVerify.Proofs.libreac.fuzz_disco.lib.A.Prog.ReacDiscoTableObserve_M.
Import ListNotations.
Unset Lia Cache. Unset Nia Cache.
Local Set Warnings "-abstract-large-number".
#[local] Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
Open Scope bv_scope.
Open Scope Z_scope.
Section d. Context {fx : YK11.FPState} {rc : YM05.RunCeil}.
Context {SK : YI16.sink_head}.
Section f.
Context {PI : PAImg disco_listing}.
#[local] Notation SEGS := (@pa_segs _ disco_listing PI).
#[local] Notation VAL := (@pa_val _ disco_listing PI).
#[local] Notation SIGMA := (@pa_sigma _ disco_listing PI).
#[local] Notation BASE := (@pa_val _ disco_listing PI A_TEXT).
Section h.
Variable B : asyms.
Hypothesis LAWS : AR_laws SEGS B.
Hypothesis TL : PALib B.
Let RUN := paj_run B LAWS.
Let RET := paj_ret_at (PL := PL_disco) (PI := PI).
Ltac tobs_ext_eq R c regs1 Tc r j := rewrite R; exact (tobs_env_extra c regs1 Tc r j ltac:(lia)).
Lemma seg_ret : forall c, SegRet B c.
Proof.
intros c regs1 m1 md1 Tc so ret HP HM Hso H18 H10 Hmod.
pose proof (tm_J _ _ _ _ _ _ HM) as HJ.
assert (B8 : base_val (tobs_env c regs1 Tc 0) (Some 8%nat) = tt c).
{ cbn [base_val]. rewrite (tobs_env_reg c regs1 Tc 0 8 8%bv eq_refl), (tm_s0 _ _ _ _ _ _ HM).
  pose proof (tp_t0 _ _ HP). pose proof (tp_t63 _ _ HP). apply unsigned_lit_small. lia. }
pose proof (tobs_env_img c regs1 Tc 0) as HEI.
unfold cfgB.
destruct Hso as [-> | ->];
(lazymatch type of H18 with _ = w64 (ts c - ?sv) =>
  destruct (tobs_enter B c regs1 m1 md1 Tc 0x55f0 false 0 sv HP HM ltac:(first [left; reflexivity | right; reflexivity]) H18 ltac:(discriminate))
  as [HS SHOK] end;
paj_run_tok RUN HS HJ SHOK TBspan;
[ exact (tobs_awr B c _ false _ 0 HP B8 ltac:(discriminate))
| prreg HS (1%bv : bv 5) R1; prreg HS (2%bv : bv 5) R2; prreg HS (3%bv : bv 5) R3; prreg HS (4%bv : bv 5) R4;
  prreg HS (8%bv : bv 5) R8; prreg HS (9%bv : bv 5) R9; prreg HS (10%bv : bv 5) R10;
  prreg HS (18%bv : bv 5) R18; prreg HS (19%bv : bv 5) R19; prreg HS (20%bv : bv 5) R20; prreg HS (21%bv : bv 5) R21;
  prreg HS (22%bv : bv 5) R22; prreg HS (23%bv : bv 5) R23; prreg HS (24%bv : bv 5) R24; prreg HS (25%bv : bv 5) R25;
  prreg HS (26%bv : bv 5) R26; prreg HS (27%bv : bv 5) R27;
  pose proof (st_ok_pi_region_nth _ _ _ 1 _ HS eq_refl) as Hreg; cbn [ms_mem restrict] in Hreg;
  eapply (RET (tW c) _ _ _ _ _ HS eq_refl ltac:(vm_compute; reflexivity));
  let mat' := fresh "mat" in intros mat';
  assert (Ra : YK11.getr (ms_regs ms) 1 = YK11.getr (tregs c) 1) by (rewrite R1; exact (tobs_env_extra c regs1 Tc 0 0 ltac:(lia)));
  rewrite Ra, (tp_ra _ _ HP);
  assert (HM2 : tobs_m B c regs1 (ms_mem ms) (with_vm_backing (m_vm_lazy md1) mat md1) Tc);
  [ apply (tobs_exit_run B LAWS c regs1 m1 md1 Tc (tobs_env c regs1 Tc 0) false _ 0 regs1 (ms_mem ms) _ Tc HP HM B8
      ltac:(discriminate) HFr HG HJ (tm_Tl _ _ _ _ _ _ HM));
    [ intros; reflexivity
    | intros i Hi;
      rewrite (region_bytes (tobs_env c regs1 Tc 0) _ 8 384 400 384 400 _ (tt c) (DTC.sub Tc 384 16) Hreg B8
        ltac:(vm_compute; reflexivity)) by
        (first [ lia
               | apply Forall_cons; [|apply Forall_nil]; apply cagree_cdata; [lia|]; intros k Hk; rewrite tobs_env_ed; cbn [tobs_data];
                 rewrite nth_error_sub by lia; f_equal; lia ]);
      rewrite nth_error_sub by lia; f_equal; lia
    | discriminate
    | intros; reflexivity ]
  | eapply tobs_post_intro;
    [ exact HP
    | apply (ajournal_materialize SEGS B LAWS pa_segs_low); exact HJ
    | apply aregs_preserved_eqs;
      [ rewrite R2, (tobs_env_reg c regs1 Tc 0 2 2%bv eq_refl);
        change (bv_unsigned (YK11.getr regs1 2)) with (spZ regs1); rewrite (tm_sp _ _ _ _ _ _ HM);
        replace (spZ (tregs c) - 96 + 96) with (spZ (tregs c)) by lia; apply Z_to_bv_bv_unsigned
      | rewrite R3, (tobs_env_reg c regs1 Tc 0 3 3%bv eq_refl); exact (tm_gp _ _ _ _ _ _ HM)
      | rewrite R4, (tobs_env_reg c regs1 Tc 0 4 4%bv eq_refl); exact (tm_tp _ _ _ _ _ _ HM)
      | tobs_ext_eq R8 c regs1 Tc 0 1%nat | tobs_ext_eq R9 c regs1 Tc 0 2%nat
      | tobs_ext_eq R18 c regs1 Tc 0 3%nat | tobs_ext_eq R19 c regs1 Tc 0 4%nat | tobs_ext_eq R20 c regs1 Tc 0 5%nat
      | tobs_ext_eq R21 c regs1 Tc 0 6%nat | tobs_ext_eq R22 c regs1 Tc 0 7%nat | tobs_ext_eq R23 c regs1 Tc 0 8%nat
      | tobs_ext_eq R24 c regs1 Tc 0 9%nat | tobs_ext_eq R25 c regs1 Tc 0 10%nat | tobs_ext_eq R26 c regs1 Tc 0 11%nat
      | rewrite R27, (tobs_env_reg c regs1 Tc 0 27 27%bv eq_refl); exact (tm_s11 _ _ _ _ _ _ HM) ]
    | rewrite R10, (tobs_env_reg c regs1 Tc 0 10 10%bv eq_refl); exact H10
    | exact (tm_kept _ _ _ _ _ _ HM2)
    | exact (tm_T _ _ _ _ _ _ HM2)
    | exact (tm_Tl _ _ _ _ _ _ HM2)
    | exact (tm_G _ _ _ _ _ _ HM2)
    | exact Hmod ] ] ]).
Qed.
End h.
End f.
End d.
