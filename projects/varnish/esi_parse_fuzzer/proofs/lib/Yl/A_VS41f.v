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
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import PropExec ShapeAlg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Tac Bytes Arr RzBridge Image.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib Require Import V_Kit V_Stgw7.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require Import ImgA.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Strw Require Import CallLit CellsX.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Spec Require Import StrFun.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yc Require Import SpinAlg Hull.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Ym Require Import Asanljo.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_seql RA_sjs3.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf Require RA_vju4.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_seql OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_sjs3 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vrre OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.RA_vt1z OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yf.RA_vju4.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIface LayoutPA AClient ATac AIcpm9j AIcp0e6.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpghc AIcp7wm.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr Require AIcpkua AIcpya4 AIcp3q7 AIcpq85 AIcpnnp AIcptdg.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIface OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.LayoutPA OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AClient OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpm9j OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp0e6 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcpxbj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc.AIcp6d9 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpghc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp7wm OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua.AIcpilj OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpkua OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpya4 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcp3q7 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpq85 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcpnnp OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.AIcptdg.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_App A_Po6qc A_Potrl A_Vsb A_World A_Img A_ImgAny A_Cocsh A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Cocsh.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_Tac.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require A_vez59 A_VSe3i A_VSa8f.
Import OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_App OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Po6qc OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Potrl OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Vsb OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_World OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Img OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_ImgAny OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Cocsh.A_Henv OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_Tac.A_Frame OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_vez59 OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSe3i OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl.A_VSa8f.
Import ListNotations.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Import Dest4xs.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require AndN.   (* [comment removed for export] *)
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yl Require Import A_AI16.   (* [comment removed for export] *)
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.DL.projn := Ltac2.Init.true.   (* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaTwx2.zify_noeuclid ::= intros; Zify.zify_pre_hook; Zify.zify_elim_let; Zify.zify_op; (Zify.zify_iter_specs); Zify.zify_post_hook.
(* [comment removed for export] *)

Local Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.transport_chunks segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_chunks segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.footprint_after_store segs m a bs ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_footprint_after_store segs m a bs.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_mem_after_store.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.transport_after_call segs m m' MU WM ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_transport_after_call segs m m' MU WM.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.addr_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_addr_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_zmlia.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.RL.sec := Ltac2.Init.true.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require StepFast.
#[local] Ltac2 Set OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sfx_on := Ltac2.Init.true.   (* [comment removed for export] *)
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.step_core segs R F pc fc rv m ro ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_step_core segs R F pc fc rv m ro.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.zstep ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.StepFast.sf_zstep.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require LiaSec.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.LiaSec.lia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietLia2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Destzna.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_exs PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_exs PO.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Tac.destruct_ands PO ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Destzna.dk_ands PO.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require WeqGuard TacDiet2.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.ZBridge.word_eq_tac ::= first [ exact eq_refl | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.WeqGuard.weq_guard; OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.TacDiet2.diet_word_eq_tac ].
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Stor0fe.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Step.mem_after_store ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Stor0fe.sb_mem_after_store.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require Diet8ul.
Local Ltac lia ::= OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.Diet8ul.dlia_sec.
(* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib Require MliaFast DietDL3.
Local Ltac OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Yr.ATac.mlia ::= first [ OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.MliaFast.mlia_fast | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietDL3.dl_solve0 | OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.DietLia2.diet_mlia ].
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Tactic Notation "keeplia" ne_hyp_list(hs) := first [ solve [ try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ] | keep_bundles; try (generalize alloc_ceiling_val); clear - hs; intros; try pose proof alloc_ceiling_val as ACV__; unhide_all; unhide_app; lia ].

Definition VSB_vprintf_entry : Z := 0x8a54c.
Definition VSB_printf_entry : Z := 0x8aa50.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Section CEIL.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Lemma got_ssp_cell : forall v, consts_hold LPA v -> ro_cells rsegs v GOT_SSP [C8 (Z_to_bv 64 SSP_GUARD)].
Proof. intros v CH. apply ro_C8_of_bytes. apply (consts_lookup v _ _ CH). vm_compute. reflexivity. Qed.

Lemma guard_any : forall M : mem, exists g, ro_cells rsegs M SSP_GUARD [C8 g].
Proof.
  intros M. destruct (rw_C8_any M SSP_GUARD ltac:(unfold SSP_GUARD; lia) ltac:(unfold SSP_GUARD; lia)
                        ltac:(vm_compute; reflexivity) ltac:(vm_compute; reflexivity)) as [g [R _]].
  exists g. exact R.
Qed.

Lemma ssp_any : forall v, consts_hold LPA v -> exists canary, ssp_cells v canary.
Proof. intros v CH. destruct (guard_any v) as [g G]. exists g. split; [exact (got_ssp_cell v CH)| exact G]. Qed.

End CEIL.

(* [comment removed for export] *)
Section Cells.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Variable v : mem.
  Hypothesis CH : consts_hold LPA v.
  Local Ltac cl := apply (consts_lookup v _ _ CH); vm_compute; reflexivity.

  #[using="CH"] Lemma strnlen_icpt_cells_of_consts : strnlen_icpt_cells v.
  Proof.
    split; [apply asan_inited_cell_of_bytes; cl|].
    split; [apply ro_C8_of_bytes; cl|].
    split; [apply ro_C8_of_bytes; cl|].
    split. { eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 251); [cl| reflexivity]. }
    split; [apply ro_C8_of_bytes; cl|].
    exact (map_cells_of_consts v CH).
  Qed.

  #[using="CH"] Lemma vficpt_cells_of_consts : vficpt_cells v.
  Proof.
    unfold vficpt_cells. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    first [ apply asan_inited_cell_of_bytes; cl
          | apply ro_C8_of_bytes; cl
          | apply ro_C4_of_bytes; cl
          | (eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 84); [cl| reflexivity])
          | exact (map_cells_of_consts v CH)
          | exact (asan_memset_cells_of_consts v CH)
          | exact (asan_memcpy_cells_of_consts v CH) ].
  Qed.

  (* [comment removed for export] *)
  #[using="CH"] Lemma vsnicpt_cells_of_consts : bytes_at rsegs v 0xaaf30 (le8 (Z_to_bv 64 0xa1b2c)) -> vsnicpt_cells v.
  Proof.
    intros R. unfold vsnicpt_cells. OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.and_splits;
    first [ apply asan_inited_cell_of_bytes; cl
          | (apply ro_C8_of_bytes; exact R)
          | apply ro_C8_of_bytes; cl
          | (eapply (ro_C1_of_nth v 0x146ee8 pa_common_flags_bytes 84); [cl| reflexivity]) ].
  Qed.
End Cells.

(* [comment removed for export] *)
Section CEIL2.
Context {Clg : Ceiling}.  (* [comment removed for export] *)

Definition vsnreal_ok : Prop := forall v, consts_hold LPA v -> bytes_at rsegs v 0xaaf30 (le8 (Z_to_bv 64 0xa1b2c)).

(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sfi_intro : forall v A la D n HS hs SB K zlo zhi,
  consts_hold LPA v -> vsnreal_ok ->
  range_ok v A la -> range_ok v D (Z.of_nat n) -> hs_shadow v HS hs ->
  bytes_at rsegs v SB (zeros K) -> zsh_bounds SB K zlo zhi -> (2147446784 <= SB)%Z (* [comment removed for export] *) ->
  sfi A la D n HS hs SB K zlo zhi v.
Proof.
  intros v A la D n HS hs SB K zlo zhi CH VR RA RD HSS ZB ZBD SBL.
  split; [| exact (vsnicpt_cells_of_consts v CH (VR v CH))].
  split; [| split; [exact (asan_memset_cells_of_consts v CH)| exact (vficpt_cells_of_consts v CH)]].
  split; [exact (asan_memcpy_cells_of_consts v CH)|]. split; [exact (strnlen_icpt_cells_of_consts v CH)|].
  split; [exact RA|]. split; [exact RD|]. split; [exact HSS|]. split; [exact ZB|]. split; [exact ZBD| exact SBL].
Qed.

End CEIL2.

(* [comment removed for export] *)
Section SS.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  Lemma zsh_of_stack_shadow : forall (v : mem) SB N lo hi lo' hi',
    stack_shadow LPA v SB N lo hi -> 0 <= lo -> lo + 64 <= lo' -> lo' <= hi' -> hi' + 64 <= hi -> hi' + 16 <= 2^47 -> kHighMemBeg <= lo' ->
    bytes_at rsegs v SB (zeros (Z.to_nat N)) /\ zsh_bounds SB (Z.to_nat N) lo' hi'.
  Proof.
    (intros v SB N lo hi lo' hi'; (first [ intro dR_11; dand6 dR_11 as B N0 Lq Hh SLO T | intros (B & N0 & Lq & Hh & SLO & T) ]); intros L0 H1 H2 H3 H4 H5).
    split; [exact B|]. unfold zsh_bounds, sha, shadow_off, kHighShadowEnd_z, kHighMemBeg_z. unfold sh, kShadowOffset, kHighMemBeg in *. all_app_facts.
    rewrite Z2Nat.id by lia.
    assert (lo / 8 + 8 <= lo' / 8) by (Z.div_mod_to_equations; lia).
    assert (hi' / 8 + 8 <= hi / 8) by (Z.div_mod_to_equations; lia).
    OSSVerify.Proofs.varnish.esi_parse_fuzzer.lib.Lib.AndN.rsplit; lia.
  Qed.
  Lemma stack_shadow_again : forall (v v' : mem) SB N lo hi K,
    stack_shadow LPA v SB N lo hi -> bytes_at rsegs v' SB (zeros K) -> K = Z.to_nat N -> stack_shadow LPA v' SB N lo hi.
  Proof. intros v v' SB N lo hi K (B & R) ZB ->. split; [exact ZB| exact R]. Qed.
End SS.

(* [comment removed for export] *)
Lemma freespace_wrap : forall s l, 0 <= l < s -> s < 2^64 ->
  (s + (18446744073709551615 - l)) mod 18446744073709551616 = s - l - 1.
Proof.
  intros s l H1 H2. replace (s + (18446744073709551615 - l)) with ((s - l - 1) + 1 * 18446744073709551616) by lia.
  rewrite Z_mod_plus_full. apply Z.mod_small. lia.
Qed.
Lemma lxor_ones64 : forall x, 0 <= x < 2^64 -> Z.lxor x 18446744073709551615 = 18446744073709551615 - x.
Proof. intros. apply zb_lxor_ones. lia. Qed.

(* [comment removed for export] *)
Section S.
Context {Clg : Ceiling}.  (* [comment removed for export] *)
  Context {AI : AsanAlloc LPA}.
  Context {AI16 : AsanAlloc16}.   (* [comment removed for export] *)
  (* [comment removed for export] *)
  Variables (FMT : list cell) (la nargs : Z) (PRE : list word -> Z -> list byte -> Prop) (OUT : list word -> list byte -> list byte).
  Hypothesis HLA : Z.of_nat (cells_size FMT) = la.
  Hypothesis HOUT : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) < 2^31)%Z.
  Hypothesis HOUT1 : forall slots HS hs, PRE slots HS hs -> (Z.of_nat (length (OUT slots hs)) + 1 < 2^31)%Z.
  Hypothesis P1 : pass1_stmt FMT la.
  Hypothesis P2 : pass2_stmt FMT la nargs PRE OUT.
  Variables (fbytes : list byte) (SLOTS : list word -> Prop).
  Hypothesis PCM : AIcptdg.pcm_stmt fbytes SLOTS.
  Hypothesis FBY : cells_bytes FMT = fbytes ++ [Z_to_bv 8 0].
  Hypothesis VSNREAL : vsnreal_ok.

  (* [comment removed for export] *)
  Definition str_home (A : AS) (S : Z) (v : vsb_rec) (HS : Z) (hs : list byte) : Prop :=
    (hs = [] /\ (HS = 0 \/ 0x10000 <= HS < 0x60a000) (* [comment removed for export] *)) \/ exists q k, a_live A q = Some k /\ q <= HS /\ HS + Z.of_nat (length hs) <= q + k /\ q <> S /\ q <> vb_buf v
                       /\ In (Z_to_bv 8 0) hs.

  (* [comment removed for export] *)
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
            (m0 : mem) (md0 : Model) (A0 : AS) (S : Z) (vr : vsb_rec)
            (Afmt VA : Z) (slots : list word) (HS : Z) (hs : list byte) (lo SB N : Z) (T : TSet).
  Hypothesis AINV00 : ainv A0 m0 md0.
  Hypothesis SOBJ : vsb_obj LPA A0 (aview A0 m0) S vr false.
  (* [comment removed for export] *)
  Hypothesis HF : forall m, mem_inv rsegs m -> ro_cells rsegs m Afmt FMT.   (* [comment removed for export] *)
  Hypothesis ARL : IMG_LO <= Afmt.
  Hypothesis ART : Afmt + la <= RO_TOP.
  Hypothesis AFR : forall v, cenv v -> range_ok v Afmt la.          (* [comment removed for export] *)
  (* [comment removed for export] *)
  Hypothesis VAA : va_area (aview A0 m0) VA slots.
  Hypothesis VLO : bv_unsigned sp <= VA.
  Hypothesis VHI : VA + 8 * Z.of_nat (length slots) <= 2^47.
  (* [comment removed for export] *)
  Hypothesis HPRE : PRE slots HS hs.
  Hypothesis HSL : SLOTS slots.
  Hypothesis HSB : bytes_at rsegs (aview A0 m0) HS hs.
  Hypothesis HSH : str_home A0 S vr HS hs.
  Hypothesis EM : vb_size vr + Z.of_nat (length (OUT slots hs)) + 1 <= EXT_MAX.
  Hypothesis LBM : a_livebytes A0 + vsb_extendsize (vb_size vr + Z.of_nat (length (OUT slots hs)) + 1) <= LIVE_MAX.
  Hypothesis NLV : a_nlive A0 + 1 <= NLIVE_MAX.
  Hypothesis SCM : 1 <= a_seccred A0.
  Hypothesis PRM : PRIM_ROOM <= a_primcred A0.   (* [comment removed for export] *)
  Hypothesis FY : frames_young A0 0 1.
  Hypothesis TP : tp = cl_tp LPA.
  Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
  Hypothesis CEIL : alloc_ceiling <= lo.
  Hypothesis LO : lo + VPRINTF_STACK <= bv_unsigned sp.
  Hypothesis SPHI : bv_unsigned sp + 64 <= 2^47.
  Hypothesis STKSH : stack_shadow LPA (aview A0 m0) SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64).
  Hypothesis K : forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (r : Z) (A' : AS) (m' : mem) (md' : Model)
                        (vr' : vsb_rec),
      let v' := aview A' m' in
      ainv A' m' md' -> mem_inv rsegs v' -> amd_frame md0 md' ->
      vsb_obj LPA A' v' S vr' false ->
      (vb_error vr <> 0 -> r = -1 /\ vr' = vr) ->
      (vb_error vr = 0 -> r = 0 /\ vb_error vr' = 0 /\
         (  vb_len vr' = vb_len vr + Z.of_nat (length (OUT slots hs))
         \/ (vb_len vr' = vb_size vr - 1 /\ vb_size vr' = vb_size vr /\ vb_buf vr' = vb_buf vr))) ->
      vb_len vr <= vb_len vr' <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
      vb_size vr <= vb_size vr' <= Z.max (vb_size vr) (vb_len vr' + 4096) ->
      (forall q, q <> vb_buf vr -> q <> vb_buf vr' -> a_live A' q = a_live A0 q) ->
      (vb_buf vr' = vb_buf vr \/ (a_live A0 (vb_buf vr') = None /\ a_live A' (vb_buf vr) = None)) ->
      frames_aged A0 A' 0 1 ->
      a_livebytes A' = a_livebytes A0 + vb_size vr' - vb_size vr ->
      a_tinycred A' = a_tinycred A0 -> a_nlive A' = a_nlive A0 ->
      a_seccred A0 - (vsb_pot vr' - vsb_pot vr) <= a_seccred A' <= a_seccred A0 ->
      a_primcred A0 - (vsb_ppot vr' - vsb_ppot vr) <= a_primcred A' <= a_primcred A0 ->   (* [comment removed for export] *)
      stk rsegs v' lo (bv_unsigned sp) ->
      va_area v' VA slots -> bytes_at rsegs v' HS hs ->
      stack_shadow LPA v' SB N (bv_unsigned sp - VPRINTF_STACK - 64) (bv_unsigned sp + 64) ->
      cframe LPA (owned A0) (owned A') (bv_unsigned sp) VPRINTF_STACK
               (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
               (newblk (vb_buf vr') (vb_size vr')) (aview A0 m0) v' ->
      srealizes rsegs (mkCfg (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                                      s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                                 F (ret_pc ra) fc None m' (seg_rom rsegs)) md') T.

  Local Ltac touch_all :=
    pose proof (conj HLA (conj HOUT (conj HOUT1 (conj P1 (conj P2 (conj PCM (conj FBY (conj VSNREAL
      (conj AINV00 (conj SOBJ (conj HF (conj ARL (conj ART (conj AFR (conj VAA (conj VLO (conj VHI (conj HPRE (conj HSL (conj HSB (conj HSH
      (conj EM (conj LBM (conj NLV (conj SCM (conj PRM (conj FY (conj TP (conj SP16 (conj CEIL (conj LO (conj SPHI (conj STKSH K))))))))))))))))))))))))))))))))
     ) as ALL_HYPS; clear ALL_HYPS.

  Local Ltac prelims :=
    pose proof alloc_ceiling_num as ACV;
    pose proof (zr_word sp) as SPR; unfold inr64 in SPR;
    unfold_stacks; unfold kHighMemBeg in *; all_app_facts.

  Local Ltac ufs := unfold_stacks.

  (* [comment removed for export] *)
  Definition fr_alloc1 (A A1 : AS) (ff : Z) : Prop :=
       a_frame A ff = None /\ a_frame A1 ff = Some (1, 0%nat)
    /\ (forall g k' age', g <> ff -> a_frame A g = Some (k', age') -> a_frame A1 g = Some (k', if Z.eqb k' 1 then Datatypes.S age' else age'))
    /\ (forall g, g <> ff -> a_frame A g = None -> a_frame A1 g = None)
    /\ (forall q0, a_live A1 q0 = a_live A q0) /\ a_livebytes A1 = a_livebytes A /\ a_tinycred A1 = a_tinycred A /\ a_nlive A1 = a_nlive A
    /\ a_seccred A1 = a_seccred A
    /\ a_primcred A1 = a_primcred A   (* [comment removed for export] *)
    /\ ff mod 32 = 0 /\ app_range LPA ff 128 (* [comment removed for export] *) /\ ff + 128 <= alloc_ceiling /\ 0 <= sh ff /\ sh ff + 16 <= SHMAX.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  #[using="K STKSH SPHI LO CEIL SP16 TP FY SCM PRM NLV LBM EM HSH HSB HSL HPRE VHI VLO VAA AFR ART ARL HF SOBJ AINV00 Afmt VSNREAL FBY PCM SLOTS fbytes P2 P1 HOUT1 HOUT HLA PRE nargs la FMT"] Lemma vp_exit : forall (xra t0 t1 t2 a0 a1 a3 a4 a5 a6 a7 t3 t4 t5 t6 xs5 xs7 xs8 xs9 xs10 xs11 : word) (d ff r : Z) (A1 A2 : AS) (m2 : mem) (md2 : Model)
                       (vr2 : vsb_rec) (j88 fj shj : list byte),
    0 <= d <= 16 ->
    ainv A2 m2 md2 -> mem_inv rsegs (aview A2 m2) -> amd_frame md0 md2 ->
    stk rsegs (aview A2 m2) lo (bv_unsigned sp + -192 - d) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -192 - d) [CB 88 j88] ->
    stk rsegs (aview A2 m2) (bv_unsigned sp + -192 - d + 88) (bv_unsigned sp + -104) ->
    rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -104)
             [C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    fr_alloc1 A0 A1 ff -> frames_same A1 A2 ->
    length fj = 120%nat -> rw_cells rsegs (aview A2 m2) ff [CB 120 fj] ->
    length shj = 16%nat -> rw_cells rsegs (aview A2 m2) (sh ff) [CB 16 shj] ->
    vsb_obj LPA A2 (aview A2 m2) S vr2 false ->
    (vb_error vr <> 0 -> r = -1 /\ vr2 = vr) ->
    (vb_error vr = 0 -> r = 0 /\ vb_error vr2 = 0 /\
       (vb_len vr2 = vb_len vr + Z.of_nat (length (OUT slots hs)) \/ (vb_len vr2 = vb_size vr - 1 /\ vb_size vr2 = vb_size vr /\ vb_buf vr2 = vb_buf vr))) ->
    vb_len vr <= vb_len vr2 <= vb_len vr + Z.of_nat (length (OUT slots hs)) ->
    vb_size vr <= vb_size vr2 <= Z.max (vb_size vr) (vb_len vr2 + 4096) ->
    (vb_buf vr2 = vb_buf vr \/ (a_live A1 (vb_buf vr2) = None /\ a_live A2 (vb_buf vr) = None)) ->
    (forall p, p <> vb_buf vr -> p <> vb_buf vr2 -> a_live A2 p = a_live A1 p) ->
    a_livebytes A2 = a_livebytes A1 + vb_size vr2 - vb_size vr ->
    a_tinycred A2 = a_tinycred A1 -> a_nlive A2 = a_nlive A1 ->
    a_seccred A1 - (vsb_pot vr2 - vsb_pot vr) <= a_seccred A2 <= a_seccred A1 ->
    a_primcred A1 - (vsb_ppot vr2 - vsb_ppot vr) <= a_primcred A2 <= a_primcred A1 ->   (* [comment removed for export] *)
    va_area (aview A2 m2) VA slots -> bytes_at rsegs (aview A2 m2) HS hs ->
    stack_shadow LPA (aview A2 m2) SB N (bv_unsigned sp - (192 + 16 + (80 + ASTK)) - 64) (bv_unsigned sp + 64) ->
    cframe LPA (owned A0) (owned A2) (bv_unsigned sp) VPRINTF_STACK
           (fun a => newblk (vb_buf vr) (vb_size vr) a \/ (S <= a < S + 40))
           (fun a => frm ff 1 a \/ newblk (vb_buf vr2) (vb_size vr2) a) (aview A0 m0) (aview A2 m2) ->
    srealizes rsegs (mkCfg (MS (mkR xra (Z_to_bv 64 (bv_unsigned sp + -192 - d)) gp tp t0 t1 t2 sp (Z_to_bv 64 (bv_unsigned sp + -192 - d))
                                    a0 a1 (Z_to_bv 64 r) a3 a4 a5 a6 a7 (Z_to_bv 64 ff) (Z_to_bv 64 ff) (Z_to_bv 64 S) xs5 (Z_to_bv 64 (sh ff)) xs7
                                    xs8 xs9 xs10 xs11 t3 t4 t5 t6)
                               F (Z_to_bv 64 0x8a848) fc None m2 (seg_rom rsegs)) md2) T.
  Proof.
    touch_all. intros until shj. intros D0 AINV MI MDF STlo SCR STpad FRH FA FS12 LFJ FFC LSH SHC SOBJ2 KE KO LEN2 SZ2 REL2 LIVEq2 LB2 TC2 NL2 SC2 PR2 VAA2 HSB2 STKSH2 CF02.
    prelims.
    (first [ dand15 FA as FN FF1 AGE NONE LV1 LB1 TC1 NL1 SC1 PR1 FAL FLO FHI SH0 SH1 | destruct FA as (FN & FF1 & AGE & NONE & LV1 & LB1 & TC1 & NL1 & SC1 & PR1 & FAL & FLO & FHI & SH0 & SH1) ]). rewrite SHMAX_val in SH1. all_app_facts.
    pose proof (as_minv LPA A2 _ _ AINV) as [_ MH].
    assert (FF2 : a_frame A2 ff = Some (1, 0%nat)) by (rewrite (FS12 ff); exact FF1).
    (* [comment removed for export] *)
    release_frame SCR STlo (bv_unsigned sp + -192 - d + 88).
    pose proof (stk_merge rsegs _ _ _ _ STlo STpad ltac:(keeplia D0 LO CEIL ACV)) as STm. clear STlo STpad.
    destruct (stk_carve rsegs _ lo _ 88 STm ltac:(keeplia D0 LO CEIL ACV)) as [STlo [j88' FRL]]. clear STm.
    change (Z.of_nat 88) with 88 in STlo, FRL. replace (bv_unsigned sp + -104 - 88) with (bv_unsigned sp + -192) in STlo, FRL by lia.
    assert (FR : rw_cells rsegs (aview A2 m2) (bv_unsigned sp + -192)
                   [CB 88 j88'; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra]).
    { apply (proj2 (rw_cells_app rsegs _ _ [CB 88 j88'] _)). split; [exact FRL|]. cbn [cells_size csize Nat.add].
      eapply rwc_eq; [exact FRH| lia]. }
    clear FRL FRH.
    destruct (stk_split rsegs _ lo (bv_unsigned sp + -192 - d) _ STlo ltac:(keeplia D0 LO CEIL ACV)) as [STlo' STpad]. clear STlo. rename STlo' into STlo.
    (* [comment removed for export] *)
    (first [ pose proof ((fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_2; dex2 dR_2 as fa fb; dand6 dR_2 as FAW FB FRO FRW FOW FNI | pose proof ((fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_2; dand8 dR_2 as fa fb FAW FB FRO FRW FOW FNI | destruct (fframe_flag A2 m2 md2 ff 1 0%nat AINV FF2) as (fa & fb & FAW & FB & FRO & FRW & FOW & FNI) ]).
    change (fsize 1) with 128 in FRO. replace (ff + 128 - 8) with (ff + 120) in FRO by lia.
    (* [comment removed for export] *)
    (first [ pose proof ((vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2)) as dR_3; dand11 dR_3 as S16 Slo Shi Simg B16 Blo Bhi Bimg DSB Smap Bmap | pose proof (vsb_obj_geom LPA A2 m2 md2 S vr2 false AINV SOBJ2) as (S16 & Slo & Shi & Simg & B16 & Blo & Bhi & Bimg & DSB & Smap & Bmap) ]).
    (first [ pose proof (SOBJ2) as dR_4; dand6 dR_4 as _ VINV2 VLS VLB VNE _ | pose proof SOBJ2 as (_ & VINV2 & VLS & VLB & VNE & _) ]).
    unfold kHighMemBeg in Slo, Blo. all_app_facts.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLS) as DJfS.
    pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 VLB) as DJfB.
    change (fsize 1) with 128 in DJfS, DJfB.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLS FOW) as OWS.
    pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV VLB FOW) as OWB.
    pose proof (owned_outside_fframe A2 m2 md2 ff 1 0%nat _ AINV FF2 FOW) as [OWF OWSH].
    change (fsize 1) with 128 in OWF, OWSH. change (128 / 8) with 16 in OWSH.
    (* [comment removed for export] *)
    pose proof (bytes_at_bound _ _ _ _ VAA2) as VAB. rewrite u64s_length in VAB.
    hide DJfS. hide DJfB. hide OWS. hide OWB. hide DSB. hide HSB2. hide_neqs.
    (* [comment removed for export] *)
    pose proof (munch_refl [(sh ff, sh ff + 16); (ff, ff + 8); (fa, fa + 1)] (aview A2 m2)) as MU.
    pose proof (wmono_refl rsegs (aview A2 m2)) as WM.
    assert (CFR : client_fp_rel LPA A2 [ff] (aview A2 m2) [(sh ff, sh ff + 16); (ff, ff + 8); (fa, fa + 1)]).
    { unfold client_fp_rel. split; [| split; [| split; [| exact I]]].
      - right; right; right; left. exists ff, 1, 0%nat. split; [exact FF2|]. change (fsize 1 / 8) with 16. lia.
      - right; right; left. exists ff, 1, 0%nat. split; [exact FF2|]. change (fsize 1) with 128. lia.
      - right; right; right; right. exists ff, 1, 0%nat, (Z_to_bv 64 fa). split; [left; reflexivity|]. split; [exact FF2|].
        split; [exact FB|]. rewrite unsigned_lit by (keeplia FAW ACV); split; reflexivity. }
    hide FB.
    ago AINV. fold_cl_segs.
    (* [comment removed for export] *)
    zstep. fix_neg. sb1.
    (* [comment removed for export] *)
    zstep. zstep. zstep. zstep. kdead.
    (* [comment removed for export] *)
    zstep. fix_neg. do 16 sb1.
    (* [comment removed for export] *)
    zstep. unhide OWS. unhide OWB. try clear FRO. sb1. hide OWS. hide OWB. zstep.
    (* [comment removed for export] *)
    zstep. zstep.
    do 13 zstep. zstep.
    try replace (bv_unsigned sp + -192 + 192) with (bv_unsigned sp) by lia.
    try rewrite (Z_to_bv_bv_unsigned sp).
    zstep.
    (* [comment removed for export] *)
    lazymatch goal with ST1 : stk _ ?mq lo _, ST2 : stk _ ?mq (bv_unsigned sp + -192 - d) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (stk_merge rsegs mq _ _ _ ST1 ST2 ltac:(keeplia D0 LO CEIL ACV)) as STm; clear ST1 ST2 end.
    lazymatch goal with FRq : rw_cells _ ?mq (bv_unsigned sp + -192) _ |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      release_frame FRq STm (bv_unsigned sp) end.
    (* [comment removed for export] *)
    lazymatch goal with FLq : rw_cells _ ?mq fa [C1 ?b] |- evt _ _ (MS _ _ _ _ _ ?mq _) =>
      pose proof (flag_cleared (Clg:=Clg) mq fa FLq FNI ltac:(keeplia FAW ACV)) as FL end.
    unhide FB. astop_rel1 AINV FF2 FB MU WM CFR FL.
    (first [ pose proof ((as_release_spec LPA A2 m2 md2 ff 1 0%nat AINV FF2)) as dR_5; dand11 dR_5 as RN RO RL RLB RTC RSC RPC RNL RH RE ROW | destruct (as_release_spec LPA A2 m2 md2 ff 1 0%nat AINV FF2) as (RN & RO & RL & RLB & RTC & RSC & RPC & RNL & RH & RE & ROW) ]).
    lazymatch goal with |- srealizes _ (mkCfg (MS _ _ _ _ _ ?m1 _) ?md1) _ =>
    eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ r (a_release A2 ff) m1 md1 vr2);
      [ assumption | assumption
      | eapply amd_frame_trans; [exact MDF| apply amd_frame_sbm; [exact SBM| exact MH]]
      | (* [comment removed for export] *)
        unhide DJfS; unhide DJfB; unhide OWS; unhide OWB;
        (first [ pose proof (SOBJ2) as dR_6; dand6 dR_6 as XC XI XLS XLB XNE XB | pose proof SOBJ2 as (XC & XI & XLS & XLB & XNE & XB) ]); split; [| split; [exact XI| split; [rewrite RL; exact XLS| split; [rewrite RL; exact XLB| split; [exact XNE|]]]]];
        [ eapply (rw_cells_munch LPA); [exact XC| exact MU| exact WM|]; rewrite vsb_cells_size; change (Z.of_nat 40) with 40;
          intros a Ha; cbn; keeplia Ha DJfS OWS SH1 Slo
        | (first [ dex1 XB as bs; dand3 XB as [UB UW] LENx NULx | dand4 XB as bs [UB UW] LENx NULx | destruct XB as (bs & [UB UW] & LENx & NULx) ]); exists bs; split; [| split; [exact LENx| exact NULx]]; split;
          [ eapply (bytes_at_munch LPA); [exact UB| exact MU| rewrite LENx; intros a Ha; cbn; keeplia Ha DJfB OWB SH1 Blo]
          | eapply wr_at_transport; [exact UW| exact WM] ] ]
      | exact KE | exact KO | exact LEN2 | exact SZ2
      | intros p Hp1 Hp2; rewrite RL, (LIVEq2 p Hp1 Hp2); apply LV1
      | destruct REL2 as [E|[E1 E2]]; [left; exact E| right; split; [rewrite <- (LV1 (vb_buf vr2)); exact E1| rewrite RL; exact E2]]
      | eapply (frames_aged_alloc_release A0 A1 A2 m2 md2 ff 1); [right; reflexivity| exact FN| exact FF1| exact AGE| exact NONE| exact FS12| exact AINV| exists 0%nat; exact FF2]
      | rewrite RLB, LB2, LB1; reflexivity
      | rewrite RTC, TC2, TC1; reflexivity
      | rewrite RNL, NL2, NL1; reflexivity
      | rewrite RSC; try (generalize alloc_ceiling_val); clear - SC2 SC1; try pose proof alloc_ceiling_val as ACV__; lia
      | rewrite RPC; clear - PR2 PR1; lia (* [comment removed for export] *)
      | assumption
      | | | | ]
    end.
    - (* [comment removed for export] *)
      unfold va_area in *. eapply (bytes_at_munch LPA); [exact VAA2| exact MU|]. rewrite u64s_length. intros a Ha. cbn. keeplia Ha VAB VLO SH1 FHI FAW LO CEIL ACV SPR.
    - (* [comment removed for export] *)
      unhide HSB2. pose proof HSH as [[E EHS]|(hq & hk & LQ & Q1 & Q2 & NQS & NQB & HNUL)].
      + rewrite E. apply bytes_at_nil. pose proof (bytes_at_bound _ _ _ _ HSB2) as Bq. keeplia Bq.
      + assert (LQ2 : a_live A2 hq = Some hk).
        { rewrite (LIVEq2 hq NQB); [rewrite (LV1 hq); exact LQ|].
          intros Ehq. destruct REL2 as [Eb|[Eb _]]; [exact (NQB (eq_trans Ehq Eb))|]. rewrite <- Ehq, (LV1 hq), LQ in Eb. discriminate Eb. }
        pose proof (as_frame_blk_disjoint LPA A2 m2 md2 ff 1 0%nat _ _ AINV FF2 LQ2) as DJfQ. change (fsize 1) with 128 in DJfQ.
        pose proof (owned_outside_live A2 m2 md2 _ _ _ AINV LQ2 FOW) as OWQ.
        (first [ pose proof ((live_geomP LPA A2 m2 md2 hq _ AINV LQ2)) as dR_8; dand4 dR_8 as _ _ Qlo _ | pose proof (live_geomP LPA A2 m2 md2 hq _ AINV LQ2) as (_ & _ & Qlo & _) ]). unfold kHighMemBeg in Qlo. all_app_facts.
        eapply (bytes_at_munch LPA); [exact HSB2| exact MU|]. intros a Ha. cbn. keeplia Ha Q1 Q2 DJfQ OWQ SH1 Qlo.
    - (* [comment removed for export] *)
      assert (M0 : 0 <= bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) by keeplia CEIL LO ACV.
      assert (M1 : bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64 <= Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling) by (clear; lia).
      assert (M2 : Z.max (bv_unsigned sp - (192 + 16 + (80 + 8192)) - 64) alloc_ceiling <= bv_unsigned sp + 64) by keeplia CEIL LO ACV.
      pose proof (stack_shadow_sub LPA _ SB N _ _ _ _ STKSH2 M1 (Z.le_refl _) M0) as SSx.
      (first [ pose proof ((crange_stack_shadow (Clg:=Clg) LPA A2 m2 md2 SB N _ _ AINV SSx ltac:(clear; lia))) as dR_9; dand3 dR_9 as _ _ CRS | pose proof (crange_stack_shadow (Clg:=Clg) LPA A2 m2 md2 SB N _ _ AINV SSx ltac:(clear; lia)) as (_ & _ & CRS) ]). clear SSx M0 M1 M2.
      (first [ pose proof (STKSH2) as dR_10; dand6 dR_10 as SSB SSN _ _ SSC SST | pose proof STKSH2 as (SSB & SSN & _ & _ & SSC & SST) ]).
      pose proof sh_ceiling_ge as SHC8 (* [comment removed for export] *).
      eapply stack_shadow_again; [exact STKSH2| | reflexivity].
      eapply (bytes_at_munch LPA); [exact SSB| exact MU|]. rewrite zeros_length, Z2Nat.id by exact SSN.
      intros a Ha. cbn.
      assert (NOa : ~ owned A2 a). { destruct (CRS (a - SB) ltac:(keeplia Ha)) as [X _]. replace (SB + (a - SB)) with a in X by lia. exact X. }
      assert (NFa : a <> fa) by (intros ->; exact (NOa FOW)).
      unfold kHighMemBeg in SST. all_app_facts. keeplia Ha NFa SSC SST SHC8 SH1 FHI FLO ACV.
    - (* [comment removed for export] *)
      ufs. eapply (cframe_release (owned A0) (owned A2) (owned (a_release A2 ff))); [exact CF02| exact MU| | keeplia LO CEIL ACV| keeplia SPR| | | intros a X; right; exact X].
      + intros a Ha NO. cbn [outside] in NO.
        assert (CS : sh ff <= a < sh ff + 16 \/ ff <= a < ff + 8 \/ a = fa) by (try (generalize alloc_ceiling_val); clear - Ha NO; try pose proof alloc_ceiling_val as ACV__; lia). clear NO.
        destruct CS as [X|[X|X]]; [left; left; right; change (fsize 1 / 8) with 16; exact X| left; left; left; change (fsize 1) with 128; keeplia X| right; rewrite X; exact FOW].
      + intros i Hi. cbn. keeplia Hi SH1 FHI FAW LO CEIL ACV.
      + intros a Oa. apply ROW in Oa. destruct Oa as [X|[X|X]]; [left; exact X| right; left; left; change (fsize 1) with 128 in *; keeplia X| right; left; right; exact X].
  Qed.
End S.
