(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)

(* [comment removed for export] *)
From Stdlib Require ZArith.
From Stdlib Require NArith.
From Stdlib Require List.
From Stdlib Require Lia.
From Stdlib Require Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase.
From LinuxProcessSemantics.LinuxProcessSem Require RiscvSemantics.
From LinuxProcessSemantics.LinuxProcessSem Require MemImageType.
From LinuxProcessSemantics.LinuxProcessSem Require State.
From LinuxProcessSemantics.LinuxProcessSem Require Run.
From LinuxProcessSemantics.Riscv Require Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Tac.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Bytes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Cells.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AImg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require AShadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_conv.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_musl.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcdefs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_fmt_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_pad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require F_printf_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit_pre2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_defs.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_dicpt.
Module Drv_art.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Cells OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Mem.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_art OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_conv OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition exit_xcells (m : mem) : Prop :=
  cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)]                      (* [comment removed for export] *)
  /\ (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None)  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa6bc0 [C8 (Z_to_bv 64 1)]                  (* [comment removed for export] *)
  /\ rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)].                 (* [comment removed for export] *)

Lemma artcells_split : forall m, ARTCELLS m ->
  icpt_cells m /\ poison_cells m /\ fmt_cells m /\ icpt_cells2 m /\ unreg_cells m /\ unreg_cells2 m /\ exit_xcells m.
Proof.
  intros m H. unfold ARTCELLS in H. unfold A_MUSL_MEMCPY, A_MUSL_MEMSET, A_MUSL_STRLEN, AGLOBALS in *.
  decompose [and ex] H; clear H.
  lazymatch goal with X : cells_at asegs m 0xaaf58 [C1 (Z_to_bv 8 1); C1 (Z_to_bv 8 1)] |- _ =>
    pose proof (proj1 (proj1 (cells_at_app m 0xaaf58 [C1 (Z_to_bv 8 1)] [C1 (Z_to_bv 8 1)]) X)) as X1 end.
  unfold fmt_cells, icpt_cells2, unreg_cells, unreg_cells2, exit_xcells, poison_cells, icpt_cells, shbase_cells, uar_cells, ro_cells, AGLOBALS.
  repeat match goal with |- _ /\ _ => split end; try assumption; try (eexists; eassumption).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma lowsh_musl_lit_shadow : forall m, lowsh_at m -> musl_lit_shadow m.
Proof. intros m HL. exact (lowshadow_musl_lits m HL). Qed.

(* [comment removed for export] *)
Lemma drv_MRT : forall m, icpt_cells m -> icpt_cells2 m -> stack_shadow_zero m -> lowsh_at m -> MRT m.
Proof.
  intros m IC IC2 SSZ HL. unfold MRT. split; [exact IC|]. split; [exact SSZ|]. split; [apply lowsh_musl_lit_shadow; exact HL| exact IC2].
Qed.

(* [comment removed for export] *)
Lemma rw_cell1_CB : forall m A n,
  (forall i, 0 <= i < Z.of_nat n -> exists b, rw_cells asegs m (A + i) [C1 b]) ->
  0 <= A -> A + Z.of_nat n <= 2^64 ->
  exists bs, rw_cells asegs m A [CB n bs].
Proof.
  intros m A n. revert A. induction n as [|n IH]; intros A HC H0 H1.
  - exists []. split; [split; [cbn; split; [reflexivity| exact I]|]|].
    + cbn. split; [lia|]. split; [cbn; lia|]. intros i Hi. cbn in Hi. lia.
    + cbn. split; [lia|]. split; [lia|]. intros i Hi. lia.
  - destruct (HC 0 ltac:(lia)) as [b Hb]. rewrite Z.add_0_r in Hb.
    destruct (IH (A + 1) ltac:(intros i Hi; replace (A + 1 + i) with (A + (1 + i)) by lia; apply HC; lia) ltac:(lia) ltac:(lia)) as [bs Hbs].
    exists (b :: bs).
    pose proof (rw_cells_glue m A [C1 b] [CB n bs] (A + 1) Hb Hbs eq_refl) as G.
    destruct G as [[[_ [Wn _]] HB] HW]. destruct Hbs as [[[Wn' _] _] _]. cbn in Wn'.
    split; [split; [cbn; split; [cbn; rewrite Wn'; reflexivity| exact I]| cbn; cbn in HB; rewrite app_nil_r in HB |- *; exact HB]|].
    cbn [cells_size csize Nat.add] in HW |- *. exact HW.
Qed.

Lemma lowsh_chunk : forall m A n, lowsh_at m -> SH AIMG_LO <= A -> A + Z.of_nat n <= SH AIMG_HI ->
  exists bs, rw_cells asegs m A [CB n bs].
Proof.
  intros m A n HL HA HB. assert (E1 : SH AIMG_LO = 0x7fffa000) by reflexivity. assert (E2 : SH AIMG_HI = 0x800b7e00) by reflexivity.
  apply rw_cell1_CB; [| lia| lia].
  intros i Hi. exists (zb (alowsh (A + i))). apply HL. lia.
Qed.

(* [comment removed for export] *)
Lemma art_exit_shadows : forall m, lowsh_at m ->
  (exists jA, rw_cells asegs m 0x7fffc238 [CB 36 jA]) /\ (exists jB, rw_cells asegs m 0x8000cca8 [CB 8 jB])
  /\ (exists jC, rw_cells asegs m 0x800b3920 [CB 8 jC]) /\ (exists jD, rw_cells asegs m 0x8000cd14 [CB 96 jD]).
Proof.
  intros m HL. assert (E1 : SH AIMG_LO = 0x7fffa000) by reflexivity. assert (E2 : SH AIMG_HI = 0x800b7e00) by reflexivity.
  repeat split; (apply lowsh_chunk; [exact HL| rewrite E1; lia| rewrite E2; cbn; lia]).
Qed.

(* [comment removed for export] *)
Lemma lowsh_msg_shadow_ok : forall m A n, lowsh_at m -> AIMG_LO <= A -> 0 < n -> A + n <= AIMG_HI -> glob_ok_b A n = true -> shadow_ok m A n.
Proof. intros m A n HL H1 H2 H3 H4. exact (lowsh_shadow_ok m A n HL H1 H2 H3 H4). Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma cj_write_ok_stack : forall sp0 SPB LB LF lo hi, alloc_ceiling <= lo -> hi <= SPB -> cj_write_ok sp0 SPB LB LF (lo, hi).
Proof. intros. right; left. cbn [fst snd]. lia. Qed.

Lemma not_in_ART_STATIC : forall a,
  (0xa6558 <= a < 0xa68a0) \/ (0x5dd2a8 <= a < 0x5fd510) \/ (0x5fd518 <= a < 0x5fe5f8) \/ (0x5fe600 <= a < 0x5ff000) ->
  ~ in_zranges ART_STATIC a.
Proof.
  intros a Ha (lo & hi & Hin & R). unfold ART_STATIC, ART_WSTATIC, ADATA_LO in Hin. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). exact Hin.
Qed.

Lemma cj_write_ok_stderr : forall sp0 SPB LB LF, cj_write_ok sp0 SPB LB LF (ASTDERR, ASTDERR + 232).
Proof.
  intros. do 6 right. left. unfold ASTDERR, ADATA_LO, AIMG_HI. cbn [fst snd]. split; [lia|]. split; [lia|].
  intros a Ha. apply not_in_ART_STATIC. lia.
Qed.

Lemma cj_write_ok_stdout : forall sp0 SPB LB LF, cj_write_ok sp0 SPB LB LF (ASTDOUT, ASTDOUT + 232).
Proof.
  intros. do 6 right. left. unfold ASTDOUT, ADATA_LO, AIMG_HI. cbn [fst snd]. split; [lia|]. split; [lia|].
  intros a Ha. apply not_in_ART_STATIC. lia.
Qed.

Lemma cj_write_ok_stdout_buf : forall sp0 SPB LB LF, cj_write_ok sp0 SPB LB LF (ASTDOUT_BUF, ASTDOUT_BUF + 1024).
Proof.
  intros. do 6 right. left. unfold ASTDOUT_BUF, ADATA_LO, AIMG_HI. cbn [fst snd]. split; [lia|]. split; [lia|].
  intros a Ha. apply not_in_ART_STATIC. lia.
Qed.

(* [comment removed for export] *)
Lemma ADSTAT_ssp : forall tid m, ADSTAT tid m -> exists canary : word, ssp_cells m canary /\ assp_cells m canary.
Proof.
  intros tid m D. unfold ADSTAT in D.
  destruct D as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & G1 & (canary & G2)).
  exists canary.
  unfold ssp_cells, assp_cells, got_ssp, ssp_guard, AGOT_SSP, ASSP, AGOT_GUARD, AGUARD, wz in *.
  refine (conj (conj _ _) (conj _ _)); assumption.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)

Lemma not_in_ART_WSTATIC : forall a,
  a < 0xa6bc0 \/ (0xa6bc8 <= a < 0xa6c18) \/ 0x5cc8d0 <= a -> ~ in_zranges ART_WSTATIC a.
Proof.
  intros a Ha (lo & hi & Hin & R). unfold ART_WSTATIC in Hin. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). exact Hin.
Qed.

(* [comment removed for export] *)
Lemma cj_client_range_img : forall sp0 LB LF SP A n,
  ADATA_LO <= A -> A + n <= AIMG_HI ->
  (A + n <= 0xa6bc0 \/ (0xa6bc8 <= A /\ A + n <= 0xa6c18) \/ 0x5cc8d0 <= A) ->
  (A + n <= AERRNO \/ AERRNO + 4 <= A) ->
  cj_client_range sp0 LB LF SP A n.
Proof.
  intros sp0 LB LF SP A n H1 H2 H3 H4. do 7 right. split; [exact H1|]. split; [exact H2|]. split; [| exact H4].
  intros a Ha. apply not_in_ART_WSTATIC. lia.
Qed.

Lemma stderr_wfile0_cj_pres : forall sp0 LB LF SP m m', stderr_wfile0 m -> cj_pres sp0 LB LF SP m m' -> stderr_wfile0 m'.
Proof.
  intros sp0 LB LF SP m m' (flags & mode & e & wend & tail & FC & R) PR. exists flags, mode, e, wend, tail. split; [| exact R].
  eapply cj_pres_rw_cells; [exact PR| exact FC|]. apply cj_client_range_img; unfold ADATA_LO, AIMG_HI, AERRNO, ATP; cbn; lia.
Qed.

Lemma cj_write_ok_errno : forall sp0 SPB LB LF, cj_write_ok sp0 SPB LB LF (AERRNO, AERRNO + 4).
Proof. intros. do 3 right. left. cbn [fst snd]. lia. Qed.

Lemma cj_write_ok_block : forall sp0 SPB LB LF A n lo hi, In (A, n) LB -> A <= lo -> hi <= A + n -> cj_write_ok sp0 SPB LB LF (lo, hi).
Proof. intros. do 7 right. left. exists A, n. cbn [fst snd]. auto. Qed.

(* [comment removed for export] *)
Lemma not_in_ART_STATIC' : forall a,
  (0xa3000 <= a < 0xa3c88) \/ (0xa6518 <= a < 0xa6540) \/ (0xa6558 <= a < 0xa68a0) \/ (0xa6bc8 <= a < 0xa6c18)
  \/ (0x5cc8d0 <= a < 0x5dd1f8) \/ (0x5dd200 <= a < 0x5dd248) \/ (0x5dd264 <= a < 0x5dd278) \/ (0x5dd280 <= a < 0x5fd510)
  \/ (0x5fd518 <= a < 0x5fe5f8) \/ (0x5fe600 <= a < 0x5ff000) ->   (* [comment removed for export] *)
  ~ in_zranges ART_STATIC a.
Proof.
  intros a Ha (lo & hi & Hin & R). unfold ART_STATIC, ART_WSTATIC, ADATA_LO in Hin. cbn in Hin.
  repeat (destruct Hin as [E|Hin]; [injection E as <- <-; lia|]). exact Hin.
Qed.

(* [comment removed for export] *)
Lemma argv_client : forall sp0 LB LF SP a, SP <= a < 2^47 -> cj_client_addr sp0 LB LF SP a.
Proof. intros sp0 LB LF SP a H. left. lia. Qed.

(* [comment removed for export] *)
Lemma cj_write_ok_img : forall sp0 SPB LB LF lo hi,
  ADATA_LO <= lo -> hi <= AIMG_HI ->
  ((0xa3000 <= lo /\ hi <= 0xa3c88) \/ (0xa6558 <= lo /\ hi <= 0xa68a0) \/ (0x5cc8d0 <= lo /\ hi <= 0x5dd1f8)
   \/ (0x5dd2a8 <= lo /\ hi <= 0x5fd510) \/ (0x5fd518 <= lo /\ hi <= 0x5fe5f8) \/ (0x5fe600 <= lo /\ hi <= 0x5ff000)) ->
  cj_write_ok sp0 SPB LB LF (lo, hi).
Proof.
  intros sp0 SPB LB LF lo hi H1 H2 H3. do 6 right. left. cbn [fst snd]. split; [exact H1|]. split; [exact H2|].
  intros a Ha. apply not_in_ART_STATIC'. lia.
Qed.

(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lowsh_buf_zero : forallb (fun k => Z.eqb (alowsh (SBZ_LO + Z.of_nat k)) 0) (seq 0 152) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lowsh_bufsh : forall m, lowsh_at m -> sh_zero m SBUF_LO SBUF_HI.
Proof.
  intros m L a Ha.
  assert (R : SBZ_LO <= SH a < SBZ_HI).
  { rewrite <- SBZ_LO_eq, <- SBZ_HI_eq. unfold SH, SBUF_LO, SBUF_HI in *. Z.div_mod_to_equations. lia. }
  unfold SBZ_LO, SBZ_HI in R.
  pose proof (L (SH a) ltac:(change (SH AIMG_LO) with 2147459072; change (SH AIMG_HI) with 2148236800; lia)) as C.
  assert (Z0 : alowsh (SH a) = 0).
  { pose proof lowsh_buf_zero as FB. rewrite forallb_forall in FB. unfold SBZ_LO in FB.
    specialize (FB (Z.to_nat (SH a - 2148236064)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in FB by lia.
    replace (2148236064 + (SH a - 2148236064)) with (SH a) in FB by lia. apply Z.eqb_eq. exact FB. }
  rewrite Z0 in C. apply (rw_cell1_shb m a 0 C). unfold SBUF_LO, SBUF_HI in Ha. lia.
Qed.

(* [comment removed for export] *)
Lemma rs_alowsh_zero : forallb (fun k => Z.eqb (alowsh (0x800b191a + Z.of_nat k)) 0) (seq 0 (Z.to_nat 8192)) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma lowsh_rs_shadow_ok : forall m a n, lowsh_at m -> ARS <= a -> 0 < n -> a + n <= ARS + 65536 -> shadow_ok m a n.
Proof.
  intros m a n HL Ha Hn Hhi. unfold ARS in *.
  assert (SHLO : SH AIMG_LO = 0x7fffa000) by reflexivity. assert (SHHI : SH AIMG_HI = 0x800b7e00) by reflexivity.
  split.
  - intros i Hi. exists 0. split; [| left; reflexivity].
    assert (R : 0x800b191a <= SH (a + i) < 0x800b191a + 8192) by (unfold SH, SHADOW_OFFSET; Z.div_mod_to_equations; lia).
    pose proof (HL (SH (a + i)) ltac:(rewrite SHLO, SHHI; lia)) as C.
    assert (Z0 : alowsh (SH (a + i)) = 0).
    { pose proof rs_alowsh_zero as FB. rewrite forallb_forall in FB.
      specialize (FB (Z.to_nat (SH (a + i) - 0x800b191a)) ltac:(apply in_seq; lia)). rewrite Z2Nat.id in FB by lia.
      replace (0x800b191a + (SH (a + i) - 0x800b191a)) with (SH (a + i)) in FB by lia. apply Z.eqb_eq. exact FB. }
    rewrite Z0 in C. apply (rw_cell1_shb m (a + i) 0 C). lia.
  - intros j Hj.
    assert (R : 0x7fffa000 <= j < 0x800b7e00) by (unfold SH, SHADOW_OFFSET in Hj; Z.div_mod_to_equations; lia).
    pose proof (HL j ltac:(rewrite SHLO, SHHI; exact R)) as HC.
    eapply rw_cell1_some; [exact HC| unfold AIMG_HI; lia].
Qed.

Lemma stack_shadow_zero_cj_pres : forall sp0 LB LF SP m m',
  stack_shadow_zero m -> cj_pres sp0 LB LF SP m m' -> lowsh_at m' -> stack_shadow_zero m'.
Proof.
  intros sp0 LB LF SP m m' H PR L. split; [eapply stack_part_cj_pres; [exact H| exact PR]| apply lowsh_bufsh; exact L].
Qed.

(* [comment removed for export] *)


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End Drv_art.

(* [comment removed for export] *)
From LinuxProcessSemantics.Riscv Require Instr.
From LinuxProcessSemantics.Riscv Require Decode.
From LinuxProcessSemantics.Riscv Require DecodeC.
From LinuxProcessSemantics.Riscv Require Sem.
From LinuxProcessSemantics.Riscv Require Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require ITree.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Nodes.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Decode.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Prelim.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Monad.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Driver.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require SO_base.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require ShapeSpec.
From Stdlib Require Zify.
Module SO_iface.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.ITree OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Nodes OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Decode OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.SCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Prelim OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Monad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Stdio OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec.Driver.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LBase OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LRz.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_data OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_musl OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcdefs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_pre1 OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.
(* [comment removed for export] *)
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeAlg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.ShapeSpec.

(* [comment removed for export] *)
Import Stdlib.micromega.Zify Stdlib.micromega.Lia.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)

Import ListNotations.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Lia.lia ::= Zify.zify; xlia zchecker.
Open Scope Z_scope.

Notation mem := (word -> option byte).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition AFPRINTF_STACK : Z := 16384.
Definition AEMIT_STACK : Z := 16384.

(* [comment removed for export] *)
Definition fdiag_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (canary : word) (m : mem) (mo : Model) (g : lghost) (K : TSet) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    munch [(bv_unsigned sp - AFPRINTF_STACK, bv_unsigned sp); (ASTDERR, ASTDERR + 232)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    frm0 fc' -> (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
    stk asegs m' lo (bv_unsigned sp) -> stderr_wfile m' -> assp_cells m' canary ->
    LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Ft (ret_pc ra) fc' None m' (seg_rom asegs)) mo g K.

(* [comment removed for export] *)
Definition so_diag_str_stmt (fmt : Z) (msg : list byte -> list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (canary : word) (s slack : list byte) (K : TSet),
    chan_ok mo 2 ->
    stderr_wfile m ->
    fmt_cells m -> MRT m -> lowsh_at m ->
    a0 = Z_to_bv 64 ASTDERR -> a1 = Z_to_bv 64 fmt ->
    bytes_at asegs m (bv_unsigned a2) (s ++ Z_to_bv 8 0 :: slack) -> ~ In (Z_to_bv 8 0) s ->
    ((- (bv_unsigned a2 + zlength s + 1)) mod 8 <= zlength slack) -> (zlength s <= 2^20) ->
    (bv_unsigned sp <= bv_unsigned a2) -> (bv_unsigned a2 + zlength s + 1 + zlength slack + 16 <= 2^47) ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AFPRINTF_STACK <= bv_unsigned sp ->
    (bv_unsigned sp + 64 <= 2^47 - 1) ->
    assp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    K [] ->
    fdiag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m mo g K ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AFPRINTF_T) fc None m (seg_rom asegs)) mo g
        (t_emit (W 2 (msg s)) K).

Definition so_diag_usage_stmt : Prop := so_diag_str_stmt A_FMT_usage msg_usage.
Definition so_diag_cannot_open_stmt : Prop := so_diag_str_stmt A_FMT_cannot_open msg_cannot_open.
Definition so_diag_read_error_stmt : Prop := so_diag_str_stmt A_FMT_read_error msg_read_error.

(* [comment removed for export] *)
Definition so_diag_refused_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (canary : word) (K : TSet),
    chan_ok mo 2 ->
    stderr_wfile m ->
    fmt_cells m -> MRT m -> lowsh_at m ->
    a0 = Z_to_bv 64 ASTDERR -> a1 = Z_to_bv 64 A_FMT_too_big -> bv_unsigned a2 mod 2^32 = 67108864 ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AFPRINTF_STACK <= bv_unsigned sp ->
    (bv_unsigned sp + 64 <= 2^47 - 1) ->
    assp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    K [] ->
    fdiag_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m mo g K ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AFPRINTF_T) fc None m (seg_rom asegs)) mo g
        (t_emit (W 2 msg_refused) K).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition emit_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word)
    (lo : Z) (canary : word) (m : mem) (so' : stdout_st) (mo : Model) (g : lghost) (K : TSet) : Prop :=
  forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Ft : bvmap 5 word) (fc' : bv 32) (m' : mem),
    munch [(bv_unsigned sp - AEMIT_STACK, bv_unsigned sp); (ASTDOUT, ASTDOUT + 232); (ASTDOUT_BUF, ASTDOUT_BUF + 1024)] m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> frm0 fc' ->
    (forall k : reg, bv_unsigned k <> 10 -> reg_get Ft k = reg_get F k) ->
    stk asegs m' lo (bv_unsigned sp) -> stdout_file m' so' -> assp_cells m' canary ->
    LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  Ft (ret_pc ra) fc' None m' (seg_rom asegs)) mo g K.

(* [comment removed for export] *)
Definition emit_after_first : stdout_st := mkStdout true [] false false.

Definition so_emit_first_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (canary : word) (K : TSet),
    chan_ok mo 1 ->
    stdout_file m stdout_init ->
    fmt_cells m -> MRT m -> lowsh_at m ->
    bv_unsigned a1 mod 2^32 = 0 ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEMIT_STACK <= bv_unsigned sp ->
    (bv_unsigned sp + 64 <= 2^47 - 1) ->
    assp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    K [] ->
    emit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m emit_after_first mo g K ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AEMIT) fc None m (seg_rom asegs)) mo g
        (t_emit (W 1 emit_line) K).

(* [comment removed for export] *)
Definition so_emit_again_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (canary : word) (buf : list Z) (K : TSet),
    chan_ok mo 1 ->
    stdout_file m (mkStdout true buf false false) -> zlength buf + 2 <= STDOUT_BUFSIZ -> Forall (fun c => 0 <= c < 256) buf ->
    fmt_cells m -> MRT m -> lowsh_at m ->
    bv_unsigned a1 mod 2^32 = 0 ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEMIT_STACK <= bv_unsigned sp ->
    (bv_unsigned sp + 64 <= 2^47 - 1) ->
    assp_cells m canary -> mem_inv asegs m -> frm0 fc ->
    K [] ->
    emit_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F lo canary m (mkStdout true (buf ++ [48; 10]) false false) mo g K ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AEMIT) fc None m (seg_rom asegs)) mo g
        (t_emit (W 1 []) K).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition so_diag_lit_stmt (A n : Z) (msg : list byte) : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (canary : word) (K : TSet),
    chan_ok mo 2 ->
    stderr_wfile0 m ->
    icpt_cells m -> fwrite_icpt_cells m ->
    (forall a, SH AIMG_LO <= a < SH AIMG_HI -> rw_cells asegs m a [C1 (zb (alowsh a))]) ->
    a0 = Z_to_bv 64 A -> a1 = Z_to_bv 64 n -> a2 = Z_to_bv 64 1 -> a3 = Z_to_bv 64 ASTDERR ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AFWRITE_STACK <= bv_unsigned sp ->
    ssp_cells m canary -> mem_inv asegs m ->
    K [] ->
    (forall (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
        munch [(bv_unsigned sp - AFWRITE_STACK, bv_unsigned sp); (ASTDERR, ASTDERR + 232)] m m' -> wmono asegs m m' ->
        mem_inv asegs m' -> stk asegs m' lo (bv_unsigned sp) -> stderr_wfile0 m' -> ssp_cells m' canary ->
        LRZ asegs (MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                      F (ret_pc ra) fc None m' (seg_rom asegs)) mo g K) ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AFWRITE_T) fc None m (seg_rom asegs)) mo g
        (t_emit (W 2 msg) K).

Definition so_diag_oom_stmt : Prop := so_diag_lit_stmt A_MSG_oom 19 msg_oom.
Definition so_diag_short_stmt : Prop := so_diag_lit_stmt A_MSG_short 31 msg_short.
Definition so_diag_overrun_stmt : Prop := so_diag_lit_stmt A_MSG_overrun 31 msg_overrun.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition AEXIT_DEPTH : Z := AEXIT_PRE_DEPTH.

Definition so_exit_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : mem) (mo : Model) (g : lghost) (lo : Z) (so : stdout_st)
         (code t : Z) (cdt thr sec : byte) (tm1 : word)
         (jA jB jC jD : list byte) (guard : word),
    chan_ok mo 1 ->
    stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo + AEXIT_DEPTH <= bv_unsigned sp -> bv_unsigned sp < 2^47 ->
    tp = Z_to_bv 64 ATP -> a0 = Z_to_bv 64 code -> 0 <= code < 256 -> 0 < t < 2^22 ->
    (* [comment removed for export] *)
    rw_cells asegs m ATIDCELL [C4 (Z_to_bv 64 t)] ->                                               (* [comment removed for export] *)
    rw_cells asegs m 0x5fd4c0 [C4 (Z_to_bv 64 0)] ->                                               (* [comment removed for export] *)
    ATEX m ->                                                                                        (* [comment removed for export] *)
    rw_cells asegs m 0x5fd3c0 [C8 (Z_to_bv 64 0x71918)] ->                                         (* [comment removed for export] *)
    rw_cells asegs m 0x5fd4e0 [C1 cdt; C1 thr; C1 sec; C1 (Z_to_bv 8 0); C4 tm1] ->                (* [comment removed for export] *)
    fini_cells m ->
    rw_cells asegs m 0xa6c10 [C1 (Z_to_bv 8 0)] ->                                                (* [comment removed for export] *)
    (* [comment removed for export] *)
    cells_at asegs m 0x13c120 [C1 (Z_to_bv 8 0)] ->                                               (* [comment removed for export] *)
    unreg_cells m -> unreg_cells2 m -> icpt_cells m -> poison_cells m ->
    (forall a, AGLOBALS <= a < AGLOBALS + 768 -> m (wa a) = None) ->                             (* [comment removed for export] *)
    rw_cells asegs m 0xa6bc0 [C8 (Z_to_bv 64 1)] -> rw_cells asegs m 0xa7b30 [C8 (Z_to_bv 64 0)] -> (* [comment removed for export] *)
    rw_cells asegs m 0x7fffc238 [CB 36 jA] -> rw_cells asegs m 0x8000cca8 [CB 8 jB] ->           (* [comment removed for export] *)
    rw_cells asegs m 0x800b3920 [CB 8 jC] -> rw_cells asegs m 0x8000cd14 [CB 96 jD] ->
    (* [comment removed for export] *)
    rw_cells asegs m AOFL_HEAD [C8 (Z_to_bv 64 0)] ->
    rw_cells asegs m ASTDIN_USED [C8 (Z_to_bv 64 ASTDIN)] ->
    rw_cells asegs m ASTDOUT_USED [C8 (Z_to_bv 64 ASTDOUT)] ->
    rw_cells asegs m ASTDERR_USED [C8 (Z_to_bv 64 ASTDERR)] ->
    stdout_file m so -> zlength (so_buf so) <= 2^25 -> stderr_file m -> stdin_file m ->
    rw_cells asegs m AGOT_GUARD [C8 (Z_to_bv 64 AGUARD)] -> rw_cells asegs m AGUARD [C8 guard] -> (* [comment removed for export] *)
    mem_inv asegs m ->
    LRZ asegs (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                  F (Z_to_bv 64 AEXITF) fc None m (seg_rom asegs)) mo g
        (t_emit (W 1 (to_bytes (so_buf so))) (t_exit (Z_to_bv 64 code) (m_fs mo))).


End CeilWrap.
(* [comment removed for export] *)
Notation mem := (word -> option byte).
End SO_iface.

(* [comment removed for export] *)
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_fwrite.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Drv_icpt_read.
Module Drv_xport.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Tac OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib.Bytes.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AImg OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.AShadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_fmt_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_pad OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.F_printf_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.SO_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Stdio_iface OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_defs OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_base OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_dicpt OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_fwrite.Drv_munch OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Drv_icpt_read.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
Ltac alits := cbv delta [adstat_easy AIMG_HI AERRNO AINITFLAG ARS ATP KHIGHMEM_BEG KHIGHMEM_END SSZ_LO SSZ_HI got_ssp ssp_guard AGOT_SSP ASSP
                         AREAD_STACK AFWRITE_STACK AMALLOC_STACK AINTRIN_STACK
                         ASTDOUT ASTDOUT_BUF ASTDERR ASTDERR_BUF ASTDIN ASTDIN_BUF ASTDOUT_USED ASTDERR_USED ASTDIN_USED AOFL_HEAD AGOT_GUARD AGUARD].
Ltac solve_ForallA tac := repeat (apply Forall_cons; [tac|]); apply Forall_nil.

Lemma assp_cells_munch : forall m m' W canary,
  assp_cells m canary -> munch W m m' -> wmono asegs m m' ->
  Forall (fun iv => (snd iv <= AGOT_SSP \/ AGOT_SSP + 8 <= fst iv) /\ (snd iv <= ASSP \/ ASSP + 8 <= fst iv)) W ->
  assp_cells m' canary.
Proof.
  intros m m' W canary [G1 G2] MU WM FW. split.
  - eapply rw_cells_transport; [exact G1 | exact MU | exact WM |]. eapply disjoint_from_Forall_fw; [exact FW|]. cbn. intros lo hi [HH _]. lia.
  - eapply rw_cells_transport; [exact G2 | exact MU | exact WM |]. eapply disjoint_from_Forall_fw; [exact FW|]. cbn. intros lo hi [_ HH]. lia.
Qed.

Ltac axport H MU WM H' :=
  lazymatch type of H with
  | ADSTAT _ _ => pose proof (ADSTAT_munch_easy _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | DICPT _ => pose proof (DICPT_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stdout_file _ _ => pose proof (stdout_file_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stderr_wfile0 _ => pose proof (stderr_wfile0_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stderr_wfile _ => pose proof (stderr_wfile_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stdin_file _ => pose proof (stdin_file_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stack_shadow_zero _ => pose proof (stack_shadow_zero_munch _ _ _ H MU ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | ssp_cells _ _ => pose proof (ssp_cells_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | assp_cells _ _ => pose proof (assp_cells_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | rw_cells _ _ _ _ => pose proof (rw_cells_transport _ _ _ _ _ _ H MU WM ltac:(pose proof RSN_Z; cbn; alits; lia)) as H'
  | ro_cells _ _ _ _ => pose proof (ro_cells_transport _ _ _ _ _ _ H MU ltac:(cbn; alits; lia)) as H'
  | bytes_at _ _ _ _ => pose proof (bytes_at_transport _ _ _ _ _ _ H MU ltac:(cbn -[Z.add Z.mul Z.of_nat]; rewrite ?length_app; cbn [length]; alits; lia)) as H'
  end.


End CeilWrap.
(* [comment removed for export] *)
Ltac alits := cbv delta [adstat_easy AIMG_HI AERRNO AINITFLAG ARS ATP KHIGHMEM_BEG KHIGHMEM_END SSZ_LO SSZ_HI got_ssp ssp_guard AGOT_SSP ASSP
                         AREAD_STACK AFWRITE_STACK AMALLOC_STACK AINTRIN_STACK
                         ASTDOUT ASTDOUT_BUF ASTDERR ASTDERR_BUF ASTDIN ASTDIN_BUF ASTDOUT_USED ASTDERR_USED ASTDIN_USED AOFL_HEAD AGOT_GUARD AGUARD].
Ltac solve_ForallA tac := repeat (apply Forall_cons; [tac|]); apply Forall_nil.
Ltac axport H MU WM H' :=
  lazymatch type of H with
  | ADSTAT _ _ => pose proof (ADSTAT_munch_easy _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | DICPT _ => pose proof (DICPT_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stdout_file _ _ => pose proof (stdout_file_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stderr_wfile0 _ => pose proof (stderr_wfile0_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stderr_wfile _ => pose proof (stderr_wfile_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stdin_file _ => pose proof (stdin_file_munch _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | stack_shadow_zero _ => pose proof (stack_shadow_zero_munch _ _ _ H MU ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | ssp_cells _ _ => pose proof (ssp_cells_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | assp_cells _ _ => pose proof (assp_cells_munch _ _ _ _ H MU WM ltac:(solve_ForallA ltac:(alits; cbn [fst snd]; lia))) as H'
  | rw_cells _ _ _ _ => pose proof (rw_cells_transport _ _ _ _ _ _ H MU WM ltac:(pose proof RSN_Z; cbn; alits; lia)) as H'
  | ro_cells _ _ _ _ => pose proof (ro_cells_transport _ _ _ _ _ _ H MU ltac:(cbn; alits; lia)) as H'
  | bytes_at _ _ _ _ => pose proof (bytes_at_transport _ _ _ _ _ _ H MU ltac:(cbn -[Z.add Z.mul Z.of_nat]; rewrite ?length_app; cbn [length]; alits; lia)) as H'
  end.
End Drv_xport.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Spec Require Import Prelim Stdio.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LBase LSCPS LSCPS2 LRz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import AImg RT_defs RT_data CJ_iface CJ_tree AShadow CJ_conv ICPT_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require RT_poison8.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.RT_poison8.RT_poison_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require ICPT_pcsdefs.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.ICPT_pcsdefs.SO_shadow.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import ICPT_musl ICPT_pcdefs ICPT_fmt_iface F_pad Exit F_printf_iface SO_base Stdio_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Exit_pre2.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.Exit_pre2.Exit_unreg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Exit_pre2.
Import SO_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_icpt_defs Drv_base Drv_dicpt Drv_iface2 Drv_traces.
Import Drv_art.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import Drv_tac.
Import Drv_xport.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_phex4.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_phex4.CJ_parse_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require CJ_fuzz_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A.CJ_fuzz_iface.CJ_print_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.A Require Import CJ_fuzz_iface Drv_stmt Drv_hooks.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg ShapeSpec.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import NElim.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.

Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Lemma lines_S : forall j, lines j ++ [48; 10] = lines (S j).
Proof.
  intros j. unfold lines. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat]. rewrite <- app_assoc, IH. reflexivity.
Qed.

Lemma lines_zlength : forall j, zlength (lines j) = 2 * Z.of_nat j.
Proof. intros j. unfold lines, zlength. induction j as [|j IH]; [reflexivity|]. cbn [repeat concat app length]. lia. Qed.

Lemma lines_bytes : forall j, Forall (fun c => 0 <= c < 256) (lines j).
Proof.
  intros j. unfold lines. induction j as [|j IH]; [constructor|]. cbn [repeat concat app].
  constructor; [lia|]. constructor; [lia|]. exact IH.
Qed.

(* [comment removed for export] *)
Lemma swrap32_small' : forall z, -2147483648 <= z < 2147483648 -> bv_swrap 32 z = z.
Proof.
  intros z Hz. apply bv_swrap_small. unfold bv_half_modulus, bv_modulus. change (2 ^ Z.of_N 32 `div` 2) with 2147483648. lia.
Qed.

Lemma in_cb_remove_ne : forall (b : cblock) X LB, In b LB -> fst b <> X -> In b (cb_remove X LB).
Proof.
  intros [B n] X LB. induction LB as [|[B' n'] LB IH]; intros Hin Hne; [destruct Hin|].
  cbn. cbn in Hne. destruct Hin as [E|Hin].
  - injection E as -> ->. destruct (Z.eqb_spec B X); [exfalso; exact (Hne e)|]. left. reflexivity.
  - destruct (Z.eqb_spec B' X); [exact Hin|]. right. apply IH; [exact Hin| exact Hne].
Qed.

(* [comment removed for export] *)
Lemma FUZZ_NP_mono : forall a b, 0 <= a <= b -> FUZZ_NP a <= FUZZ_NP b.
Proof. intros. unfold FUZZ_NP. lia. Qed.

Lemma FUZZ_COST_mono : forall a b, 0 <= a <= b -> FUZZ_COST a <= FUZZ_COST b.
Proof. intros. unfold FUZZ_COST. lia. Qed.

Lemma FUZZ_NP_pos : forall a, 0 <= FUZZ_NP a.
Proof. intros. unfold FUZZ_NP. lia. Qed.

Lemma FUZZ_COST_pos : forall a, 0 <= a -> 0 <= FUZZ_COST a.
Proof. intros. unfold FUZZ_COST, PRINT_COST. lia. Qed.

Section S.
  Variables (AI : art_iface) (DI : drv_iface2 AI) (TI : trs_iface) (S_LIB : list (list Z)).
  Let ART := CJ_iface.ART AI.
  Hypothesis TROK : drv_traces_ok TI.
  Hypothesis LIBOK : forall tr, In tr S_LIB -> STAT TI tr.
  Hypothesis FUZZ : llvmfuzz_stmt AI TI S_LIB.

  (* [comment removed for export] *)
  Lemma doc_addr_stack : forall sp0 LB SP a, SP <= a < 2^47 -> alloc_ceiling <= SP -> doc_addr sp0 LB [] SP a.
  Proof. intros sp0 LB SP a Ha HS. try rewrite alloc_ceiling_lit in HS. split; [left; lia|]. unfold AERRNO, ATP, AGERROR0, AGERROR1. lia. Qed.
  Lemma doc_addr_img : forall sp0 LB SP a, aclient_image a -> ~ (AGERROR0 <= a < AGERROR0 + 8) -> ~ (AGERROR1 <= a < AGERROR1 + 8) -> doc_addr sp0 LB [] SP a.
  Proof.
    intros sp0 LB SP a Hi H0 H1. split; [right; left; exact Hi|]. split; [| split; assumption].
    destruct Hi as [H|[H|(_ & _ & H)]]; [unfold AGERROR0 in *| unfold AGERROR1 in *|]; unfold AERRNO, ATP in *; lia.
  Qed.
  (* [comment removed for export] *)
  Lemma adstat_doc : forall sp0 LB SP a, adstat_addr a -> doc_addr sp0 LB [] SP a.
  Proof.
    intros sp0 LB SP a Hd. unfold doc_addr. split; [apply adstat_client; exact Hd|].
    revert Hd. unfold adstat_addr, atex_addr, A_ATEXIT, A_AEF_INIT, AINCB, AINITFLAG, ATIDCELL, AOFL_HEAD, ASTDIN_USED, ASTDOUT_USED, ASTDERR_USED, AGOT_STDERR, ASTDERR_VAR, AGOT_GUARD, AGUARD,
      AERRNO, AGERROR0, AGERROR1, ATP; clear; intros Hd; lia.
  Qed.
  Lemma incb_doc : forall sp0 LB SP a, AINCB <= a < AINCB + 1 -> doc_addr sp0 LB [] SP a.
  Proof.
    intros sp0 LB SP a Ha. apply doc_addr_img; [apply aclient_image_of| |]; revert Ha; unfold AINCB, ADATA_LO, AIMG_HI, AERRNO, ATP, AGERROR0, AGERROR1; clear; intros; lia.
  Qed.
  Lemma ADSTAT_dpres : forall tid sp0 LB SP m m', ADSTAT tid m -> dpres sp0 LB [] SP m m' -> ADSTAT tid m'.
  Proof.
    intros tid sp0 LB SP m m' D PR. eapply ADSTAT_magree; [exact D|]. eapply magree_mono; [exact PR|]. intros a Hd. apply adstat_doc. exact Hd.
  Qed.
  (* [comment removed for export] *)
  Lemma adstat_incb0 : forall tid m, ADSTAT tid m -> rw_cells asegs m AINCB [C1 (Z_to_bv 8 0)].
  Proof.
    intros tid m DS. (nelimp DS 5%nat; intros _ _ _ AT _).
    destruct AT as [(_ & _ & IC)|(_ & _ & _ & IC)]; exact IC.
  Qed.
  Hypothesis SO_EMIT1 : so_emit_first_stmt.
  Hypothesis SO_EMIT2 : so_emit_again_stmt.

  (* [comment removed for export] *)
  Variables (sp gp tp : word) (fs : Fs) (lo SPB : Z) (tid : word)
            (fj : list byte) (v0 v1 v2 v3 v4 v5 v6 v7 ra0 : word) (ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 : word)
            (A cap D plen owned : Z) (pay : list byte).
  Hypothesis TP : tp = wz ATP.
  Hypothesis LO : lo + 2^22 <= bv_unsigned sp + 80.
  Hypothesis GT : alloc_ceiling <= lo.
  Hypothesis SPH : bv_unsigned sp + 128 <= 2^47.
  Hypothesis SPBE : SPB = bv_unsigned sp + 80.
  Hypothesis SPAL : bv_unsigned sp mod 16 = 0.
  Hypothesis PLEN : 0 <= plen < 2^26.
  Hypothesis WIN : sp_window_lo <= bv_unsigned sp + 128.
  Hypothesis BOT : ASTACK_BOTTOM (bv_unsigned sp + 128) <= lo.
  Hypothesis OWN : owned = 0 \/ (owned = D /\ D <> A).
  Notation sp0 := (bv_unsigned sp + 128) (only parsing).

  Lemma CEIL : alloc_ceiling <= lo. Proof. try rewrite alloc_ceiling_lit. exact GT. Qed.

  (* [comment removed for export] *)
  Definition titer (k : Z) (LB : list cblock) (TRS : list (list Z)) (B np : Z) (so : stdout_st) (fc : bv 32)
             (m : word -> option byte) (mo : Model) (g : lghost) : Prop :=
    ART sp0 SPB LB [] TRS B m mo g /\ In (A, cap) LB /\ (owned = 0 \/ In (D, plen) LB)
    /\ (plen <= 4 \/ (In (D, plen) LB /\ bytes_at asegs m D pay /\ Z.of_nat (length pay) = plen))
    /\ TINV TI np TRS /\ 0 <= k /\ 0 <= np /\ np + k * FUZZ_NP (2^26) <= NPMAX TI
    /\ k * FUZZ_COST (2^26) + 2 * cost_free <= B
    /\ (exists e, rw_cells asegs m AERRNO [C4 e]) /\ mem_inv asegs m /\ stk asegs m lo (bv_unsigned sp - 80)
    /\ (exists uj, rw_cells asegs m (bv_unsigned sp - 80) [CB 8 uj; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (wz 0x8202c)])
    /\ rw_cells asegs m (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)
    /\ ADSTAT tid m /\ DICPT m /\ stderr_wfile0 m /\ stdin_file m /\ stack_shadow_zero m /\ stdout_file m so
    /\ DMOD fs FDS0 mo /\ frm0 fc.

  Notation TRET := (trun_ret AI TI sp gp tp fs lo SPB tid fj v0 v1 v2 v3 v4 v5 v6 v7 ra0 ms0 ms1 ms2 ms3 ms4 ms5 s6 s7 s8 s9 s10 s11 A cap).

  (* [comment removed for export] *)
  Definition SM2 : Z := 18446744073709551614.   (* [comment removed for export] *)
  Notation LST pc Fv fcv mm rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31 :=
    (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 owned) x19 (Z_to_bv 64 AINITFLAG) (Z_to_bv 64 cnt) (Z_to_bv 64 0) (Z_to_bv 64 SM2) s8 s9 s10 s11 x28 x29 x30 x31)
        Fv (Z_to_bv 64 pc) fcv None mm (seg_rom asegs)) (only parsing).

  (* [comment removed for export] *)
  Lemma emit_facts : forall LB TRS B m mo g,
    ART sp0 SPB LB [] TRS B m mo g -> ADSTAT tid m -> stack_shadow_zero m ->
    fmt_cells m /\ MRT m /\ lowsh_at m /\ exists cn0 : word, assp_cells m cn0.
  Proof.
    intros LB TRS B m mo g HART DS SSZ.
    (nelimp (artcells_split m (art_rtcells AI _ _ _ _ _ _ _ _ _ HART)) 7%nat; intros IC PC FMC IC2 UC UC2 XC).
    pose proof (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART) as LOW.
    (nelim (ADSTAT_ssp tid m DS) 3%nat; intros cn0 SSP ASSP).
    split; [exact FMC|]. split; [apply drv_MRT; [exact IC| exact IC2| exact SSZ| exact LOW]|]. split; [exact LOW| exists cn0; exact ASSP].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_call : forall (k : Z) LB TRS B np so fc m mo g (F : bvmap 5 word) (cnt : Z) (T : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    titer k LB TRS B np so fc m mo g -> 1 <= k ->
    (forall LB' TRS' B' np' fc' m' mo' g' (F' : bvmap 5 word) y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        titer (k - 1) LB' TRS' B' np' so fc' m' mo' g' ->
        LRZ asegs (LST 0x82310 F' fc' m' (Z_to_bv 64 0x82264) y5 y6 y7 (Z_to_bv 64 0) (Z_to_bv 64 0) y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo' g' T) ->
    LRZ asegs (LST 0x82240 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31) mo g T.
  Proof.
    intros until x31. intros IT Hk K.
    (nelim IT 22%nat; intros HART INA IND PAY HT K0 NP0 HNP HB [e ER] MI ST [u TFR] MFR DS DIC SEF SIF SSZ SOF DM FRM).
    pose proof CEIL as CE. pose proof GT as GT'. try rewrite <- alloc_ceiling_lit in GT'.
    unfold AERRNO, ATP in ER.
    pose proof (FUZZ_NP_mono plen (2^26) ltac:(lia)) as NPM. pose proof (FUZZ_COST_mono plen (2^26) ltac:(lia)) as FCM.
    pose proof (Z.mul_nonneg_nonneg (k - 1) (FUZZ_NP (2^26)) ltac:(lia) (FUZZ_NP_pos _)) as NPK.
    pose proof (Z.mul_nonneg_nonneg (k - 1) (FUZZ_COST (2^26)) ltac:(lia) (FUZZ_COST_pos (2^26) ltac:(lia))) as FCK.
    pose proof cost_free_eq as CF.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART INA) 4%nat; intros BR1 BR2 BR3 BR4). unfold AIMG_HI in BR1. try rewrite alloc_ceiling_lit in BR4.
    (* [comment removed for export] *)
    pose proof (adstat_incb0 tid m DS) as IC. unfold AINCB in IC.
    pose proof (munch_refl [(AINCB, AINCB + 1)] m) as MU. pose proof (wmono_refl asegs m) as WM. unfold AINCB in MU.
    apply lrz_step_evt. unfold AINITFLAG. step. step; fix_litstore; mem_after_store_opt.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
    assert (HART1 : ART sp0 SPB LB [] TRS B m1 mo g).
    { eapply (art_frame AI); [exact HART| exact MU| exact WM|]. apply Forall_cons; [apply cj_write_ok_img; unfold ADATA_LO, AIMG_HI; cbn; lia| apply Forall_nil]. }
    assert (AG1 : magree (fun a => adstat_addr a /\ ~ (AINCB <= a < AINCB + 1)) m m1).
    { eapply magree_of_munch; [exact MU| exact WM|]. unfold AINCB. intros a _ [_ Ha]. cbn. lia. }
    assert (PAY1 : plen <= 4 \/ (In (D, plen) LB /\ bytes_at asegs m1 D pay /\ Z.of_nat (length pay) = plen)).
    { destruct PAY as [H|(H1 & H2 & H3)]; [left; exact H| right]. split; [exact H1|]. split; [| exact H3].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ D plen HART H1) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, AIMG_HI in R1.
      axport H2 MU WM H2'. exact H2'. }
    (* [comment removed for export] *)
    axport DIC MU WM DIC1. axport SEF MU WM SEF1. axport SIF MU WM SIF1. axport SSZ MU WM SSZ1. axport SOF MU WM SOF1.
    assert (IC1 : rw_cells asegs m1 AINCB [C1 (Z_to_bv 8 1)]) by (unfold AINCB; exact IC).
    clear MU WM.
    do 3 step. apply evt_done.
    change (Z_to_bv 64 6146256) with (Z_to_bv 64 AINITFLAG : word).
    eapply lrz_lscps_vm.
    { eapply (FUZZ) with (lo := lo) (data := pay) (LB := LB) (SPB := SPB) (errv := e) (sp0 := sp0) (np := np) (size := plen) (D := D);
        [ exact HART1 | exact HT | lia | exact LIBOK | exact PAY1 | exact PLEN
        | unfold AERRNO, ATP; exact ER | exact MI
        | rewrite unsigned_lit by lia; exact ST | exact CEIL
        | rewrite unsigned_lit by lia; unfold AFUZZ_STACK, PARSE_DOC_STACK, PARSE_STACK; lia
        | rewrite unsigned_lit by lia; rewrite SPBE; lia
        | rewrite unsigned_lit by lia; rewrite <- Zminus_mod_idemp_l, SPAL; reflexivity
        | rewrite SPBE; lia | lia
        | rewrite unsigned_lit by lia; revert SPH; clear; intros SPH; unfold ASTACK_TOP, roundup; Z.div_mod_to_equations; lia
        | exact BOT
        | rewrite unsigned_lit by lia; lia
        | exact FRM | exact TP | reflexivity | reflexivity
        | lia
        | exact (proj1 SSZ1) ]. }
    cbv beta. intros ms' mo' g' PO VO.
    (nelim PO 40%nat; intros y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 F' fc' m' e' LB' LX TRS' B' np' -> -> FRM' _ MI' ST' ER' HART' HP PR GM HT' HNP' HB' SSZ' PAY')
.
    rewrite ?unsigned_lit in ST', PR by lia.
    replace (ret_pc (Z_to_bv 64 0x82254)) with (Z_to_bv 64 0x82254 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    (* [comment removed for export] *)
    assert (IC2 : rw_cells asegs m' AINCB [C1 (Z_to_bv 8 1)]).
    { eapply rw_cells_magree; [exact PR| exact IC1|]. cbn. intros a Ha. apply incb_doc. lia. }
    unfold AINCB in IC2.
    pose proof (munch_refl [(AINCB, AINCB + 1)] m') as MU. pose proof (wmono_refl asegs m') as WM. unfold AINCB in MU.
    (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ A cap HART' ltac:(eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact INA])) 4%nat; intros BS1 BS2 BS3 BS4).
    unfold AIMG_HI in BS1. try rewrite alloc_ceiling_lit in BS4.
    unfold AERRNO, ATP in ER'.
    apply lrz_step_evt. unfold wz, AINITFLAG. step. step; fix_litstore; mem_after_store_opt.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m3 end.
    assert (HART3 : ART sp0 SPB LB' [] TRS' B' m3 mo' g').
    { eapply (art_frame AI); [exact HART'| exact MU| exact WM|]. apply Forall_cons; [apply cj_write_ok_img; unfold ADATA_LO, AIMG_HI; cbn; lia| apply Forall_nil]. }
    assert (AG3 : magree (fun a => adstat_addr a /\ ~ (AINCB <= a < AINCB + 1)) m m3).
    { eapply magree_trans; [exact AG1|]. eapply magree_trans.
      - eapply magree_mono; [exact PR|]. intros a [Ha _]. apply adstat_doc. exact Ha.
      - eapply magree_of_munch; [exact MU| exact WM|]. unfold AINCB. intros a _ [_ Ha]. cbn. lia. }
    assert (IC3 : rw_cells asegs m3 AINCB [C1 (Z_to_bv 8 0)]) by (unfold AINCB; assumption).
    pose proof (ADSTAT_incb tid m m3 DS AG3 IC3) as DS3.
    assert (INL : forall b, In b LB -> In b LB').
    { intros b Hb. eapply Permutation_in; [apply Permutation_sym; exact HP| apply in_or_app; left; exact Hb]. }
    do 2 step. apply evt_done.
    eapply K. split; [exact HART3|]. split; [apply INL; exact INA|]. split.
    { destruct IND as [H|H]; [left; exact H| right; apply INL; exact H]. }
    split.
    { destruct PAY' as [H'|H']; [left; exact H'|]. destruct PAY as [H|(H1 & H2 & H3)]; [left; exact H| right].
      split; [apply INL; exact H1|]. split; [| exact H3].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ D plen HART' ltac:(apply INL; exact H1)) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, AIMG_HI in R1. try rewrite alloc_ceiling_lit in R4.
      axport H' MU WM H''. exact H''. }
    split; [exact HT'|]. split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
    split; [exists e'; exact ER'|]. split; [exact MI'|]. split; [exact ST'|]. split.
    { exists u. assert (TFR2 : rw_cells asegs m' (bv_unsigned sp - 80) [CB 8 u; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x8202c)]).
      { eapply rw_cells_magree; [exact PR| exact TFR| cbn; intros a Ha; apply doc_addr_stack; [lia| try rewrite alloc_ceiling_lit; lia]]. }
      axport TFR2 MU WM TFR3. exact TFR3. }
    split. { assert (MFR2 : rw_cells asegs m' (bv_unsigned sp) (mframe fj v0 v1 v2 v3 v4 v5 v6 v7 ra0)).
             { eapply rw_cells_magree; [exact PR| exact MFR| cbn; intros a Ha; apply doc_addr_stack; [lia| try rewrite alloc_ceiling_lit; lia]]. }
             axport MFR2 MU WM MFR3. exact MFR3. }
    split. { exact DS3. }
    split. { assert (DIC2 : DICPT m').
             { eapply DICPT_magree; [exact DIC1| eapply magree_mono; [exact PR|]]. intros a Hd. apply doc_addr_img; [apply aclient_image_of| |]; revert Hd; unfold dicpt_addr, ADATA_LO, AIMG_HI, AGERROR0, AGERROR1; clear; intros; lia. }
             axport DIC2 MU WM DIC3. exact DIC3. }
    split. { assert (SEF2 : stderr_wfile0 m').
             { (nelim SEF1 7%nat; intros flags mode ee wend tail FC R). exists flags, mode, ee, wend, tail. split; [| exact R].
               eapply rw_cells_magree; [exact PR| exact FC|]. unfold ASTDERR. cbn. intros a Ha. apply doc_addr_img; [apply aclient_image_of| |]; revert Ha; unfold ADATA_LO, AIMG_HI, AGERROR0, AGERROR1; clear; intros; lia. }
             axport SEF2 MU WM SEF3. exact SEF3. }
    split. { assert (SIF2 : stdin_file m').
             { eapply stdin_file_magree; [exact SIF1| exact PR|]. intros a Ha. apply doc_addr_img; [apply aclient_image_of| |]; revert Ha; unfold ASTDIN, ADATA_LO, AIMG_HI, AGERROR0, AGERROR1; clear; intros; lia. }
             axport SIF2 MU WM SIF3. exact SIF3. }
    split. { assert (SSZ2 : stack_shadow_zero m') by (split; [exact SSZ'| apply lowsh_bufsh; exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART')]).
             axport SSZ2 MU WM SSZ3. exact SSZ3. }   (* [comment removed for export] *)
    split. { assert (SOF2 : stdout_file m' so).
             { eapply stdout_file_magree; [exact SOF1| exact PR|]. intros a Ha. apply doc_addr_img; [apply aclient_image_of| |]; revert Ha; unfold ASTDOUT, ASTDOUT_BUF, ADATA_LO, AIMG_HI, AGERROR0, AGERROR1; clear; intros; lia. }
             axport SOF2 MU WM SOF3. exact SOF3. }
    split. { eapply DMOD_vm_only; [exact DM| exact VO]. }
    exact FRM'.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_ctrl : forall (n : nat) (k : Z) LB TRS B np so fc m mo g (F : bvmap 5 word) (T : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    titer k LB TRS B np so fc m mo g -> (1 <= n <= 4)%nat ->
    (forall x19, n = 1%nat -> LRZ asegs (LST 0x82278 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 0 x28 x29 x30 x31) mo g T) ->
    (forall x19, (2 <= n)%nat -> LRZ asegs (LST 0x82240 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z.of_nat n - 1) x28 x29 x30 x31) mo g T) ->
    LRZ asegs (LST 0x82264 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) (Z.of_nat n) x28 x29 x30 x31) mo g T.
  Proof.
    intros until x31. intros IT Hn K1 K2.
    apply lrz_step_evt. unfold SM2.
    step. (* [comment removed for export] *)
    step. if_cases K; zify_cond K; [clear K| exfalso; clear - K; lia]. (* [comment removed for export] *)
    step.
    rewrite (unsigned_lit (Z.of_nat n)) by lia. rewrite swrap32_small' by lia.
    step. if_cases K'; zify_cond K'; rewrite ?unsigned_lit in K' by lia.
    - apply evt_done. replace (Z.of_nat n + -1) with (Z.of_nat n - 1) by lia. apply K2. lia.
    - apply evt_done. replace (Z.of_nat n + -1) with 0 by lia. apply K1. lia.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_tail : forall (k : Z) LB TRS B np so fc m mo g (F : bvmap 5 word) (T : TSet) (cnt : Z) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    titer k LB TRS B np so fc m mo g ->
    (forall ms' mo' g', TRET 0 so ms' mo' g' -> LRZ asegs ms' mo' g' T) ->
    LRZ asegs (LST 0x82278 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 cnt x28 x29 x30 x31) mo g T.
  Proof.
    intros until x31. intros IT K.
    (nelim IT 22%nat; intros HART INA IND PAY HT K0 NP0 HNP HB [e ER] MI ST [u TFR] MFR DS DIC SEF SIF SSZ SOF DM FRM).
    pose proof CEIL as CE. pose proof GT as GT'. try rewrite <- alloc_ceiling_lit in GT'.
    pose proof (FUZZ_COST_pos (2^26) ltac:(lia)) as FC0. pose proof (Z.mul_nonneg_nonneg k (FUZZ_COST (2^26)) K0 FC0) as KF.
    pose proof cost_free_eq as CF.
    unfold AERRNO, ATP in ER. unfold wz in TFR.
    apply lrz_step_evt. unfold SM2. do 2 step. apply evt_done.
    destruct (Z.eq_dec owned 0) as [OW | NZ].
    - (* [comment removed for export] *)
      rewrite OW.
      eapply (drv_free_null AI) with (lo := lo) (sp0 := sp0) (SPB := SPB) (LB := LB) (TRS := TRS) (B := B) (errv := e);
        [ exact HART | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto | rewrite !unsigned_lit by lia; lia | rewrite unsigned_lit by lia; rewrite SPBE; lia
        | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
        | unfold AERRNO, ATP; exact ER | exact MI | exact TP | reflexivity | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' g' MI' ST' ER' PR GM HV HART'.
      rewrite ?unsigned_lit in ST', PR by lia.
      replace (ret_pc (Z_to_bv 64 0x82280)) with (Z_to_bv 64 0x82280 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TFR' : rw_cells asegs m' (bv_unsigned sp - 80) [CB 8 u; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x8202c)]).
      { eapply cj_pres_rw_cells; [exact PR| exact TFR| left; cbn; lia]. }
      unfold AERRNO, ATP in ER'.
      apply lrz_step_evt. do 3 step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1) + -1))) 78)) with (Z_to_bv 64 0 : word)
        by (apply bv_eq; vm_compute; reflexivity).
      do 11 step. (* [comment removed for export] *)
      replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      apply evt_done. apply K.
      unfold trun_ret.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m', e, LB, TRS, B, np.
      split; [reflexivity|]. split; [exact FRM|]. split; [exact MI'|]. split.
      { pose proof (stk_release asegs m' lo _ _ ST' TFR' ltac:(lia)) as ST2. cbn [cells_size Cells.csize Nat.add] in ST2.
        replace (bv_unsigned sp - 80 + Z.of_nat 80) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      split; [unfold AERRNO, ATP; exact ER'|]. split; [exact HART'|]. split; [exact INA|]. split; [exact HT|]. split; [lia|].
      split. { eapply cj_pres_rw_cells; [exact PR| exact MFR| left; cbn; lia]. }
      split. { eapply ADSTAT_cj_pres; [exact DS| exact PR]. }
      split. { eapply DICPT_cj_pres; [exact DIC| exact PR]. }
      split. { eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]. }
      split. { eapply stdin_file_cj_pres; [exact SIF| exact PR]. }
      split. { eapply stack_shadow_zero_cj_pres; [exact SSZ| exact PR| exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART')]. }
      split. { eapply stdout_file_cj_pres; [exact SOF| exact PR]. }
      eapply DMOD_vm_only; [exact DM| exact HV].
    - (* [comment removed for export] *)
      destruct OWN as [H0 | [OW DNA]]; [exfalso; exact (NZ H0)|].
      rewrite OW. assert (INDL : In (D, plen) LB) by (destruct IND as [H|H]; [exfalso; exact (NZ H)| exact H]).
      eapply (drv_free AI TI TROK) with (lo := lo) (sp0 := sp0) (SPB := SPB) (LB := LB) (TRS := TRS) (B := B) (np := np) (A := D) (n := plen) (errv := e);
        [ exact HART | exact INDL | exact HT | unfold S_DRIVER; rewrite unsigned_lit by lia; cbn; tauto
        | rewrite !unsigned_lit by lia; lia | rewrite unsigned_lit by lia; rewrite SPBE; lia
        | rewrite unsigned_lit by lia; exact ST | exact CEIL | rewrite unsigned_lit by lia; unfold AMALLOC_STACK; lia
        | unfold AERRNO, ATP; exact ER | exact MI | exact TP | reflexivity | lia | ].
      intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' mo' g' TRS' MI' ST' ER' PR GM HT' HV HART'.
      rewrite ?unsigned_lit in ST', PR by lia.
      replace (ret_pc (Z_to_bv 64 0x82280)) with (Z_to_bv 64 0x82280 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      assert (TFR' : rw_cells asegs m' (bv_unsigned sp - 80) [CB 8 u; C8 s7; C8 s6; C8 ms5; C8 ms4; C8 ms3; C8 ms2; C8 ms1; C8 ms0; C8 (Z_to_bv 64 0x8202c)]).
      { eapply cj_pres_rw_cells; [exact PR| exact TFR| left; cbn; lia]. }
      unfold AERRNO, ATP in ER'.
      apply lrz_step_evt. do 3 step. (* [comment removed for export] *)
      replace (Z_to_bv 64 (Z.land (bv_unsigned (Z_to_bv 64 (bv_unsigned (v_sltiu (Z_to_bv 64 0) 1) + -1))) 78)) with (Z_to_bv 64 0 : word)
        by (apply bv_eq; vm_compute; reflexivity).
      do 11 step. (* [comment removed for export] *)
      replace (bv_unsigned sp - 80 + 80) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
      apply evt_done. apply K.
      unfold trun_ret.
      eexists _, _, _, _, _, _, _, _, _, _, _, _, _, _, F, fc, m', e, (cb_remove D LB), TRS', (B - cost_free), np.
      split; [reflexivity|]. split; [exact FRM|]. split; [exact MI'|]. split.
      { pose proof (stk_release asegs m' lo _ _ ST' TFR' ltac:(lia)) as ST2. cbn [cells_size Cells.csize Nat.add] in ST2.
        replace (bv_unsigned sp - 80 + Z.of_nat 80) with (bv_unsigned sp) in ST2 by lia. exact ST2. }
      split; [unfold AERRNO, ATP; exact ER'|]. split; [exact HART'|].
      split; [apply in_cb_remove_ne; [exact INA| cbn; intros E; apply DNA; symmetry; exact E]|]. split; [exact HT'|]. split; [lia|].
      split. { eapply cj_pres_rw_cells; [exact PR| exact MFR| left; cbn; lia]. }
      split. { eapply ADSTAT_cj_pres; [exact DS| exact PR]. }
      split. { eapply DICPT_cj_pres; [exact DIC| exact PR]. }
      split. { eapply stderr_wfile0_cj_pres; [exact SEF| exact PR]. }
      split. { eapply stdin_file_cj_pres; [exact SIF| exact PR]. }
      split. { eapply stack_shadow_zero_cj_pres; [exact SSZ| exact PR| exact (art_lowshadow AI _ _ _ _ _ _ _ _ _ HART')]. }
      split. { eapply stdout_file_cj_pres; [exact SOF| exact PR]. }
      eapply DMOD_vm_only; [exact DM| exact HV].
  Qed.

  (* [comment removed for export] *)
  Lemma titer_emit : forall k LB TRS B np so so' fc fc' m m' mo g,
    titer k LB TRS B np so fc m mo g ->
    munch [(bv_unsigned sp - 80 - AEMIT_STACK, bv_unsigned sp - 80); (ASTDOUT, ASTDOUT + 232); (ASTDOUT_BUF, ASTDOUT_BUF + 1024)] m m' ->
    wmono asegs m m' -> mem_inv asegs m' -> frm0 fc' -> stk asegs m' lo (bv_unsigned sp - 80) -> stdout_file m' so' ->
    titer k LB TRS B np so' fc' m' mo g.
  Proof.
    intros until g. intros IT MU WM MI' FRM' ST' SOF'.
    (nelim IT 22%nat; intros HART INA IND PAY HT K0 NP0 HNP HB [e ER] MI ST [u TFR] MFR DS DIC SEF SIF SSZ SOF DM FRM).
    pose proof CEIL as CE. try rewrite alloc_ceiling_lit in CE.
    split.
    { eapply (art_frame AI); [exact HART| exact MU| exact WM|].
      apply Forall_cons; [apply cj_write_ok_stack; [try rewrite alloc_ceiling_lit; unfold AEMIT_STACK| rewrite SPBE]; lia|].
      apply Forall_cons; [apply cj_write_ok_stdout|]. apply Forall_cons; [apply cj_write_ok_stdout_buf| apply Forall_nil]. }
    split; [exact INA|]. split; [exact IND|]. split.
    { destruct PAY as [H|(H1 & H2 & H3)]; [left; exact H| right]. split; [exact H1|]. split; [| exact H3].
      (nelimp (art_block_range AI _ _ _ _ _ _ _ _ _ D plen HART H1) 4%nat; intros R1 R2 R3 R4). unfold KHIGHMEM_BEG, AIMG_HI in R1. try rewrite alloc_ceiling_lit in R4.
      unfold AEMIT_STACK in MU. axport H2 MU WM H2'. exact H2'. }
    split; [exact HT|]. split; [exact K0|]. split; [exact NP0|]. split; [exact HNP|]. split; [exact HB|].
    unfold AEMIT_STACK in MU. unfold AERRNO, ATP in ER.
    split. { axport ER MU WM ER'. exists e. exact ER'. }
    split; [exact MI'|]. split; [exact ST'|].
    split. { axport TFR MU WM TFR'. exists u. exact TFR'. }
    split. { axport MFR MU WM MFR'. exact MFR'. }
    split. { axport DS MU WM DS'. exact DS'. }
    split. { axport DIC MU WM DIC'. exact DIC'. }
    split. { axport SEF MU WM SEF'. exact SEF'. }
    split. { axport SIF MU WM SIF'. exact SIF'. }
    split. { axport SSZ MU WM SSZ'. exact SSZ'. }
    split; [exact SOF'|]. split; [exact DM| exact FRM'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_emit2 : forall (j : nat) (k : Z) LB TRS B np fc m mo g (F : bvmap 5 word) (K : TSet) (cnt : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    titer k LB TRS B np (so_after j) fc m mo g -> (j <= 3)%nat -> K [] ->
    (forall fc' m' (F' : bvmap 5 word) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        titer k LB TRS B np (so_after (S j)) fc' m' mo g ->
        LRZ asegs (LST 0x82264 F' fc' m' (Z_to_bv 64 0x82264) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo g K) ->
    LRZ asegs (LST 0x82310 F fc m (Z_to_bv 64 0x82264) x5 x6 x7 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) cnt x28 x29 x30 x31) mo g K.
  Proof.
    intros until x31. intros IT Hj HK K2.
    (nelimp IT 22%nat; intros HART INA IND PAY HT K0 NP0 HNP HB [e ER] MI ST [u TFR] MFR DS DIC SEF SIF SSZ SOF DM FRM).
    destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    destruct (emit_facts _ _ _ _ _ _ HART DS SSZ) as (FMC & MR & LOW & (cn0 & ASSP)).
    pose proof (lines_zlength j) as LL. pose proof (lines_bytes j) as LBY.
    apply lrz_drop_nil; [exact HK|].
    unfold so_after in SOF. unfold SM2.
    eapply (SO_EMIT2 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0 (lines j) K);
      first [exact CH1| exact SOF| exact LBY| exact FMC| exact MR| exact LOW| exact ASSP| exact MI| exact FRM| exact HK| exact CEIL
            | rewrite ?unsigned_lit by lia; first [exact ST| reflexivity| unfold STDOUT_BUFSIZ, AEMIT_STACK in *; lia] | idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU WM MI' FRM' FA ST' SOF' ASSP'.
    rewrite ?unsigned_lit in MU, ST' by lia.
    replace (ret_pc (Z_to_bv 64 0x82264)) with (Z_to_bv 64 0x82264 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply K2. rewrite lines_S in SOF'. eapply titer_emit; [exact IT| exact MU| exact WM| exact MI'| exact FRM'| exact ST'| exact SOF'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_emit1 : forall (k : Z) LB TRS B np fc m mo g (F : bvmap 5 word) (K : TSet) (cnt : Z) x5 x6 x7 x10 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31,
    titer k LB TRS B np stdout_init fc m mo g -> K [] ->
    (forall fc' m' (F' : bvmap 5 word) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31,
        titer k LB TRS B np (so_after 0) fc' m' mo g ->
        LRZ asegs (LST 0x82264 F' fc' m' (Z_to_bv 64 0x82264) y5 y6 y7 y10 y11 y12 y13 y14 y15 y16 y17 (Z_to_bv 64 0) cnt y28 y29 y30 y31) mo g K) ->
    LRZ asegs (LST 0x82310 F fc m (Z_to_bv 64 0x82264) x5 x6 x7 x10 (Z_to_bv 64 0) x12 x13 x14 x15 x16 x17 (Z_to_bv 64 0) cnt x28 x29 x30 x31) mo g
        (t_emit (W 1 emit_line) K).
  Proof.
    intros until x31. intros IT HK K2.
    (nelimp IT 22%nat; intros HART INA IND PAY HT K0 NP0 HNP HB [e ER] MI ST [u TFR] MFR DS DIC SEF SIF SSZ SOF DM FRM).
    destruct (DMOD_chan _ _ _ DM ltac:(left; reflexivity)) as [CH1 CH2].
    destruct (emit_facts _ _ _ _ _ _ HART DS SSZ) as (FMC & MR & LOW & (cn0 & ASSP)).
    unfold SM2.
    eapply (SO_EMIT1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m mo g lo cn0 K);
      first [exact CH1| exact SOF| exact FMC| exact MR| exact LOW| exact ASSP| exact MI| exact FRM| exact HK| exact CEIL
            | rewrite ?unsigned_lit by lia; first [exact ST| reflexivity| unfold AEMIT_STACK in *; lia] | idtac].
    intros t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' Ft fc' m' MU WM MI' FRM' FA ST' SOF' ASSP'.
    rewrite ?unsigned_lit in MU, ST' by lia.
    replace (ret_pc (Z_to_bv 64 0x82264)) with (Z_to_bv 64 0x82264 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
    apply K2. change emit_after_first with (so_after 0) in SOF'.
    eapply titer_emit; [exact IT| exact MU| exact WM| exact MI'| exact FRM'| exact ST'| exact SOF'].
  Qed.

  (* [comment removed for export] *)
  Lemma trun_again : forall (n j : nat) LB TRS B np fc m mo g (F : bvmap 5 word) (KT : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x28 x29 x30 x31,
    titer (Z.of_nat n) LB TRS B np (so_after j) fc m mo g -> (1 <= n)%nat -> (j + n <= 4)%nat -> KT [] ->
    (forall ms' mo' g', TRET 0 (so_after (j + n)) ms' mo' g' -> LRZ asegs ms' mo' g' KT) ->
    LRZ asegs (LST 0x82240 F fc m rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 (Z.of_nat n) x28 x29 x30 x31) mo g KT.
  Proof.
    induction n as [|n IH]; intros until x31; intros IT Hn Hjn HK KF; [exfalso; lia|].
    eapply trun_call; [exact IT| lia|].
    intros LB' TRS' B' np' fc' m' mo' g' F' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 IT'.
    eapply trun_emit2; [exact IT'| lia| exact HK|].
    intros fc2 m2 F2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 IT2.
    eapply trun_ctrl; [exact IT2| lia| |].
    - intros z19 Hn1. eapply trun_tail; [exact IT2|]. intros msx mox gx HR. apply KF. replace (j + S n)%nat with (S j) by lia. exact HR.
    - intros z19 Hn2. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) by lia. replace (Z.of_nat (S n) - 1) with (Z.of_nat n) in IT2 by lia.
      eapply IH; [exact IT2| lia| lia| exact HK|]. intros msx mox gx HR. apply KF. replace (j + S n)%nat with (S j + n)%nat by lia. exact HR.
  Qed.

  (* [comment removed for export] *)
  Lemma trun_rounds : forall (c : nat) LB TRS B np fc m mo g (F : bvmap 5 word) (KT : TSet) rav x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x19 x22 x23 x28 x29 x30 x31,
    titer (Z.of_nat c) LB TRS B np stdout_init fc m mo g -> (1 <= c <= 4)%nat -> KT [] ->
    (forall ms' mo' g', TRET 0 (so_after (c - 1)) ms' mo' g' -> LRZ asegs ms' mo' g' KT) ->
    LRZ asegs (MS (mkR rav (Z_to_bv 64 (bv_unsigned sp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 plen) (Z_to_bv 64 D) x10 x11 x12 x13 x14 x15 x16 x17
                   (Z_to_bv 64 owned) x19 (Z_to_bv 64 AINITFLAG) (Z_to_bv 64 (Z.of_nat c)) x22 x23 s8 s9 s10 s11 x28 x29 x30 x31)
               F (Z_to_bv 64 0x82238) fc None m (seg_rom asegs)) mo g
        (t_emit (W 1 emit_line) KT).
  Proof.
    intros until x31; intros IT Hc HK KF.
    apply lrz_step_evt. do 2 step. apply evt_done.
    replace (Z_to_bv 64 (-2)) with (Z_to_bv 64 SM2 : word) by (apply bv_eq; vm_compute; reflexivity).
    eapply trun_call; [exact IT| lia|].
    intros LB' TRS' B' np' fc' m' mo' g' F' y5 y6 y7 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 IT'.
    eapply trun_emit1; [exact IT'| exact HK|].
    intros fc2 m2 F2 z5 z6 z7 z10 z11 z12 z13 z14 z15 z16 z17 z28 z29 z30 z31 IT2.
    eapply trun_ctrl; [exact IT2| lia| |].
    - intros z19 Hc1. eapply trun_tail; [exact IT2|]. intros msx mox gx HR. apply KF. replace (c - 1)%nat with 0%nat by lia. exact HR.
    - intros z19 Hc2. replace (Z.of_nat c - 1) with (Z.of_nat (c - 1)) by lia. replace (Z.of_nat c - 1) with (Z.of_nat (c - 1)) in IT2 by lia.
      eapply trun_again; [exact IT2| lia| lia| exact HK|]. intros msx mox gx HR. apply KF. replace (c - 1)%nat with (0 + (c - 1))%nat by lia. exact HR.
  Qed.
End S.


End CeilWrap.
