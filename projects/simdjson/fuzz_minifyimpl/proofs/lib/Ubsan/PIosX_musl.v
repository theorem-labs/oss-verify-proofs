(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep StoreFast MonadX.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import F_fmt_fp_lib Stdio_pure Startup_kit.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Ubsan Require Import F_syscalls StdioFiles Stdio_kit F_stdout_write UImg PExitU_tac PIosX_iface PF_fwrite0 PF_fflushU.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

(* [comment removed for export] *)
Lemma munch_sub2 : forall (sp d D Fa : Z) m m', 0 <= d <= D ->
  munch [(sp - d, sp); (Fa, Fa + 232)] m m' -> munch [(sp - D, sp); (Fa, Fa + 232)] m m'.
Proof.
  intros sp d D Fa m m' Hd MU. eapply munch_weaken; [| exact MU]. unfold sub_fp. cbn [outside]. intros x (H1 & H2 & _). repeat split; lia.
Qed.

(* [comment removed for export] *)
Lemma ssp_cells_transport2 : forall (sp D Fa lo : Z) m m' guard,
  ssp_cells m guard -> munch [(sp - D, sp); (Fa, Fa + 232)] m m' -> wmono usegs m m' ->
  GLOBALS_TOP <= sp - D -> (Fa = RSTDOUT \/ Fa = RSTDERR) -> ssp_cells m' guard.
Proof.
  intros sp D Fa lo m m' guard [G1 G2] MU WM HS HF. unfold ssp_cells, got_ssp, ssp_guard, GLOBALS_TOP in *.
  split; (eapply rw_cells_transport; [eassumption | exact MU | exact WM |]; cbn [disjoint_from cells_size csize Nat.add]; destruct HF as [-> | ->]; repeat split; lia).
Qed.

(* [comment removed for export] *)
Lemma flags72_zx8 : forall flags : word, Z.land (bv_unsigned flags) 72 = 0 -> Z.land (bv_unsigned (zx32 flags)) 8 = 0.
Proof.
  intros flags H.
  assert (H8 : Z.land (bv_unsigned flags) 8 = 0).
  { apply Z.bits_inj'. intros i Hi. rewrite Z.land_spec, Z.bits_0.
    destruct (Z.eq_dec i 3) as [->|NE].
    - pose proof (f_equal (fun z => Z.testbit z 3) H) as T. cbn beta in T. rewrite Z.land_spec, Z.bits_0 in T.
      change (Z.testbit 72 3) with true in T. change (Z.testbit 8 3) with true. exact T.
    - change 8 with (2^3). rewrite Z.pow2_bits_eqb by lia. destruct (Z.eqb_spec 3 i); [lia|]. apply Bool.andb_false_r. }
  unfold zx32. rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with (2^64).
  rewrite Z.mod_small.
  - rewrite <- Z.land_ones by lia. rewrite <- Z.land_assoc. change (Z.land (Z.ones 32) 8) with 8. exact H8.
  - pose proof (Z.mod_pos_bound (bv_unsigned flags) (2^32) ltac:(lia)). lia.
Qed.

(* [comment removed for export] *)
Lemma implM_rdso_inv_nil : forall (so_x : stdout_st) {B : list Z} (Q : unit -> stdout_st -> machine_state -> Prop) ms,
  so_buf so_x = B -> B = [] ->
  implM usegs (so <- rd_so (fun so => so) ;; if 0 <? zlength (so_buf so) then stdout_writefn (fun so => so) (fun so _ => so) [] else mret tt) so_x Q ms ->
  evt usegs (Q tt so_x) ms.
Proof.
  intros so_x B Q ms E1 E2 H. subst B. unfold implM, rd_so, mbind, mget, mret in H. cbn in H. rewrite E2 in H. cbn in H. exact H.
Qed.

Section Out.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  (* [comment removed for export] *)
  Lemma fout_same :
    forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St),
      stk usegs m lo (bv_unsigned sp) -> stdout_file m (get_so s) ->
      ssp_cells m guard -> mem_inv usegs m ->
      a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
      lo <= bv_unsigned sp - 512 -> GLOBALS_TOP <= lo -> bv_unsigned sp < 2^47 ->
      implM usegs (stdout_exit_flush get_so set_so) s
             (fflush_out_post set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
             (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                 F (Z_to_bv 64 PFFLUSH) fc None m (seg_rom usegs)).
  Proof.
    intros until s. intros ST SOF [GS GU] MI A0 TP LO GLO SP47.
    pose proof SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
    eapply implM_mono.
    - eapply (fflush_stdout_spec get_so set_so get_set set_set set_get) with (lo := lo) (guard := guard);
        first [ exact ST | exact SOF | exact GS | exact GU | exact MI | exact A0 | exact GLO | exact SP47 | (clear - LO; lia) ].
    - cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & so' & flags2 & mode2 & tail2 & m2
                       & -> & MU2 & WM2 & MI2 & ST2 & -> & EB2 & FC2 & FL2 & SSP2).
      unfold fflush_out_post, icpt_post.
      exists so'. split; [reflexivity|]. split; [exact EB2|].
      do 15 eexists. split; [reflexivity|].
      split; [eapply (munch_sub2 _ 176 512); [clear; lia | exact MU2]|].
      split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|]. split; [exact SSP2|].
      exists flags2, mode2, tail2, bufbytes. cbn [so_inact so_active so_buf so_first so_lbf_nl]. unfold file_cells, wfn_of, lbf_of in *.
      split; [exact FC2|]. split; [exact FL2|].
      split. { eapply rw_cells_transport; [exact BUF | exact MU2 | exact WM2 |]. unfold GLOBALS_TOP in GLO. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
      split; [reflexivity|]. split; [unfold zlength; cbn; lia| reflexivity].
  Qed.

End Out.

(* [comment removed for export] *)
Section OutStmt.
  Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
  Hypothesis get_set : forall s so, get_so (set_so so s) = so.
  Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
  Hypothesis set_get : forall s, set_so (get_so s) s = s.

  Theorem fflush_out_proof : fflush_out_stmt get_so set_so.
  Proof.
    unfold fflush_out_stmt. intros until so_x. intros ST SOF EB ENE EF EL SSP MI A0 TP LO GLO SP47.
    destruct (so_buf (get_so s)) as [|c0 cs] eqn:EBUF.
    - (* [comment removed for export] *)
      pose proof (fout_same (St := stdout_st) (fun so => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)
                    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo guard so_x
                    ST SOF SSP MI A0 TP LO GLO SP47) as G.
      unfold stdout_exit_flush in G |- *. apply (implM_rdso usegs get_so). rewrite EBUF.
      change (0 <? zlength (@nil Z)) with false. cbv iota.
      apply implM_ret.
      apply (implM_rdso_inv_nil so_x (B := []) _ _ EB eq_refl) in G.
      eapply evt_mono; [exact G|]. cbv beta. intros ms' (so' & E1 & E2 & PO). cbn beta in E1.
      exists (get_so s). split; [symmetry; apply set_get|]. split; [exact EBUF|].
      replace (so_inact (get_so s)) with (so_inact so'); [exact PO|].
      subst so'. unfold so_inact. rewrite EF, EL. reflexivity.
    - (* [comment removed for export] *)
      assert (EX : so_x = get_so s) by (apply ENE; discriminate). subst so_x.
      eapply fout_same; eassumption.
  Qed.
End OutStmt.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Theorem fflush_err_proof : fflush_err_stmt.
Proof.
  unfold fflush_err_stmt. intros until guard. intros ST SEF SSP MI A0 LO GLO.
  eapply evt_mono.
  - eapply fflush_stderr_spec with (lo := lo); first [ exact ST | exact SEF | exact MI | exact A0 | exact GLO | (clear - LO; lia) ].
  - cbv beta. intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2 & SEF2).
    unfold icpt_post. do 15 eexists. split; [reflexivity|].
    split; [eapply (munch_sub2 _ 32 512); [clear; lia | exact MU2]|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [| exact SEF2].
    eapply (ssp_cells_transport2 (bv_unsigned sp) 32 RSTDERR lo); [exact SSP | exact MU2 | exact WM2 | clear - LO GLO; lia | right; reflexivity].
Qed.

Theorem fwrite0_err_proof : fwrite0_err_stmt.
Proof.
  unfold fwrite0_err_stmt. intros until guard. intros ST SEF SSP MI A1 A2 A3 LO GLO.
  destruct SEF as (eflags & emode & ee & ewend & etail & EFC).
  eapply evt_mono.
  - eapply (fwrite0_musl_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo RSTDERR);
      first [ exact EFC | exact ST | exact MI | exact A1 | exact A2 | exact A3 | exact GLO | (right; reflexivity) | (clear - LO; lia) ].
  - cbv beta. intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & fl' & md' & wend' & wpos' & wbase' & m2
                          & -> & MU2 & WM2 & MI2 & ST2 & FC2 & CS).
    unfold icpt_post. do 15 eexists. split; [reflexivity|].
    split; [eapply (munch_sub2 _ 256 512); [clear; lia | exact MU2]|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [eapply (ssp_cells_transport2 (bv_unsigned sp) 256 RSTDERR lo); [exact SSP | exact MU2 | exact WM2 | clear - LO GLO; lia | right; reflexivity]|].
    destruct CS as [(_ & -> & -> & -> & -> & ->)|[(_ & -> & -> & -> & ->)|(_ & _ & -> & -> & ->)]].
    all: unfold stderr_file; do 5 eexists; eassumption.
Qed.

Theorem fwrite0_out_proof : fwrite0_out_stmt.
Proof.
  unfold fwrite0_out_stmt. intros until so_x. intros ST SOF SSP MI A1 A2 A3 LO GLO.
  destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
  eapply evt_mono.
  - eapply (fwrite0_musl_spec ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo RSTDOUT);
      first [ exact FC | exact ST | exact MI | exact A1 | exact A2 | exact A3 | exact GLO | (left; reflexivity) | (clear - LO; lia) ].
  - cbv beta. intros ms' (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & fl' & md' & wend' & wpos' & wbase' & m2
                          & -> & MU2 & WM2 & MI2 & ST2 & FC2 & CS).
    assert (BUF2 : rw_cells usegs m2 RSTDOUT_BUF [CB 1024 bufbytes]).
    { eapply rw_cells_transport; [exact BUF | exact MU2 | exact WM2 |]. unfold GLOBALS_TOP in GLO. cbn [disjoint_from cells_size csize Nat.add]. repeat split; lia. }
    unfold icpt_post. do 15 eexists. split; [reflexivity|].
    split; [eapply (munch_sub2 _ 256 512); [clear; lia | exact MU2]|].
    split; [exact WM2|]. split; [exact MI2|]. split; [exact ST2|].
    split; [eapply (ssp_cells_transport2 (bv_unsigned sp) 256 RSTDOUT lo); [exact SSP | exact MU2 | exact WM2 | clear - LO GLO; lia | left; reflexivity]|].
    destruct CS as [(NZ & -> & -> & -> & -> & ->)|[(ZW & -> & -> & -> & ->)|(_ & NOWR & _)]].
    + (* [comment removed for export] *)
      destruct (so_active so_x) eqn:EA; [| exfalso; apply NZ; reflexivity].
      exists flags, mode, tail, bufbytes. cbn [so_act so_active so_buf so_lbf_nl so_first].
      split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF2|]. split; [exact BUFP|]. split; [exact BUFL|]. intros X; discriminate X.
    + (* [comment removed for export] *)
      destruct (so_active so_x) eqn:EA; [exfalso; cbv in ZW; discriminate ZW|].
      pose proof (INACT eq_refl) as EB.
      exists flags. eexists. exists tail, bufbytes. cbn [so_act so_active so_buf so_lbf_nl so_first]. rewrite EB in *.
      change (zlength (@nil Z)) with 0. rewrite Z.add_0_r.
      split; [exact FC2|]. split; [exact FL72|]. split; [exact BUF2|]. split; [exact BUFP|]. split; [exact BUFL|]. intros X; discriminate X.
    + exfalso. apply NOWR. apply flags72_zx8. exact FL72.
Qed.

(* [comment removed for export] *)
Theorem wcrtomb0_proof : wcrtomb0_stmt.
Proof.
  unfold wcrtomb0_stmt. intros until jb. intros ST PC PLO PHI MI -> -> GLO LO SP47.
  pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP. unfold GLOBALS_TOP in GLO.
  pose proof (munch_refl [(P, P + 1)]%Z m) as MU. pose proof (wmono_refl usegs m) as WM.
  assert (EP : bv_unsigned (Z_to_bv 64 P) = P) by (apply unsigned_lit; clear - PLO PHI RSP SP47 GLO LO; lia).
  unfold PWCRTOMB.
  zstep. zstep. if_cases K; zify_cond K. { exfalso. clear - K PLO GLO LO. lia. } clear K.
  zstep. zstep. first [if_lit | if_true | if_false].
  rewrite ?EP. zstep. zstep. zstep.
  apply evt_done. unfold wcr_post. do 14 eexists. eexists.
  split; [cbv delta [mkR]; reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [assumption|]. assumption.
Qed.
