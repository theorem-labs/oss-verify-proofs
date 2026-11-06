(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Lib Require Import Tac ITree Nodes Decode SysStep ZBridge Cells InitMem.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Spec Require Import Prelim Monad Stdio.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.LibA Require Import Shadow ITreeA StepF StrwF.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AImg RtCells ShadowTac F_syscalls StdioFiles Stdio_kit MonadF I_fwrite F_stdout_write AExitU_wr AIos_iface.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.AsanW Require Import AIcptU_hmap AIcptU_fflush AIcptU_defs F_fflushU.
From OSSVerify.Proofs.simdjson.fuzz_minifyimpl.lib.Common Require Import RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Local Ltac transport_chunks segs m a bs ::= transport_chunks_fast segs m a bs.
Local Ltac footprint_after_store segs m a bs ::= footprint_after_store_fast segs m a bs.
Local Ltac mem_after_store ::= mem_after_store_fast.
Local Ltac transport_after_call segs m m' MU WM ::= transport_after_call_fast segs m m' MU WM.

Section CANSEC1. Context {rc : runConstT}.
Section Chains.
  Variables (T SLO SHI : Z).
  (* [comment removed for export] *)
  Lemma implAM_rdso_inv_nil : forall (so_x : stdout_st) {B : list Z} RNG (Q : unit -> stdout_st -> machine_state -> Prop) ms,
    so_buf so_x = B -> B = [] ->
    implAM RNG (so <- rd_so (fun so => so) ;; if 0 <? zlength (so_buf so) then stdout_writefn (fun so => so) (fun so _ => so) [] else mret tt) so_x Q ms ->
    evtF asegs RNG (Q tt so_x) ms.
  Proof.
    intros so_x B RNG Q ms E1 E2 H. subst B. unfold implAM, rd_so, mbind, mget, mret in H. cbn in H. rewrite E2 in H. cbn in H.
    eapply evtF_mono; [exact H|]. cbv beta. intros ms' [_ HQ]. exact HQ.
  Qed.

  Section Out.
    Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Hypothesis get_set : forall s so, get_so (set_so so s) = so.
    Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
    Hypothesis set_get : forall s, set_so (get_so s) s = s.

    (* [comment removed for export] *)
    Lemma fout_same :
      forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St),
        stk asegs m lo (bv_unsigned sp) -> stdout_file m (get_so s) ->
        ssp_cells m guard -> icptU T m -> mem_inv asegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
        rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> icptU_rng T RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
        implAM RNG (stdout_exit_flush get_so set_so) s
               (fflush_out_post (icptU T) set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom asegs)).
    Proof.
      intros until s. intros ST SOF [GS GU] IC MI -> -> LO GLO ALO SP16 RSTK RI [RBE RBO] RG0 SP47.
      pose proof IC as ((R1 & R2 & R3 & R4 & R5 & R6) & (M1 & M2 & B1 & B2 & TLO & THI & TAL)).
      unfold HMAP, BOFF_ERR, BOFF_OUT in *.
      destruct SOF as (flags & mode & tail & bufbytes & FC & FL72 & BUF & BUFP & BUFL & INACT).
      pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. change (2 ^ Z.of_N 64) with (2^64) in SPR.
      pose proof (munch_refl [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232); (T + 1354800, T + 1354800 + 8)]%Z m) as MU.
      pose proof (wmono_refl asegs m) as WM.
      pose proof (fun m' H' => rw_cells_same_bytes m m' (T + 1354800) hm_bucket0 B2 H' ltac:(lia)) as SAME.
      unfold FFLUSH_STUB. unfold hm_bucket0 in B1, B2. unfold file_cells in FC. unfold got_ssp, ssp_guard in GS, GU.
      pose proof GLO as GLO'. unfold GLOBALS_TOP in GLO'.
      (* [comment removed for export] *)
      eapply implAM_evt; [eapply (fflush_i_pre RNG); iprem|].
      lazymatch goal with MIh : mem_inv asegs ?mm |- forall _, _ => post_call asegs mm end.
      replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) in * by lia.
      (* [comment removed for export] *)
      name_sp sp (-80)%Z.
      eapply implAM_post_evt'.
      { eapply (fflush_stdout_spec get_so set_so get_set set_set set_get RNG) with (lo := lo) (guard := guard); rewrite ?Hsp.
        all: lazymatch goal with
             | |- stdout_file _ _ => exists flags, mode, tail, bufbytes; unfold file_cells; split; [exact FC|]; split; [exact FL72|]; split; [exact BUF|]; split; [exact BUFP|]; split; [exact BUFL| exact INACT]
             | |- @eq word _ _ => reflexivity
             | |- rw_cells _ _ _ _ => unfold got_ssp, ssp_guard; eassumption
             | |- rng0 _ => exact RG0
             | |- _ => unfold GLOBALS_TOP; iprem
             end. }
      cbv beta. intros [] st2 ms2 PO2.
      destruct PO2 as (u0 & u1 & u2 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & so' & flags2 & mode2 & tail2 & m2
                       & -> & MU2 & WM2 & MI2 & ST2 & -> & EB2 & FC2 & FL2 & [GS2 GU2]).
      unfold file_cells in FC2. unfold got_ssp, ssp_guard in GS2, GU2.
      lazymatch type of MU2 with munch _ ?mm _ => transport_after_call asegs mm m2 MU2 WM2 end. clear MU2 WM2.
      unname_sp.
      replace (ret_pc (Z_to_bv 64 475120)) with (Z_to_bv 64 475120 : word) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
      (* [comment removed for export] *)
      eapply evtF_cut; [eapply (fflush_i_post RNG) with (lo := lo) (T := T) (addr := 0x16ba20) (boff := 1354800)|].
      all: lazymatch goal with
           | |- forall _, _ => idtac
           | |- _ \/ _ => left; split; reflexivity
           | |- rw_cells _ _ _ hm_bucket0 => unfold hm_bucket0; eassumption
           | |- rw_cells _ _ _ _ => unfold HMAP; first [eassumption | (replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; eassumption)]
           | |- stk _ _ _ _ => replace (bv_unsigned sp - 80) with (bv_unsigned sp + -80) by lia; eassumption
           | |- mem_inv _ _ => exact MI2
           | |- _ => unfold KHIGH in *; atop_facts; iprem
           end.
      post_call asegs m2.
      apply evtF_done. unfold fflush_out_post, icpt_post.
      exists so'. split; [reflexivity|]. split; [exact EB2|].
      do 15 eexists. split; [reflexivity|].
      split. { eapply (munch_drop_eq [(bv_unsigned sp - 4096, bv_unsigned sp); (RSTDOUT, RSTDOUT + 232)]%Z (T + 1354800) 8); [exact MU|].
               intros xx Hx _. lazymatch goal with BK : rw_cells asegs ?mm (T + 1354800) hm_bucket0 |- ?mm _ = _ => apply (SAME _ BK) end.
               unfold hm_bucket0. cbn [cells_size csize Nat.add]. lia. }
      split; [exact WM|]. split; [assumption|]. split; [assumption|].
      split. { unfold ssp_cells, got_ssp, ssp_guard. split; assumption. }
      split. { unfold icptU, icpt_rt, icpt_tab, HMAP, BOFF_ERR, BOFF_OUT.
               lazymatch goal with BK : rw_cells asegs _ (T + 1354800) hm_bucket0 |- _ => unfold hm_bucket0 in BK |- * end.
               repeat match goal with |- _ /\ _ => split end; assumption. }
      exists flags2, mode2, tail2, bufbytes. cbn [so_inact so_active so_buf so_first so_lbf_nl]. unfold file_cells, wfn_of, lbf_of in *.
      split; [exact FC2|]. split; [exact FL2|]. split; [exact BUF|]. split; [reflexivity|]. split; [unfold zlength; cbn; lia| reflexivity].
    Qed.
  End Out.

  (* [comment removed for export] *)
  Section OutStmt.
    Context {St : Type} (get_so : St -> stdout_st) (set_so : stdout_st -> St -> St).
    Hypothesis get_set : forall s so, get_so (set_so so s) = so.
    Hypothesis set_set : forall s so so', set_so so' (set_so so s) = set_so so' s.
    Hypothesis set_get : forall s, set_so (get_so s) s = s.

    Theorem fflush_out_proof :
      forall RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z) (guard : word) (s : St) (so_x : stdout_st),
        stk asegs m lo (bv_unsigned sp) -> stdout_file m so_x ->
        so_buf so_x = so_buf (get_so s) -> (so_buf (get_so s) <> [] -> so_x = get_so s) ->
        so_first so_x = so_first (get_so s) -> so_lbf_nl so_x = so_lbf_nl (get_so s) ->          (* [comment removed for export] *)
        ssp_cells m guard -> icptU T m -> mem_inv asegs m ->
        a0 = Z_to_bv 64 RSTDOUT -> tp = Z_to_bv 64 RTP ->
        lo <= bv_unsigned sp - 4096 -> GLOBALS_TOP <= lo -> ATOP <= lo -> bv_unsigned sp mod 16 = 0 ->
        rng RNG lo (bv_unsigned sp - lo) -> rng_aimg RNG -> icptU_rng T RNG -> rng0 RNG -> bv_unsigned sp < 2^47 ->
        implAM RNG (stdout_exit_flush get_so set_so) s
               (fflush_out_post (icptU T) set_so ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo guard m s)
               (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                   F (Z_to_bv 64 FFLUSH_STUB) fc None m (seg_rom asegs)).
    Proof.
      intros until so_x. intros ST SOF EB ENE EF EL SSP IC MI A0 TP LO GLO ALO SP16 RSTK RI RB RG0 SP47.
      destruct (so_buf (get_so s)) as [|c0 cs] eqn:EBUF.
      - (* [comment removed for export] *)
        pose proof (fout_same (St := stdout_st) (fun so => so) (fun so _ => so) (fun _ _ => eq_refl) (fun _ _ _ => eq_refl) (fun _ => eq_refl)
                      RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m lo guard so_x
                      ST SOF SSP IC MI A0 TP LO GLO ALO SP16 RSTK RI RB RG0 SP47) as G.
        unfold stdout_exit_flush in G |- *. apply (implAM_rdso get_so). rewrite EBUF.
        change (0 <? zlength (@nil Z)) with false. cbv iota.
        apply implAM_ret.
        apply (implAM_rdso_inv_nil so_x (B := []) _ _ _ EB eq_refl) in G.
        eapply evtF_mono; [exact G|]. cbv beta. intros ms' (so' & E1 & E2 & PO). cbn beta in E1.
        exists (get_so s). split; [symmetry; apply set_get|]. split; [exact EBUF|].
        replace (so_inact (get_so s)) with (so_inact so'); [exact PO|].
        subst so'. unfold so_inact. rewrite EF, EL. reflexivity.
      - (* [comment removed for export] *)
        assert (EX : so_x = get_so s) by (apply ENE; discriminate). subst so_x.
        eapply fout_same; eassumption.
    Qed.
  End OutStmt.
End Chains.
End CANSEC1.
