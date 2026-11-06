(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut.
From Stdlib Require Lia. Unset Lia Cache.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV A0_cmp_msV A0_cmp_cbV.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

Section A0HCB.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (P STRM : Z).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx).
  (* [comment removed for export] *)
  Hypothesis ESTRM : STRM = (c_bz cx + BZF_STRM)%Z.
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis CX : cctx_ok cx.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z. Hypothesis PLO : (CEILv <= P)%Z. Hypothesis PHI : (P + 304 <= 18446744073709551616)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80.
  Definition ci_adv_W : list (Z * Z) := [(E + 16, E + 20); (STRM, STRM + 20)]%Z.

  Lemma A0_ci_adv : forall g e1 z (rest : list Z) (ni : Z) (me m : word -> option byte)
      (ra t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 : word),
    (1 <= z_avail_in z < 2147483648)%Z -> e_avail_in_expect e1 = z_avail_in z -> g_aie g = true -> (0 <= e_nblock e1 < 2147483648)%Z ->
    (0 < ni)%Z -> (ni + 1 < 18446744073709551616)%Z ->
    rw_cells a0segs m E (EHEAD1 cx g e1) -> rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) -> mem_inv a0segs m ->
    munch ci_adv_W me m -> wmono a0segs me m -> frdW a0segs ci_adv_W me (P + 120) [C8 (Z_to_bv 64 (E + 112))] ->
    shzW a0segs ci_adv_W me E (E + ESTATE_SIZE) -> shzW a0segs ci_adv_W me STRM (STRM + 80) ->
    (forall m' (y10 y11 y12 y14 : word),
        (NBLOCKMAX <= e_nblock e1 \/ z_avail_in (z_adv z rest) = 0)%Z ->
        rw_cells a0segs m' E (EHEAD1 cx g (est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1))) ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr (z_adv z rest) (ni + 1) p1 p2) -> mem_inv a0segs m' -> munch ci_adv_W me m' -> wmono a0segs me m' ->
        evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) t1 t2 (Z_to_bv 64 E) cSB y10 y11 y12 (Z_to_bv 64 1) y14 a5 a6 (Z_to_bv 64 (E + 108))
                              s2 s3 s4 s5 (Z_to_bv 64 (SHE + 2)) s7 s8 (Z_to_bv 64 SHE) s10 s11 t3 t4 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                         F (Z_to_bv 64 0x83638) fc None m' (seg_rom a0segs))) ->
    (forall m' (y11 y13 y14 : word),
        (e_nblock e1 < NBLOCKMAX)%Z -> (z_avail_in (z_adv z rest) <> 0)%Z ->
        rw_cells a0segs m' E (EHEAD1 cx g (est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1))) ->
        rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr (z_adv z rest) (ni + 1) p1 p2) -> mem_inv a0segs m' -> munch ci_adv_W me m' -> wmono a0segs me m' ->
        evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) t1 t2 (Z_to_bv 64 E) cSB (Z_to_bv 64 STRM) y11 (Z_to_bv 64 (e_nblock e1)) y13 y14 a5 a6 (Z_to_bv 64 (E + 108))
                              s2 s3 s4 s5 (Z_to_bv 64 (SHE + 2)) s7 s8 (Z_to_bv 64 SHE) s10 s11 t3 t4 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                         F (Z_to_bv 64 0x83214) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) t1 t2 (Z_to_bv 64 E) cSB a0 a1 a2 a3 a4 a5 a6 (Z_to_bv 64 (E + 108))
                          s2 s3 s4 s5 (Z_to_bv 64 (SHE + 2)) s7 s8 (Z_to_bv 64 SHE) s10 s11 t3 t4 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                     F (Z_to_bv 64 0x833f0) fc None m (seg_rom a0segs)).
  Proof.
    intros g e1 z rest ni me m ra t1 t2 a0 a1 a2 a3 a4 a5 a6 s2 s3 s4 s5 s7 s8 s10 s11 t3 t4 AIN EXP GA NBR NI0 NI1 EH1 SM MI MU WM V120 SHe SHs KX KL.
    cb_ranges CX. unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs.
    unfold ci_adv_W in MU, SHe, SHs, V120.
    unfold EHEAD1 in EH1. rewrite GA, <- ESTRM in EH1. unfold STRMB in SM.
    set (zn := z_adv z rest) in *. set (en := est_set_modes e1 (e_mode e1) (e_state e1) (e_avail_in_expect e1 - 1)) in *.
    (* [comment removed for export] *)
    assert (TAIL : forall (mt : word -> option byte) (x10 x11 x12 x13 x14 : word),
      rw_cells a0segs mt E (EHEAD1 cx g e1) -> rw_cells a0segs mt STRM (STRMB cx ob on dbza dbzfr zn (ni + 1) p1 p2) -> mem_inv a0segs mt ->
      munch ci_adv_W me mt -> wmono a0segs me mt ->
      evt a0segs Q (MS (mkR ra (Z_to_bv 64 P) gp tp (Z_to_bv 64 (E + 16)) t1 t2 (Z_to_bv 64 E) cSB x10 x11 x12 x13 x14 a5 a6 (Z_to_bv 64 (E + 108))
                            s2 s3 s4 s5 (Z_to_bv 64 (SHE + 2)) s7 s8 (Z_to_bv 64 SHE) s10 s11 t3 t4 (Z_to_bv 64 (SHE + 13)) (Z_to_bv 64 (SHE + 14)))
                       F (Z_to_bv 64 0x8347c) fc None mt (seg_rom a0segs))).
    { clear EH1 SM MI MU WM. intros mt x10 x11 x12 x13 x14 EH1 SM MI MU WM. unfold ci_adv_W in MU.
      unfold EHEAD1 in EH1. rewrite GA, <- ESTRM in EH1. unfold STRMB in SM. subst zn. unfold z_adv in SM. cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi] in SM.
      (* [comment removed for export] *)
      arun_to 0x834a4%Z.
      reword_C4 EH1 3%nat (e_avail_in_expect e1 - 1)%Z. { rewrite EXP. now low32. }
      pose proof (V120 _ MU) as RO. wstep. clear RO.
      (* [comment removed for export] *)
      arun_to 0x834b0%Z. try rewrite (sx32_of_Z (e_nblock e1)) by lia. try rewrite (sx32_of_Z NBLOCKMAX) by (bz_params; lia).
      assert (EH1n : forall mm, rw_cells a0segs mm E
                [C8 (Z_to_bv 64 STRM); C4 (Z_to_bv 64 (e_mode e1)); C4 (Z_to_bv 64 (e_state e1)); C4 (Z_to_bv 64 (e_avail_in_expect e1 - 1)); C4 (jw4 (c_J cx) 20);
                 C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 (c_A2 cx)); C8 (Z_to_bv 64 (c_FT cx)); C4 (if g_sort g then Z_to_bv 64 (e_origPtr e1) else jw4 (c_J cx) 48); C4 (jw4 (c_J cx) 52);
                 C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 (c_A2 cx)); C8 (Z_to_bv 64 (c_A1 cx)); C8 (g_zbits g);
                 C4 (Z_to_bv 64 WORKFACTOR); C4 (Z_to_bv 64 (e_state_in_ch e1)); C4 (Z_to_bv 64 (e_state_in_len e1)); C4 (jw4 (c_J cx) 100); C4 (jw4 (c_J cx) 104);
                 C4 (Z_to_bv 64 (e_nblock e1)); C4 (Z_to_bv 64 NBLOCKMAX); C4 (Z_to_bv 64 (bw_numZ (e_bw e1))); C4 (Z_to_bv 64 (e_state_out_pos e1));
                 C4 (if g_mtf g then Z_to_bv 64 (e_nInUse e1) else jw4 (c_J cx) 124)] -> rw_cells a0segs mm E (EHEAD1 cx g en)).
      { intros mm H. unfold EHEAD1. subst en. cbn_est. cbn [est_set_modes]. rewrite GA, <- ESTRM. exact H. }
      wstep; if_cases Kf; zify_cond_z Kf.
      { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ _ _) end;
          [st_eq| left; lia| apply EH1n; exact EH1| unfold STRMB, z_adv; cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi]; exact SM| exact MI| unfold ci_adv_W; exact MU| exact WM]. }
      (* [comment removed for export] *)
      arun_to 0x834d8%Z. try rewrite (sx32_of_Z (z_avail_in z - 1)) by lia.
      wstep; if_cases Ka; zify_cond_z Ka.
      { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KX mm _ _ _ _) end;
          [st_eq| right; unfold z_adv; cbn [z_avail_in]; lia| apply EH1n; exact EH1| unfold STRMB, z_adv; cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi]; exact SM| exact MI| unfold ci_adv_W; exact MU| exact WM]. }
      (* [comment removed for export] *)
      arun_to 0x834e8%Z. try rewrite (sx32_of_Z (e_avail_in_expect e1 - 1)) by lia.
      wstep; if_cases Ke; zify_cond_z Ke; [exfalso; lia|].
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (KL mm _ _ _) end;
        [st_eq| lia| unfold z_adv; cbn [z_avail_in]; lia| apply EH1n; exact EH1| unfold STRMB, z_adv; cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi]; exact SM| exact MI| unfold ci_adv_W; exact MU| exact WM]. }
    (* [comment removed for export] *)
    arun_to 0x83458%Z.
    reword_C4 SM 2%nat (m32 (z_tin_lo z + 1))%Z. { rewrite low32_inc_sx32, m32_eq. symmetry. apply low32_mod. }
    replace (z_avail_in z + -1)%Z with (z_avail_in z - 1)%Z in SM by lia.
    wstep; if_cases Kc; zify_cond_z Kc.
    - assert (NC : (m32 (z_tin_lo z + 1) <> 0)%Z).
      { intros Hz. apply Kc. apply (proj2 (swrap32_mod64_zero_iff _)). rewrite inc_sx32_mod. exact Hz. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _) end;
        [st_eq| unfold EHEAD1; rewrite GA, <- ESTRM; exact EH1| unfold STRMB; subst zn; unfold z_adv; cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi]; rewrite (proj2 (Z.eqb_neq _ _) NC); exact SM| exact MI| unfold ci_adv_W; exact MU| exact WM].
    - assert (CA : (m32 (z_tin_lo z + 1) = 0)%Z).
      { apply (proj1 (swrap32_mod64_zero_iff _)) in Kc. rewrite inc_sx32_mod in Kc. exact Kc. }
      (* [comment removed for export] *)
      arun_to 0x8347c%Z.
      reword_C4 SM 3%nat (z_tin_hi z + 1)%Z. { first [rewrite low32_inc64_sx32 | rewrite low32_inc64_sx32_mod]. reflexivity. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _) end;
        [st_eq| unfold EHEAD1; rewrite GA, <- ESTRM; exact EH1| unfold STRMB; subst zn; unfold z_adv; cbn [z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi]; rewrite (proj2 (Z.eqb_eq _ _) CA); exact SM| exact MI| unfold ci_adv_W; exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0HCB.

End ACeilS1.
