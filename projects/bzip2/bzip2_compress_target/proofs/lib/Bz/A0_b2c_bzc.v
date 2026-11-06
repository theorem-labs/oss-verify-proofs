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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpSess CmpSessB CmpSess2 CmpSdTac CmpFsKit0 AsanKit AsanCut.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Ltac lit_store :=
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 8 ?v)) _) => change (Z_to_le_bytes 8 v) with (le8 (Z_to_bv 64 v)); mem_after_store
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (Z_to_le_bytes 4 ?v)) _) => change (Z_to_le_bytes 4 v) with (le4 (Z_to_bv 64 v)); mem_after_store
  | _ => idtac
  end.
Ltac split_at_cb8 cs :=
  lazymatch cs with
  | CB 8 ?bs :: ?post => constr:((@nil cell, bs, post))
  | ?c :: ?rest => let r := split_at_cb8 rest in lazymatch r with (?pre, ?bs, ?post) => constr:((c :: pre, bs, post)) end
  end.
Ltac cb8_all H :=
  repeat (lazymatch type of H with rw_cells ?segs ?m ?A ?cs =>
            let r := split_at_cb8 cs in
            lazymatch r with (?pre, ?bs, ?post) => apply (rw_cells_CB8_C8 segs m A pre bs post) in H; cbn [app] in H end end).
(* [comment removed for export] *)

Section A0BZC.
  Variable X : cbenv. Variable Q : machine_state -> Prop.
  Variables (SHE SHS : Z) (ob on dbza dbzfr nin : Z) (p1 p2 : word).
  Hypothesis XOK : cbenv_ok X.
  Notation cx := (ce_cx X).
  Notation usp := (bv_unsigned (ce_sp X)). Notation E := (c_E cx). Notation STRM := (c_bz cx + BZF_STRM)%Z.
  Notation gp := (ce_gp X). Notation tp := (ce_tp X). Notation F := (ce_F X). Notation fc := (ce_fc X). Notation lo := (ce_lo X).
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80.
  (* [comment removed for export] *)
  Definition BSAVED : list cell :=
    [C8 (ce_s8 X); C8 (ce_s7 X); C8 (ce_s6 X); C8 (ce_s5 X); C8 (ce_s4 X); C8 (ce_s3 X); C8 (ce_s2 X); C8 (ce_s1 X); C8 (ce_s0 X); C8 (ce_ra X)].
  Definition bzcA_W : list (Z * Z) := [(E + 8, E + 20); (usp - 80, usp)]%Z.
  (* [comment removed for export] *)
  Notation RBZ ra t0 t1 t2 s0 a0 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 :=
    (mkR ra (Z_to_bv 64 (usp - 80)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (E + 8)) a0 a1 a2 a3 a4 a5 a6 a7
         (Z_to_bv 64 E) (Z_to_bv 64 (E + 16)) (Z_to_bv 64 (SHE + 1)) cSB s6 s7 (Z_to_bv 64 (SHE + 2)) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3 t4 t5 t6).

  Lemma A0_bzc_A : forall (g0 : eg) (e0 : est) (z0 : zstrm) (m : word -> option byte) (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word),
    e_mode e0 = BZ_M_RUNNING -> (0 <= z_avail_in z0 < 2147483648)%Z ->
    rw_cells a0segs m E (EHEAD1 cx g0 e0) -> rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z0 nin p1 p2) ->
    mem_inv a0segs m -> stk a0segs m lo usp -> aconsts A0C m ->
    shzW a0segs bzcA_W m E (E + ESTATE_SIZE) -> shzW a0segs bzcA_W m STRM (STRM + 80) ->
    (forall m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31 : word),
       rw_cells a0segs m' E (EHEAD1 cx (eg_set_aie g0) (e_finish e0 z0)) -> rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z0 nin p1 p2) ->
       rw_cells a0segs m' (usp - 80) BSAVED -> stk a0segs m' lo (usp - 80) -> mem_inv a0segs m' -> munch bzcA_W m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (RBZ (Z_to_bv 64 0x82614) y5 y6 y7 (Z_to_bv 64 (-1)) (Z_to_bv 64 STRM) y11 y12 y13 y14 y15 y16 y17 y22 y23 y28 y29 y30 y31)
                        F (Z_to_bv 64 0x828cc) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR (ce_ra X) (ce_sp X) gp tp t0 t1 t2 (ce_s0 X) (ce_s1 X) (Z_to_bv 64 STRM) (Z_to_bv 64 BZ_FINISH) a2 a3 a4 a5 a6 a7
                          (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82468) fc None m (seg_rom a0segs)).
  Proof.
    intros g0 e0 z0 m t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 MR AVR EH1 SM MI ST AC SHe SHs K.
    cbenv_open XOK. cb_ranges CX. clear SEP.
    destruct AC as [GOT SBV]. cbn [aci_segs aci_c aci_got_sh aci_shvar A0C ci_segs] in GOT, SBV.
    unfold CEILv, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (munch_refl bzcA_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold bzcA_W in MU, SHe, SHs.
    unfold EHEAD1 in EH1. unfold STRMB in SM. unfold BZ_M_RUNNING in MR. rewrite MR in EH1. unfold BZ_FINISH.
    carve_frame 80%nat ST.
    apply (rw_cells_split_CB a0segs _ _ [] 80 _ [] [8;8;8;8;8;8;8;8;8;8]%nat) in FR; [| reflexivity].
    cbn [mk_CB_cells app] in FR.
    replace (usp + -80)%Z with (usp - 80)%Z in * by lia.
    (* [comment removed for export] *)
    wstep. replace (Z_to_bv 64 (usp + -80)) with (Z_to_bv 64 (usp - 80)) by (f_equal; lia).
    do 10 wstep. wstep.
    wstep; if_cases KZ; zify_cond_z KZ; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x824c0%Z.
    wstep; if_cases KS; zify_cond_z KS; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x824d8%Z.
    wstep; if_cases KE; zify_cond_z KE; [|exfalso; lia].
    (* [comment removed for export] *)
    arun; if_cases K9; zify_cond_z K9; [exfalso; lia|].
    (* [comment removed for export] *)
    wstep. repeat sh_norm.
    cb8_all FR.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
      [st_eq| unfold EHEAD1, e_finish, eg_set_aie; cbn_est; cbn [g_aie g_sort g_mtf g_bs g_zbits est_set_modes]; unfold BZ_M_FINISHING; exact EH1| unfold STRMB; exact SM
      | unfold BSAVED; exact FR| exact ST| exact MI| unfold bzcA_W; exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
  Lemma stk_join8 : forall segs m a b b' c, stk segs m a b -> stk segs m b' c -> b = b' -> (a <= b <= c)%Z -> stk segs m a c.
  Proof. intros segs m a b b' c H1 H2 -> Hle. eapply stk_merge; [exact H1| exact H2| exact Hle]. Qed.

  Definition bzcB_W : list (Z * Z) := [(E + 8, E + 12)]%Z.
  Lemma A0_bzc_B : forall (g' : eg) (e' e'' : est) (z' z'' : zstrm) (pr : bool) (ret : Z) (m : word -> option byte)
      (ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 : word),
    bzc_finish_tail e' z' pr = (ret, e'', z'') ->
    est_ok e' -> g_aie g' = true -> (0 <= e_avail_in_expect e' < 2147483648)%Z -> (bw_numZ (e_bw e') < 2147483648)%Z ->
    rw_cells a0segs m E (EHEAD1 cx g' e') -> rw_cells a0segs m (usp - 80) BSAVED -> stk a0segs m lo (usp - 80) -> mem_inv a0segs m ->
    shzW a0segs bzcB_W m E (E + ESTATE_SIZE) ->
    (forall m' (y5 y6 y7 y11 y12 y13 y14 y15 y16 y17 y28 y29 y30 y31 : word),
       rw_cells a0segs m' E (EHEAD1 cx g' e'') -> stk a0segs m' lo usp -> mem_inv a0segs m' -> munch bzcB_W m m' -> wmono a0segs m m' ->
       evt a0segs Q (MS (mkR (ce_ra X) (ce_sp X) gp tp y5 y6 y7 (ce_s0 X) (ce_s1 X) (Z_to_bv 64 ret) y11 y12 y13 y14 y15 y16 y17
                             (ce_s2 X) (ce_s3 X) (ce_s4 X) (ce_s5 X) (ce_s6 X) (ce_s7 X) (ce_s8 X) (ce_s9 X) (ce_s10 X) (ce_s11 X) y28 y29 y30 y31)
                        F (ret_pc (ce_ra X)) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RBZ ra t0 t1 t2 (Z_to_bv 64 (-1)) (Z_to_bv 64 (Z.b2z pr)) a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82614) fc None m (seg_rom a0segs)).
  Proof.
    intros g' e' e'' z' z'' pr ret m ra t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 s6 s7 t3 t4 t5 t6 RES EOK GA AIR NZR EH1 SAV ST MI SHe K.
    cbenv_open XOK. cb_ranges CX. clear SEP.
    unfold est_ok in EOK. cps_destruct EOK as (_ & _ & _ & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & _ & _ & _).
    pose proof (munch_refl bzcB_W m) as MU. pose proof (wmono_refl a0segs m) as WM. unfold bzcB_W, ESTATE_SIZE in MU, SHe.
    unfold BSAVED in SAV.
    (* [comment removed for export] *)
    assert (EXIT : forall (mx : word -> option byte) (x1 x5 x6 x7 x8' x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      rw_cells a0segs mx E (EHEAD1 cx g' e'') -> rw_cells a0segs mx (usp - 80) BSAVED -> stk a0segs mx lo (usp - 80) -> mem_inv a0segs mx ->
      munch bzcB_W m mx -> wmono a0segs m mx ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 ret) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (ce_s9 X) (ce_s10 X) (ce_s11 X) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x824dc) fc None mx (seg_rom a0segs))).
    { clear EH1 SAV ST MI MU WM. intros mx x1 x5 x6 x7 x8' x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 EH1 SAV ST MI MU WM.
      unfold BSAVED in SAV.
      wstep. do 10 wstep. wstep.
      pose proof (stk_of_rw_cells a0segs _ _ _ SAV) as K5. cbn [cells_size csize Nat.add] in K5. change (Z.of_nat 80) with 80%Z in K5.
      pose proof (stk_join8 a0segs _ lo _ _ _ ST K5 eq_refl ltac:(lia)) as ST'. replace (usp - 80 + 80)%Z with usp in ST' by lia.
      replace (Z_to_bv 64 (usp - 80 + 80)) with (ce_sp X) by (rewrite <- (Z_to_bv_bv_unsigned (ce_sp X)) at 1; f_equal; lia).
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [st_eq| exact EH1| exact ST'| exact MI| unfold bzcB_W; exact MU| exact WM]. }
    unfold bzc_finish_tail in RES.
    Ltac xside := let EH1 := ident:(EH1) in let SAV := ident:(SAV) in let ST := ident:(ST) in let MI := ident:(MI) in let MU := ident:(MU) in let WM := ident:(WM) in let GA := ident:(GA) in
      first [exact SAV | exact ST | exact MI | exact MU | exact WM | (unfold BSAVED; exact SAV) | (unfold EHEAD1; rewrite GA; exact EH1)].
    unfold EHEAD1 in EH1. rewrite GA in EH1.
    destruct pr; cbn [Z.b2z negb] in *.
    2:{ (* [comment removed for export] *)
        wstep; if_cases KP; zify_cond_z KP; [|exfalso; lia].
        inversion RES; subst ret e'' z''.
        lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (EXIT mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [unfold BZ_SEQUENCE_ERROR; st_eq| ..]; xside. }
    wstep; if_cases KP; zify_cond_z KP; [exfalso; lia|].
    (* [comment removed for export] *)
    arun_to 0x82628%Z. try rewrite (sx32_of_Z (e_avail_in_expect e')) by lia.
    wstep; if_cases KA; zify_cond_z KA.
    { (* [comment removed for export] *)
      replace (0 <? e_avail_in_expect e')%Z with true in RES by (symmetry; apply Z.ltb_lt; lia). cbn [orb] in RES.
      inversion RES; subst ret e'' z''.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (EXIT mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [unfold BZ_FINISH_OK; st_eq| ..]; xside. }
    replace (0 <? e_avail_in_expect e')%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in RES.
    unfold isempty_RL_e, isempty_RL, est_rl in RES. cbn [rl_ch rl_len] in RES. rewrite Bool.negb_involutive in RES.
    (* [comment removed for export] *)
    arun_to 0x82648%Z. try rewrite (sx32_of_Z (e_state_in_ch e')) by lia.
    assert (FOK : forall (mx : word -> option byte) (x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 : word),
      ((e_state_in_ch e' <? 256) && (0 <? e_state_in_len e') || (e_state_out_pos e' <? bw_numZ (e_bw e')) = true)%Z%bool ->
      rw_cells a0segs mx E (EHEAD1 cx g' e') -> rw_cells a0segs mx (usp - 80) BSAVED -> stk a0segs mx lo (usp - 80) -> mem_inv a0segs mx ->
      munch bzcB_W m mx -> wmono a0segs m mx ->
      evt a0segs Q (MS (mkR x1 (Z_to_bv 64 (usp - 80)) gp tp x5 x6 x7 (Z_to_bv 64 3) x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 (ce_s9 X) (ce_s10 X) (ce_s11 X) x28 x29 x30 x31)
                       F (Z_to_bv 64 0x824dc) fc None mx (seg_rom a0segs))).
    { intros mx x1 x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 x23 x24 x28 x29 x30 x31 CND EH1' SAV' ST' MI' MU' WM'.
      rewrite CND in RES. inversion RES; subst ret e'' z''.
      enter_with (EXIT mx _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ EH1' SAV' ST' MI' MU' WM'). unfold BZ_FINISH_OK. st_eq. }
    (* [comment removed for export] *)
    assert (JN : forall (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 : word),
      ((e_state_in_ch e' <? 256) && (0 <? e_state_in_len e') = false)%Z%bool ->
      evt a0segs Q (MS (RBZ x1 x5 x6 x7 (Z_to_bv 64 3) x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x82668) fc None m (seg_rom a0segs))).
    { intros x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x22 x23 x28 x29 x30 x31 EMP.
      (* [comment removed for export] *)
      arun_to 0x82698%Z. try rewrite (sx32_of_Z (e_state_out_pos e')) by lia. try rewrite (sx32_of_Z (bw_numZ (e_bw e'))) by lia.
      wstep; if_cases KN; zify_cond_z KN.
      { lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (FOK mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
          [st_eq| ..]; try xside.
        replace (e_state_out_pos e' <? bw_numZ (e_bw e'))%Z with true by (symmetry; apply Z.ltb_lt; lia). apply Bool.orb_true_r. }
      rewrite EMP in RES. replace (e_state_out_pos e' <? bw_numZ (e_bw e'))%Z with false in RES by (symmetry; apply Z.ltb_ge; lia). cbn [orb] in RES.
      inversion RES; subst ret e'' z''.
      (* [comment removed for export] *)
      arun_to 0x826a8%Z. wstep; lit_store. wstep. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (EXIT mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
        [unfold BZ_STREAM_END; st_eq| ..]; xside. }
    wstep; if_cases KC; zify_cond_z KC.
    2:{ (* [comment removed for export] *)
        arun_to 0x82664%Z. try rewrite (sx32_of_Z (e_state_in_len e')) by lia.
        wstep; if_cases KL; zify_cond_z KL.
        - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (FOK mm _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _) end;
            [st_eq| ..]; try xside.
          replace (e_state_in_ch e' <? 256)%Z with true by (symmetry; apply Z.ltb_lt; lia).
          replace (0 <? e_state_in_len e')%Z with true by (symmetry; apply Z.ltb_lt; lia). reflexivity.
        - enter_with (JN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq|].
          replace (0 <? e_state_in_len e')%Z with false by (symmetry; apply Z.ltb_ge; lia). apply Bool.andb_false_r. }
    enter_with (JN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq|].
    replace (e_state_in_ch e' <? 256)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity.
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.

End A0BZC.

End ACeilS1.
