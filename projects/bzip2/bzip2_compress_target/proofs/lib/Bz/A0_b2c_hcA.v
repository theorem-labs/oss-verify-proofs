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

Section A0HCA.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (OB : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation STRM := (c_bz cx + BZF_STRM)%Z.
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x61e000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis OOK : out_okB (aci_c A0C) cx ob on. Hypothesis LOB : Z.of_nat (length OB) = on.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis SOS : apartv ob on STRM 80.
  Definition co_W : list (Z * Z) := [(E + 120, E + 124); (STRM + 24, STRM + 44); (ob, ob + on)]%Z.

  Lemma A0_co_loop : forall (fuel : nat) g e z (ni : Z) (me m : word -> option byte)
      (ra sp t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s5 s6 s8 t3 t4 t5 t6 : word),
    (Z.of_nat fuel > z_avail_out z)%Z -> e_state e = BZ_S_OUTPUT -> z_avail_out z <> 0%Z -> (e_state_out_pos e < bw_numZ (e_bw e))%Z ->
    HCXB cx on g e z ->
    rw_cells a0segs m E (EHEAD1 cx g e) -> rw_cells a0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) ->
    u8arr a0segs m ob (outb (z_outr z) OB) ->
    (forall m', munch co_W me m' -> u8arr a0segs m' A2 (zb8 (e_arr2 e) ARR2_SIZE)) ->
    mem_inv a0segs m -> munch co_W me m -> wmono a0segs me m ->
    shzW a0segs co_W me E (E + ESTATE_SIZE) -> shzW a0segs co_W me STRM (STRM + 80) -> shzW a0segs co_W me A2 (A2 + ARR2_SIZE) -> shpW a0segs co_W me ob (ob + on) ->
    (forall e' z' m' (a1' a2' a3' : word),
        copy_output fuel e z true = (e', z', true) -> e_state e' = BZ_S_OUTPUT ->
        (z_avail_out z' = 0 \/ bw_numZ (e_bw e') <= e_state_out_pos e')%Z ->
        HCXB cx on g e' z' -> z_in z' = z_in z -> z_avail_in z' = z_avail_in z -> e_arr2 e' = e_arr2 e ->
        rw_cells a0segs m' E (EHEAD1 cx g e') -> rw_cells a0segs m' STRM (STRMB cx ob on dbza dbzfr z' ni p1 p2) ->
        u8arr a0segs m' ob (outb (z_outr z') OB) ->
        mem_inv a0segs m' -> munch co_W me m' -> wmono a0segs me m' ->
        evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) cSB (Z_to_bv 64 1) a1' a2' a3' a4 a5 a6 a7
                              s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) s5 s6 (Z_to_bv 64 (E + 116)) s8 (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6)
                         F (Z_to_bv 64 0x82bd8) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) cSB a0 (Z_to_bv 64 STRM) (Z_to_bv 64 (e_state_out_pos e)) a3 a4 a5 a6 a7
                          s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) s5 s6 (Z_to_bv 64 (E + 116)) s8 (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82a44) fc None m (seg_rom a0segs)).
  Proof.
    induction fuel as [|fuel IH]; intros g e z ni me m ra sp t0 t1 t2 a0 a3 a4 a5 a6 a7 s2 s5 s6 s8 t3 t4 t5 t6 FUEL STO AO POS HX EH1 SM OBM VA2 MI MU WM SHe SHs SH2 SHo K.
    { pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & _). exfalso; lia. }
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI.
    pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK. pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN). cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    unfold est_ok in EOK. cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO).
    cb_ranges CX.
    pose proof OOK as OOK'. unfold out_okB, apart, img_apart in OOK'. cbn [ci_hi aci_c A0C] in OOK'. cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    unfold CEILv, CEIL, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs.
    pose proof (outb_length_nat (z_outr z) OB ltac:(lia)) as LOBn. replace (length OB) with (Z.to_nat on) in LOBn by lia.
    unfold co_W in MU, SHe, SHs, SH2, SHo, VA2.
    unfold EHEAD1 in EH1. unfold STRMB in SM. rewrite GZ in EH1.
    (* [comment removed for export] *)
    arun_to 0x82a8c%Z.
    ack_rd (ob + (on - z_avail_out z))%Z 1%Z.
    pose proof (VA2 m MU) as AR2.
    pose proof (zb8_read1 a0segs m A2 (e_arr2 e) ARR2_SIZE (e_nblock e + e_state_out_pos e) _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD AR2. cbv beta.
    set (c := zget (e_arr2 e) (e_nblock e + e_state_out_pos e)%Z).
    assert (Hc : (0 <= c < 256)%Z) by (subst c; apply BOK2). rewrite (unsigned_lit8 c Hc).
    ack_merge.
    (* [comment removed for export] *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok a0segs mm ob _ (on - z_avail_out z) _ OBM ltac:(rewrite LOBn; lia) eq_refl) as SO end.
    wstep. rewrite le1_lit'.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u8arr_write a0segs mm ob (outb (z_outr z) OB) (on - z_avail_out z) (Z_to_bv 8 c) OBM ltac:(rewrite LOBn; lia)) as OBM' end.
    clear OBM. store_done. rename OBM' into OBM.
    replace (upd (outb (z_outr z) OB) (Z.to_nat (on - z_avail_out z)) (Z_to_bv 8 c)) with (outb (c :: z_outr z) OB) in OBM
      by (rewrite outb_cons by lia; f_equal; lia).
    clear LOBn. pose proof (outb_length_nat (c :: z_outr z) OB ltac:(cbn [length]; lia)) as LOBn. replace (length OB) with (Z.to_nat on) in LOBn by lia.
    (* [comment removed for export] *)
    arun_to 0x82b1c%Z.
    reword_C4 SM 7%nat (m32 (z_tout_lo z + 1))%Z. { rewrite low32_inc_sx32, m32_eq. symmetry. apply low32_mod. }
    replace (z_avail_out z + -1)%Z with (z_avail_out z - 1)%Z in SM by lia.
    replace (ob + (on - z_avail_out z) + 1)%Z with (ob + (on - (z_avail_out z - 1)))%Z in SM by lia.
    assert (COS : copy_output (S fuel) e z true = copy_output fuel (fst (co_step e z)) (snd (co_step e z)) true).
    { rewrite copy_output_S. replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    pose proof (hlB_co _ _ LAWS cx on g e z HX STO AO POS) as HX'.
    assert (Ec : c = zget (bw_zb (e_bw e)) (e_state_out_pos e)) by (subst c; apply ZREL; lia).
    set (e1 := fst (co_step e z)) in *. set (z1 := snd (co_step e z)) in *.
    assert (Ee1 : e1 = est_set_outpos e (e_state_out_pos e + 1)) by (subst e1; rewrite co_step_eq; reflexivity).
    assert (Ez1 : z1 = ZS (z_in z) (z_avail_in z) (c :: z_outr z) (z_avail_out z - 1) (z_tin_lo z) (z_tin_hi z) (m32 (z_tout_lo z + 1))
                         (if (m32 (z_tout_lo z + 1) =? 0)%Z then (z_tout_hi z + 1)%Z else z_tout_hi z))
      by (subst z1; rewrite co_step_eq, Ec; reflexivity).
    clearbody e1 z1. subst e1 z1. cbn [fst snd] in COS, HX'.
    set (hi' := if (m32 (z_tout_lo z + 1) =? 0)%Z then (z_tout_hi z + 1)%Z else z_tout_hi z) in COS, HX'.
    set (zn := ZS (z_in z) (z_avail_in z) (c :: z_outr z) (z_avail_out z - 1) (z_tin_lo z) (z_tin_hi z) (m32 (z_tout_lo z + 1)) hi') in *.
    set (en := est_set_outpos e (e_state_out_pos e + 1)) in *.
    (* [comment removed for export] *)
    assert (TAIL : forall (mt : word -> option byte) (x10 x13 : word),
      rw_cells a0segs mt E (EHEAD1 cx g en) -> rw_cells a0segs mt STRM (STRMB cx ob on dbza dbzfr zn ni p1 p2) -> u8arr a0segs mt ob (outb (z_outr zn) OB) ->
      mem_inv a0segs mt -> munch co_W me mt -> wmono a0segs me mt ->
      evt a0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) cSB x10 (Z_to_bv 64 STRM) (Z_to_bv 64 (z_avail_out z - 1)) x13 a4 a5 a6 a7
                            s2 (Z_to_bv 64 (E + 120)) (Z_to_bv 64 (SHE + 15)) s5 s6 (Z_to_bv 64 (E + 116)) s8 (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6)
                       F (Z_to_bv 64 0x82b40) fc None mt (seg_rom a0segs))).
    { clear EH1 SM OBM MI MU WM. intros mt x10 x13 EH1 SM OBM MI MU WM. unfold co_W in MU.
      assert (AR2E : e_arr2 en = e_arr2 e) by reflexivity.
      (* [comment removed for export] *)
      wstep. wstep; if_cases Kz; zify_cond_z Kz.
      { (* [comment removed for export] *)
        enter_with (K en zn mt _ _ _);
          [ st_eq
          | rewrite COS; destruct fuel; [reflexivity| rewrite copy_output_S; subst zn; cbn [z_avail_out];
            replace (z_avail_out z - 1 =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity]
          | exact STO | subst zn; cbn [z_avail_out]; lia | exact HX' | reflexivity | reflexivity | exact AR2E
          | exact EH1 | exact SM | exact OBM | exact MI | unfold co_W; exact MU | exact WM ]. }
      (* [comment removed for export] *)
      pose proof EH1 as EH1r. unfold EHEAD1 in EH1r. subst en. cbn [e_state_out_pos e_bw est_set_outpos] in EH1r. set (en := est_set_outpos e (e_state_out_pos e + 1)) in *.
      arun_to 0x82b60%Z. clear EH1r.
      try rewrite (sx32_of_Z (e_state_out_pos e + 1)) by lia. try rewrite (sx32_of_Z (bw_numZ (e_bw e))) by lia.
      wstep; if_cases Kp; zify_cond_z Kp.
      { enter_with (K en zn mt _ _ _);
          [ st_eq
          | rewrite COS; destruct fuel; [reflexivity| rewrite copy_output_S; subst zn en; cbn [z_avail_out e_bw e_state_out_pos est_set_outpos];
            replace (z_avail_out z - 1 =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia);
            replace (bw_numZ (e_bw e) <=? e_state_out_pos e + 1)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity]
          | exact STO | subst en; cbn [e_bw e_state_out_pos est_set_outpos]; lia | exact HX' | reflexivity | reflexivity | exact AR2E
          | exact EH1 | exact SM | exact OBM | exact MI | unfold co_W; exact MU | exact WM ]. }
      (* [comment removed for export] *)
      wstep.
      enter_with (IH g en zn ni me mt ra sp t0 t1 t2 _ _ a4 a5 a6 a7 s2 s5 s6 s8 t3 t4 t5 t6);
        [ subst en; cbn [e_state_out_pos est_set_outpos]; st_eq
        | subst zn; cbn [z_avail_out]; lia | exact STO | subst zn; cbn [z_avail_out]; lia | subst en; cbn [e_bw e_state_out_pos est_set_outpos]; lia
        | exact HX' | exact EH1 | exact SM | exact OBM | exact VA2 | exact MI | unfold co_W; exact MU | exact WM | exact SHe | exact SHs | exact SH2 | exact SHo
        | intros e' z' m' a1' a2' a3' CO' ST' EX' HXn ZI' ZA' AR' EH1' SM' OBM' MI' MU' WM';
          eapply K; [rewrite COS; exact CO'| exact ST' | exact EX' | exact HXn | exact ZI' | exact ZA' | exact AR' | exact EH1' | exact SM' | exact OBM' | exact MI' | exact MU' | exact WM'] ]. }
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (NC : (m32 (z_tout_lo z + 1) <> 0)%Z).
      { intros Hz. apply Kc. apply (proj2 (swrap32_mod64_zero_iff _)). rewrite inc_sx32_mod. exact Hz. }
      assert (EH1n : rw_cells a0segs _ E (EHEAD1 cx g en)) by (unfold EHEAD1; subst en; cbn_est; cbn [est_set_outpos]; rewrite GZ; exact EH1). clear EH1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _) end;
        [st_eq| exact EH1n| unfold STRMB; subst zn hi'; cbn_est; rewrite (proj2 (Z.eqb_neq _ _) NC); exact SM| subst zn; cbn [z_outr]; exact OBM| exact MI| unfold co_W; exact MU| exact WM].
    - (* [comment removed for export] *)
      assert (CA : (m32 (z_tout_lo z + 1) = 0)%Z).
      { apply (proj1 (swrap32_mod64_zero_iff _)) in Kc. rewrite inc_sx32_mod in Kc. exact Kc. }
      arun_to 0x82b40%Z.
      reword_C4 SM 8%nat (z_tout_hi z + 1)%Z. { first [rewrite low32_inc64_sx32 | rewrite low32_inc64_sx32_mod]. reflexivity. }
      assert (EH1n : rw_cells a0segs _ E (EHEAD1 cx g en)) by (unfold EHEAD1; subst en; cbn_est; cbn [est_set_outpos]; rewrite GZ; exact EH1). clear EH1.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _) end;
        [st_eq| exact EH1n| unfold STRMB; subst zn hi'; cbn_est; rewrite (proj2 (Z.eqb_eq _ _) CA); exact SM| subst zn; cbn [z_outr]; exact OBM| exact MI| unfold co_W; exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End A0HCA.

End ACeilS1.
