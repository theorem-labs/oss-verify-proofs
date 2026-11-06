(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTables BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCBlock BzCDriver BzArrD CmpMem CmpCut CmpArith CmpArith2 CmpSess CmpSessB CmpSdTac GlueTac BzInv BzCLemmas1 CmpFsKit0 AsanKit AsanCut AsanCutB0 AsanKitB0.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV B0_cmp_msV B0_b2c_cbV B0_b2c_hcV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpHmKit.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpHmKit.
Local Ltac AsanKit.a_norm ::= AsanKit.sh_fold.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

(* [comment removed for export] *)

Section B0HCA.
  Variables (cx : cctx) (Q : machine_state -> Prop).
  Variables (HCXB : cctx -> Z -> eg -> est -> zstrm -> Prop) (CBFACTS : est -> Prop).
  Variables (SHE SHS : Z) (ob on dbza dbzfr : Z) (p1 p2 : word) (OB : list byte).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Notation E := (c_E cx). Notation A2 := (c_A2 cx). Notation STRM := (c_bz cx + BZF_STRM)%Z.
  Notation cSB := (Z_to_bv 64 2147450880).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx. Hypothesis LAWS : hc_lawsB HCXB CBFACTS.
  Hypothesis AE : sanchor E SHE. Hypothesis AS : sanchor STRM SHS.
  Hypothesis SLO : (0x62b000 <= STRM)%Z. Hypothesis SHI : (STRM + 80 <= CEILv)%Z.
  Hypothesis OOK : out_okB (aci_c B0C) cx ob on. Hypothesis LOB : Z.of_nat (length OB) = on.
  Hypothesis SES : apartv E ESTATE_SIZE STRM 80. Hypothesis SOS : apartv ob on STRM 80.
  Definition co_W : list (Z * Z) := [(E + 120, E + 124); (STRM + 24, STRM + 44); (ob, ob + on)]%Z.

  Ltac cbn_est := cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
         e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
         e_len e_code e_rfreq e_len_pack est_set_outpos est_set_modes est_set_rl est_rl rl_nblock rl_block rl_inUse rl_crc rl_ch rl_len
         z_in z_avail_in z_outr z_avail_out z_tin_lo z_tin_hi z_tout_lo z_tout_hi fst snd].

  Lemma B0_co_loop : forall (fuel : nat) g e z (p : bool) (ni : Z) (me m : word -> option byte)
      (ra sp t0 t1 t2 s1 a0 a2 a4 a5 a6 a7 s2 s3 s6 s7 t3 t4 t5 t6 : word),
    (Z.of_nat fuel > z_avail_out z)%Z -> e_state e = BZ_S_OUTPUT ->
    HCXB cx on g e z ->
    rw_cells b0segs m E (EHEAD1 cx g e) -> rw_cells b0segs m STRM (STRMB cx ob on dbza dbzfr z ni p1 p2) ->
    u8arr b0segs m ob (outb (z_outr z) OB) ->
    (forall m', munch co_W me m' -> u8arr b0segs m' A2 (zb8 (e_arr2 e) ARR2_SIZE)) ->
    mem_inv b0segs m -> munch co_W me m -> wmono b0segs me m ->
    shzW b0segs co_W me E (E + ESTATE_SIZE) -> shzW b0segs co_W me STRM (STRM + 80) -> shzW b0segs co_W me A2 (A2 + ARR2_SIZE) -> shpW b0segs co_W me ob (ob + on) ->
    (forall e' z' (p' : bool) m' (a2' a5' a6' : word),
        copy_output fuel e z p = (e', z', p') -> e_state e' = BZ_S_OUTPUT ->
        (z_avail_out z' = 0 \/ bw_numZ (e_bw e') <= e_state_out_pos e')%Z ->
        HCXB cx on g e' z' -> z_in z' = z_in z -> z_avail_in z' = z_avail_in z -> e_arr2 e' = e_arr2 e ->
        rw_cells b0segs m' E (EHEAD1 cx g e') -> rw_cells b0segs m' STRM (STRMB cx ob on dbza dbzfr z' ni p1 p2) ->
        u8arr b0segs m' ob (outb (z_outr z') OB) ->
        mem_inv b0segs m' -> munch co_W me m' -> wmono b0segs me m' ->
        evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 (Z_to_bv 64 (SHE + -2147450866)) (Z_to_bv 64 STRM) a2' (Z_to_bv 64 (Z.b2z p')) (Z_to_bv 64 (SHE + -2147450865)) a5' a6' a7
                              s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) s6 s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB t3 t4 t5 t6)
                         F (Z_to_bv 64 0x82850) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 a0 (Z_to_bv 64 STRM) a2 (Z_to_bv 64 (Z.b2z p)) a4 a5 a6 a7
                          s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) s6 s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB t3 t4 t5 t6)
                     F (Z_to_bv 64 0x82608) fc None m (seg_rom b0segs)).
  Proof.
    induction fuel as [|fuel IH]; intros g e z p ni me m ra sp t0 t1 t2 s1 a0 a2 a4 a5 a6 a7 s2 s3 s6 s7 t3 t4 t5 t6 FUEL STO HX EH1 SM OBM VA2 MI MU WM SHe SHs SH2 SHo K.
    { pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI. pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & _). exfalso; lia. }
    pose proof (hlB_hci _ _ LAWS _ _ _ _ _ HX) as HI.
    pose proof (HCIB_est_ok _ _ _ _ _ HI) as EOK. pose proof (HCIB_avail_out _ _ _ _ _ HI) as (AOR & OLEN). cps_pose (HCIB_output _ _ _ _ _ HI STO) as (GZ & NZR & ZREL).
    unfold est_ok in EOK. cps_destruct EOK as (BOK1 & BOK2 & FTR & NBR & NZ0 & POSR & MODES & STATES & CHR & LENR & CRCR & CCR & BNO).
    cb_ranges CX.
    pose proof OOK as OOK'. unfold out_okB, apart, img_apart in OOK'. cbn [ci_hi aci_c B0C] in OOK'. cps_destruct OOK' as (RO1 & RO2 & RO3 & RO4 & SO1 & SO2 & SO3 & SO4 & IO).
    pose proof SEP as SP'; unfold cctx_sep, apart, ESTATE_SIZE in SP'; cbv zeta in SP'; cps_destruct SP' as (_ & AEA2 & _).
    unfold CEILv, CEIL, apartv, ESTATE_SIZE in *. box_ors.
    pose proof (proj2 AE : saddr E SHE) as AEs. pose proof (proj1 AE) as EM8. pose proof (proj1 AS) as SM8.
    pose proof (b2z_range p) as BPP.
    pose proof (outb_length_nat (z_outr z) OB ltac:(lia)) as LOBn. replace (length OB) with (Z.to_nat on) in LOBn by lia.
    unfold co_W in MU, SHe, SHs, SH2, SHo, VA2.
    pose proof EH1 as EH1f. unfold EHEAD1 in EH1. unfold STRMB in SM. rewrite GZ in EH1.
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (z_avail_out z)) by lia. sh_norm.
    if_cases KA; zify_cond_z KA.
    { eapply (K e z p m); [ rewrite copy_output_S; replace (z_avail_out z =? 0)%Z with true by (symmetry; apply Z.eqb_eq; lia); reflexivity
        | exact STO | lia | exact HX | reflexivity | reflexivity | reflexivity | exact EH1f | unfold STRMB; exact SM | exact OBM | exact MI | unfold co_W; exact MU | exact WM ]. }
    (* [comment removed for export] *)
    brun. try rewrite (sx32_of_Z (e_state_out_pos e)) by lia. try rewrite (sx32_of_Z (bw_numZ (e_bw e))) by lia.
    if_cases KG; zify_cond_z KG.
    { eapply (K e z p m); [ rewrite copy_output_S; replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia);
                            replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with true by (symmetry; apply Z.leb_le; lia); reflexivity
        | exact STO | lia | exact HX | reflexivity | reflexivity | reflexivity | exact EH1f | unfold STRMB; exact SM | exact OBM | exact MI | unfold co_W; exact MU | exact WM ]. }
    assert (COS : copy_output (S fuel) e z p = copy_output fuel (fst (co_step e z)) (snd (co_step e z)) true).
    { rewrite copy_output_S. replace (z_avail_out z =? 0)%Z with false by (symmetry; apply Z.eqb_neq; lia).
      replace (bw_numZ (e_bw e) <=? e_state_out_pos e)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
    pose proof (hlB_co _ _ LAWS cx on g e z HX STO ltac:(lia) ltac:(lia)) as HX'.
    set (c := zget (e_arr2 e) (e_nblock e + e_state_out_pos e)%Z).
    assert (Hc : (0 <= c < 256)%Z) by (subst c; apply BOK2).
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
    assert (TAIL : forall (mt : word -> option byte) (x10 x11 x12 x13 x14 x15 x16 : word),
      rw_cells b0segs mt E (EHEAD1 cx g en) -> rw_cells b0segs mt STRM (STRMB cx ob on dbza dbzfr zn ni p1 p2) -> u8arr b0segs mt ob (outb (z_outr zn) OB) ->
      mem_inv b0segs mt -> munch co_W me mt -> wmono b0segs me mt ->
      evt b0segs Q (MS (mkR ra sp gp tp t0 t1 t2 (Z_to_bv 64 E) s1 x10 x11 x12 x13 x14 x15 x16 a7
                            s2 s3 (Z_to_bv 64 2) (Z_to_bv 64 (E + 120)) s6 s7 (Z_to_bv 64 (E + 116)) (Z_to_bv 64 SHE) (Z_to_bv 64 (E + 80)) cSB t3 t4 t5 t6)
                       F (Z_to_bv 64 0x82798) fc None mt (seg_rom b0segs))).
    { clear EH1 EH1f SM OBM MI MU WM. intros mt x10 x11 x12 x13 x14 x15 x16 EH1 SM OBM MI MU WM. unfold co_W in MU.
      assert (AR2E : e_arr2 en = e_arr2 e) by reflexivity.
      pose proof EH1 as EH1f. unfold EHEAD1 in EH1. rewrite GZ in EH1. unfold STRMB in SM.
      (* [comment removed for export] *)
      brun_to 0x82608%Z.
      enter_with (IH g en zn true ni me mt ra sp t0 t1 t2 s1 _ _ _ _ _ a7 s2 s3 s6 s7 t3 t4 t5 t6);
        [ st_eq
        | subst zn; cbn [z_avail_out]; lia | subst en; cbn [e_state est_set_outpos]; exact STO | exact HX'
        | exact EH1f | unfold STRMB; exact SM | exact OBM | rewrite AR2E; exact VA2 | exact MI | unfold co_W; exact MU | exact WM | exact SHe | exact SHs | exact SH2 | exact SHo
        | intros e' z' p' m' a2' a5' a6' CO' ST' EX' HXn ZI' ZA' AR' EH1' SM' OBM' MI' MU' WM';
          eapply K; [rewrite COS; exact CO'| exact ST' | exact EX' | exact HXn | subst zn; exact ZI' | subst zn; exact ZA' | rewrite <- AR2E; exact AR'
                    | exact EH1' | exact SM' | exact OBM' | exact MI' | exact MU' | exact WM'] ]. }
    (* [comment removed for export] *)
    brun_to 0x826c0%Z.
    ack_rd (ob + (on - z_avail_out z))%Z 1%Z.
    (* [comment removed for export] *)
    pose proof (VA2 m MU) as AR2.
    pose proof (zb8_read1 b0segs m A2 (e_arr2 e) ARR2_SIZE (e_nblock e + e_state_out_pos e) _ AR2 ltac:(lia) ltac:(unfold wa; f_equal; lia)) as RD.
    wstep. clear RD AR2. cbv beta. fold c. rewrite (unsigned_lit8 c Hc).
    (* [comment removed for export] *)
    ack_merge.
    (* [comment removed for export] *)
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (u8arr_store_ok b0segs mm ob _ (on - z_avail_out z) _ OBM ltac:(rewrite LOBn; lia) eq_refl) as SO end.
    wstep. rewrite le1_lit'.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?mm _ _) _) =>
      pose proof (u8arr_write b0segs mm ob (outb (z_outr z) OB) (on - z_avail_out z) (Z_to_bv 8 c) OBM ltac:(rewrite LOBn; lia)) as OBM' end.
    clear OBM. store_done. rename OBM' into OBM.
    replace (upd (outb (z_outr z) OB) (Z.to_nat (on - z_avail_out z)) (Z_to_bv 8 c)) with (outb (c :: z_outr z) OB) in OBM
      by (rewrite outb_cons by lia; f_equal; lia).
    clear LOBn. pose proof (outb_length_nat (c :: z_outr z) OB ltac:(cbn [length]; lia)) as LOBn. replace (length OB) with (Z.to_nat on) in LOBn by lia.
    (* [comment removed for export] *)
    brun.
    reword_C4 SM 7%nat (m32 (z_tout_lo z + 1))%Z. { rewrite low32_inc_sx32, m32_eq. symmetry. apply low32_mod. }
    replace (z_avail_out z + -1)%Z with (z_avail_out z - 1)%Z in SM by lia.
    replace (ob + (on - z_avail_out z) + 1)%Z with (ob + (on - (z_avail_out z - 1)))%Z in SM by lia.
    assert (EH1n : forall mm, rw_cells b0segs mm E
      [C8 (Z_to_bv 64 STRM); C4 (Z_to_bv 64 (e_mode e)); C4 (Z_to_bv 64 (e_state e)); C4 (if g_aie g then Z_to_bv 64 (e_avail_in_expect e) else jw4 (c_J cx) 16); C4 (jw4 (c_J cx) 20);
       C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 (c_FT cx)); C4 (if g_sort g then Z_to_bv 64 (e_origPtr e) else jw4 (c_J cx) 48); C4 (jw4 (c_J cx) 52);
       C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 A2); C8 (Z_to_bv 64 (c_A1 cx)); C8 (Z_to_bv 64 (A2 + e_nblock e));
       C4 (Z_to_bv 64 WORKFACTOR); C4 (Z_to_bv 64 (e_state_in_ch e)); C4 (Z_to_bv 64 (e_state_in_len e)); C4 (jw4 (c_J cx) 100); C4 (jw4 (c_J cx) 104);
       C4 (Z_to_bv 64 (e_nblock e)); C4 (Z_to_bv 64 NBLOCKMAX); C4 (Z_to_bv 64 (bw_numZ (e_bw e))); C4 (Z_to_bv 64 (e_state_out_pos e + 1));
       C4 (if g_mtf g then Z_to_bv 64 (e_nInUse e) else jw4 (c_J cx) 124)] -> rw_cells b0segs mm E (EHEAD1 cx g en)).
    { intros mm H. unfold EHEAD1. subst en. cbn_est. rewrite GZ. exact H. }
    if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (NC : (m32 (z_tout_lo z + 1) <> 0)%Z).
      { intros Hz. apply Kc. apply (proj2 (swrap32_mod64_zero_iff _)). rewrite inc_sx32_mod. exact Hz. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _ _ _) end;
        [st_eq| apply EH1n; first [exact EH1 | cells_eq_by EH1]| unfold STRMB; subst zn hi'; cbn_est; rewrite (proj2 (Z.eqb_neq _ _) NC); exact SM| subst zn; cbn [z_outr]; exact OBM| exact MI| unfold co_W; exact MU| exact WM].
    - (* [comment removed for export] *)
      assert (CA : (m32 (z_tout_lo z + 1) = 0)%Z).
      { apply (proj1 (swrap32_mod64_zero_iff _)) in Kc. rewrite inc_sx32_mod in Kc. exact Kc. }
      brun_to 0x82798%Z.
      reword_C4 SM 8%nat (z_tout_hi z + 1)%Z. { first [rewrite low32_inc64_sx32 | rewrite low32_inc64_sx32_mod]. reflexivity. }
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (TAIL mm _ _ _ _ _ _ _) end;
        [st_eq| apply EH1n; first [exact EH1 | cells_eq_by EH1]| unfold STRMB; subst zn hi'; cbn_est; rewrite (proj2 (Z.eqb_eq _ _) CA); exact SM| subst zn; cbn [z_outr]; exact OBM| exact MI| unfold co_W; exact MU| exact WM].
  Unshelve. all: try exact (Z_to_bv 64 0).
  Qed.
End B0HCA.

End ACeilS1.
