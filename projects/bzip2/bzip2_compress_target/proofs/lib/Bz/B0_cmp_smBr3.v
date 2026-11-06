(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib SegsA0 SegsB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut AsanCutB0 AsanKitB0.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_fsV.   (* [comment removed for export] *)
From Stdlib Require Lia. Unset Lia Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpCut6.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.   (* [comment removed for export] *)
Local Ltac BzTac.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.   (* [comment removed for export] *)
Local Ltac lia ::= CmpLiaC.lia_c.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.   (* [comment removed for export] *)
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.   (* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpStEq.   (* [comment removed for export] *)
Local Ltac BzTac.st_eq ::= CmpStEq.st_eq_fast.   (* [comment removed for export] *)
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.   (* [comment removed for export] *)
(* [comment removed for export] *)
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
(* [comment removed for export] *)
Local Ltac Lib.Step.solve_load ::= AsanKit.asan_solve_load.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpRel.   (* [comment removed for export] *)
Local Ltac lia ::= CmpRel.lia_cr.   (* [comment removed for export] *)
Local Ltac Lib.StoreFast.tlia ::= RelLia.tlia_r.   (* [comment removed for export] *)
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section FR.
  Variables (cx : cctx) (e : est) (Q : machine_state -> Prop).
  Variables (ra gp tp t0 t1 t2 s0 a4 s3 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P : Z).
  Variables (rf0 : zarr) (gs bt bc nSel B : Z).
  Hypothesis CX : cctx_ok cx.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation J := (c_J cx).
  Notation arr1 := (e_arr1 e). Notation A := (sm_alpha e). Notation nG := (smA_ng e). Notation nMTF := (sm_nmtf e).
  Notation q := (QV arr1 gs).
  Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsM : (gs + 50 <= nMTF)%Z. Hypothesis HM : (nMTF <= (NBLOCKMAX + 20))%Z.
  Hypothesis Hbt : (0 <= bt < nG)%Z. Hypothesis HnG : (nG <= 6)%Z. Hypothesis HB : (0 <= B)%Z. Hypothesis HBM : (B + 50 <= 2000000000)%Z.
  Hypothesis ZB : zbok arr1.
  Hypothesis QB : forall k, (0 <= k < 50)%Z -> (0 <= q k < A)%Z.
  Ltac openCX :=
    let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
    cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb).
  (* [comment removed for export] *)
  Ltac bzl :=
    repeat match goal with
    | |- context [Z.shiftr ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftr_div a k) by lia
    | |- context [Z.shiftl ?a ?k] => is_Zlit_zb k; rewrite (zb_shiftl_mul a k) by lia
    | |- context [Z.modulo ?e 18446744073709551616] => rewrite (Z.mod_small e 18446744073709551616) by lia
    | |- context [bv_swrap 32 ?e] => rewrite (swrap32_id e) by lia
    | |- context [Z.lxor ?e 18446744073709551615] => rewrite (zb_lxor_ones e) by lia
    | |- context [Z.lxor ?e 9223372036854775808] => rewrite (lxor_sign_small e) by lia      (* [comment removed for export] *)
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  (* [comment removed for export] *)
  Ltac fstep := let R := AsanKitB0.b_regs in AsanKit.a_zstep_nofb; bzl; AsanKitB0.b_flags R; AsanKit.a_try_lit_branch; AsanKitB0.b_try_guard.
  Ltac frun_to p := first [ AsanKit.a_at_pc p | AsanKit.a_pc_is_lit; fstep; frun_to p | fail 1 "frun_to: stuck before" p ].
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  (* [comment removed for export] *)
  Ltac RDV V :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let RO := fresh "RO" in pose proof (V mm MU') as RO; lstep; clear RO end.
  (* [comment removed for export] *)
  Ltac RDQ VAR1 k :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let AR1v := fresh "AR1v" in let RD := fresh "RD" in
      pose proof (VAR1 mm MU') as AR1v;
      pose proof (zb8_read2 b0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1v ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD;
      clear AR1v;
      change (rd16 arr1 (2 * (gs + k))) with (q k) in RD;
      pose proof (QB k ltac:(lia)) as ?QBk;
      lstep; clear RD; rewrite (zx16_lit (q k)) by lia end.
  (* [comment removed for export] *)
  Ltac RDRF RFQ RFF k :=
    let RD := fresh "RD" in let Fk := fresh "RFk" in
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk _ _) =>
    pose proof (RFF (q k) ltac:(lia)) as Fk;
    pose proof (ovw_read b0segs mm (E + 45448) rfk (jseg J 45448 6192) 1548 (258 * bt + q k) _ RFQ ltac:(lia) (proj1 Fk) ltac:(unfold wa; f_equal; lia)) as RD;
    lstep; clear RD; rewrite (sx32_of_Z (zget rfk (258 * bt + q k))) by (change (2^31)%Z with 2147483648%Z; lia) end end.
  Ltac STRF RFQ k :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk _ _) =>
    pose proof (u32arr_store_ok b0segs mm (E + 45448) _ (258 * bt + q k) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
    lstep; store_addr (E + 45448 + 4 * (258 * bt + q k))%Z;
    ovw_store RFQ (258 * bt + q k)%Z (zget rfk (258 * bt + q k) + 1)%Z (rewrite unsigned_lit by lia; reflexivity) end end.
  (* [comment removed for export] *)
  Ltac RFNEXT RFQ ERF RFF k knat :=
    lazymatch type of RFQ with u32arr _ ?mm _ (ovw (zset ?rfk ?i (zget ?rfk ?i + 1)) _ _) =>
      let rf' := fresh "rf" in let E' := fresh "ERF" in let F' := fresh "RFF" in
      pose proof (RFrow_incr rfk bt A _ (q k) RFF (QB k ltac:(lia))) as F';
      change (zset rfk i (zget rfk i + 1)) with (zincr rfk i) in RFQ;
      remember (zincr rfk i) as rf' eqn:E' in RFQ;
      rewrite <- E' in F'; rewrite ERF in E'; rewrite <- (sm_rfreq_inc_QVz knat k rf0 arr1 bt gs eq_refl) in E';
      clear ERF RFF; rename E' into ERF; rename F' into RFF
    end.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma B0_fr3 : forall (m me : word -> option byte) (rfk : zarr) (xa0 xa2 xa5 : word),
    u32arr b0segs m (E + 45448) (ovw rfk (jseg J 45448 6192) 1548) ->
    rfk = sm_rfreq_inc 34 rf0 arr1 bt gs -> RFrow rfk bt A (B + 34) ->
    mem_inv b0segs m -> munch Wrf me m -> wmono b0segs me m ->
    (forall m', munch Wrf me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs Wrf me A1 (A1 + ARR1_SIZE) -> shzW b0segs Wrf me E (E + ESTATE_SIZE) ->
    frdW b0segs Wrf me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (rfk' : zarr) (ya0 ya1 ya2 ya3 ya5 ya7 : word),
      u32arr b0segs m' (E + 45448) (ovw rfk' (jseg J 45448 6192) 1548) ->
      rfk' = sm_rfreq_inc 50 rf0 arr1 bt gs -> RFrow rfk' bt A (B + 50) ->
      mem_inv b0segs m' -> munch Wrf me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR ra (Z_to_bv 64 (P)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (P)) ya0 ya1 ya2 ya3 a4 ya5 (Z_to_bv 64 (gs)) ya7 (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x91d9c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 (P)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (P)) xa0 (Z_to_bv 64 (E + 1032 * bt + 45448)) xa2 (Z_to_bv 64 (gs + 34)) a4 xa5 (Z_to_bv 64 (gs)) (Z_to_bv 64 ((-1) * E + (-1032) * bt + 18446744073709506167)) (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x911cc) fc None m (seg_rom b0segs)).
  Proof.
    intros m me rfk xa0 xa2 xa5 RFQ ERF RFF MI MU WM VAR1 SHa SHe V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rfk (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    frun_to 0x911d8%Z. RDV V1552.
    frun_to 0x911e8%Z. RDV V1552.
    frun_to 0x91224%Z. RDQ VAR1 34%Z.
    frun_to 0x91254%Z. RDRF RFQ RFF 34%Z.
    frun_to 0x91274%Z. STRF RFQ 34%Z. RFNEXT RFQ ERF RFF 34%Z 34%nat.
    frun_to 0x91284%Z. RDV V1552.
    frun_to 0x91294%Z. RDV V1552.
    frun_to 0x912d0%Z. RDQ VAR1 35%Z.
    frun_to 0x91300%Z. RDRF RFQ RFF 35%Z.
    frun_to 0x91320%Z. STRF RFQ 35%Z. RFNEXT RFQ ERF RFF 35%Z 35%nat.
    frun_to 0x91330%Z. RDV V1552.
    frun_to 0x91340%Z. RDV V1552.
    frun_to 0x9137c%Z. RDQ VAR1 36%Z.
    frun_to 0x913ac%Z. RDRF RFQ RFF 36%Z.
    frun_to 0x913cc%Z. STRF RFQ 36%Z. RFNEXT RFQ ERF RFF 36%Z 36%nat.
    frun_to 0x913dc%Z. RDV V1552.
    frun_to 0x913ec%Z. RDV V1552.
    frun_to 0x91428%Z. RDQ VAR1 37%Z.
    frun_to 0x91458%Z. RDRF RFQ RFF 37%Z.
    frun_to 0x91478%Z. STRF RFQ 37%Z. RFNEXT RFQ ERF RFF 37%Z 37%nat.
    frun_to 0x91488%Z. RDV V1552.
    frun_to 0x91498%Z. RDV V1552.
    frun_to 0x914d4%Z. RDQ VAR1 38%Z.
    frun_to 0x91504%Z. RDRF RFQ RFF 38%Z.
    frun_to 0x91524%Z. STRF RFQ 38%Z. RFNEXT RFQ ERF RFF 38%Z 38%nat.
    frun_to 0x91534%Z. RDV V1552.
    frun_to 0x91544%Z. RDV V1552.
    frun_to 0x91580%Z. RDQ VAR1 39%Z.
    frun_to 0x915b0%Z. RDRF RFQ RFF 39%Z.
    frun_to 0x915d0%Z. STRF RFQ 39%Z. RFNEXT RFQ ERF RFF 39%Z 39%nat.
    frun_to 0x915e0%Z. RDV V1552.
    frun_to 0x915f0%Z. RDV V1552.
    frun_to 0x9162c%Z. RDQ VAR1 40%Z.
    frun_to 0x9165c%Z. RDRF RFQ RFF 40%Z.
    frun_to 0x9167c%Z. STRF RFQ 40%Z. RFNEXT RFQ ERF RFF 40%Z 40%nat.
    frun_to 0x9168c%Z. RDV V1552.
    frun_to 0x9169c%Z. RDV V1552.
    frun_to 0x916d8%Z. RDQ VAR1 41%Z.
    frun_to 0x91708%Z. RDRF RFQ RFF 41%Z.
    frun_to 0x91728%Z. STRF RFQ 41%Z. RFNEXT RFQ ERF RFF 41%Z 41%nat.
    frun_to 0x91738%Z. RDV V1552.
    frun_to 0x91748%Z. RDV V1552.
    frun_to 0x91784%Z. RDQ VAR1 42%Z.
    frun_to 0x917b4%Z. RDRF RFQ RFF 42%Z.
    frun_to 0x917d4%Z. STRF RFQ 42%Z. RFNEXT RFQ ERF RFF 42%Z 42%nat.
    frun_to 0x917e4%Z. RDV V1552.
    frun_to 0x917f4%Z. RDV V1552.
    frun_to 0x91830%Z. RDQ VAR1 43%Z.
    frun_to 0x91860%Z. RDRF RFQ RFF 43%Z.
    frun_to 0x91880%Z. STRF RFQ 43%Z. RFNEXT RFQ ERF RFF 43%Z 43%nat.
    frun_to 0x91890%Z. RDV V1552.
    frun_to 0x918a0%Z. RDV V1552.
    frun_to 0x918dc%Z. RDQ VAR1 44%Z.
    frun_to 0x9190c%Z. RDRF RFQ RFF 44%Z.
    frun_to 0x9192c%Z. STRF RFQ 44%Z. RFNEXT RFQ ERF RFF 44%Z 44%nat.
    frun_to 0x9193c%Z. RDV V1552.
    frun_to 0x9194c%Z. RDV V1552.
    frun_to 0x91988%Z. RDQ VAR1 45%Z.
    frun_to 0x919b8%Z. RDRF RFQ RFF 45%Z.
    frun_to 0x919d8%Z. STRF RFQ 45%Z. RFNEXT RFQ ERF RFF 45%Z 45%nat.
    frun_to 0x919e8%Z. RDV V1552.
    frun_to 0x919f8%Z. RDV V1552.
    frun_to 0x91a34%Z. RDQ VAR1 46%Z.
    frun_to 0x91a64%Z. RDRF RFQ RFF 46%Z.
    frun_to 0x91a84%Z. STRF RFQ 46%Z. RFNEXT RFQ ERF RFF 46%Z 46%nat.
    frun_to 0x91a94%Z. RDV V1552.
    frun_to 0x91aa4%Z. RDV V1552.
    frun_to 0x91ae0%Z. RDQ VAR1 47%Z.
    frun_to 0x91b10%Z. RDRF RFQ RFF 47%Z.
    frun_to 0x91b30%Z. STRF RFQ 47%Z. RFNEXT RFQ ERF RFF 47%Z 47%nat.
    frun_to 0x91b40%Z. RDV V1552.
    frun_to 0x91b50%Z. RDV V1552.
    frun_to 0x91b8c%Z. RDQ VAR1 48%Z.
    frun_to 0x91bbc%Z. RDRF RFQ RFF 48%Z.
    frun_to 0x91bdc%Z. STRF RFQ 48%Z. RFNEXT RFQ ERF RFF 48%Z 48%nat.
    frun_to 0x91bec%Z. RDV V1552.
    frun_to 0x91bfc%Z. RDV V1552.
    frun_to 0x91c38%Z. RDQ VAR1 49%Z.
    frun_to 0x91c68%Z. RDRF RFQ RFF 49%Z.
    frun_to 0x91c84%Z. STRF RFQ 49%Z. RFNEXT RFQ ERF RFF 49%Z 49%nat.
    frun_to 0x91d9c%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk' _ _) => enter_with (K mm rfk' _ _ _ _ _ _) end end;
      [ st_eq | exact RFQ | exact ERF | eapply RFrow_weaken; [exact RFF| lia] | assumption | exact MU | exact WM ].
  Qed.
End FR.
End ACeilS1.
