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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCRebuildF CmpMem CmpCut CmpCutSM CmpCutSmA CmpCutSmB BzCFactsSmA BzCFactsSmB CmpSmKit CmpFsKit CmpHmKit.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import AsanKit AsanCut.
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
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE CO : Z).
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
    end; zb_fold_lits.
  Ltac lstep := zstep; bzl.
  Ltac fstep := AsanKit.a_zstep_nofb; bzl; AsanKit.a_try_lit_branch.
  Ltac frun_to p := first [ AsanKit.a_at_pc p | AsanKit.a_pc_is_lit; fstep; frun_to p | fail 1 "frun_to: stuck before" p ].
  Notation Wrf := [(E + 45448, E + 51640)]%Z.
  (* [comment removed for export] *)
  Ltac RDQ VAR1 k :=
    lazymatch goal with MU' : munch _ _ ?mm |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      let AR1v := fresh "AR1v" in let RD := fresh "RD" in
      pose proof (VAR1 mm MU') as AR1v;
      pose proof (zb8_read2 a0segs mm A1 arr1 ARR1_SIZE (2 * (gs + k)) _ AR1v ltac:(lia) ltac:(lia) ZB ltac:(unfold wa; f_equal; lia)) as RD;
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
    pose proof (ovw_read a0segs mm (E + 45448) rfk (jseg J 45448 6192) 1548 (258 * bt + q k) _ RFQ ltac:(lia) (proj1 Fk) ltac:(unfold wa; f_equal; lia)) as RD;
    lstep; clear RD; rewrite (sx32_of_Z (zget rfk (258 * bt + q k))) by (change (2^31)%Z with 2147483648%Z; lia) end end.
  Ltac STRF RFQ k :=
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk _ _) =>
    pose proof (u32arr_store_ok a0segs mm (E + 45448) _ (258 * bt + q k) _ RFQ ltac:(rewrite ovw_length_nat; lia) ltac:(unfold wa; f_equal; lia)) as SO;
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
  Lemma A0_fr1 : forall (m me : word -> option byte) (rfk : zarr) (xra xt0 xt1 xa0 xa1 xa3 xa5 xa6 xa7 : word),
    u32arr a0segs m (E + 45448) (ovw rfk (jseg J 45448 6192) 1548) ->
    rfk = sm_rfreq_inc 0 rf0 arr1 bt gs -> RFrow rfk bt A (B + 0) ->
    mem_inv a0segs m -> munch Wrf me m -> wmono a0segs me m ->
    (forall m', munch Wrf me m' -> u8arr a0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW a0segs Wrf me A1 (A1 + ARR1_SIZE) -> shzW a0segs Wrf me E (E + ESTATE_SIZE) ->
    (forall m' (rfk' : zarr) (yra yt0 yt1 ya1 ya3 ya5 ya6 ya7 : word),
      u32arr a0segs m' (E + 45448) (ovw rfk' (jseg J 45448 6192) 1548) ->
      rfk' = sm_rfreq_inc 17 rf0 arr1 bt gs -> RFrow rfk' bt A (B + 17) ->
      mem_inv a0segs m' -> munch Wrf me m' -> wmono a0segs me m' ->
      evt a0segs Q (MS (mkR yra (Z_to_bv 64 (P)) gp tp yt0 yt1 (Z_to_bv 64 (CO)) s0 (Z_to_bv 64 (P)) (Z_to_bv 64 (A1 + 2 * gs)) ya1 (Z_to_bv 64 (bc)) ya3 (Z_to_bv 64 (E + 1032 * bt + 45448)) ya5 ya6 ya7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
           F (Z_to_bv 64 0x8cfa0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR xra (Z_to_bv 64 (P)) gp tp xt0 xt1 (Z_to_bv 64 (CO)) s0 (Z_to_bv 64 (P)) xa0 xa1 (Z_to_bv 64 (bc)) xa3 (Z_to_bv 64 (1032 * bt)) xa5 xa6 xa7 (Z_to_bv 64 (49)) (Z_to_bv 64 (E + 37708)) (Z_to_bv 64 (2147450880)) (Z_to_bv 64 (nSel)) (Z_to_bv 64 (1)) (Z_to_bv 64 (A)) (Z_to_bv 64 (A1)) (Z_to_bv 64 (SHE + 83)) (Z_to_bv 64 (nG)) (Z_to_bv 64 (E + 668)) (Z_to_bv 64 (E + 45448)) (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 (gs)) (Z_to_bv 64 (gs + 49)))
         F (Z_to_bv 64 0x8cb10) fc None m (seg_rom a0segs)).
  Proof.
    intros m me rfk xra xt0 xt1 xa0 xa1 xa3 xa5 xa6 xa7 RFQ ERF RFF MI MU WM VAR1 SHa SHe K.
    openCX. try clear ME MA1 MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rfk (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    frun_to 0x8cb2c%Z. RDQ VAR1 0%Z.
    frun_to 0x8cb50%Z. RDRF RFQ RFF 0%Z.
    frun_to 0x8cb58%Z. STRF RFQ 0%Z. RFNEXT RFQ ERF RFF 0%Z 0%nat.
    frun_to 0x8cb74%Z. RDQ VAR1 1%Z.
    frun_to 0x8cb98%Z. RDRF RFQ RFF 1%Z.
    frun_to 0x8cba0%Z. STRF RFQ 1%Z. RFNEXT RFQ ERF RFF 1%Z 1%nat.
    frun_to 0x8cbbc%Z. RDQ VAR1 2%Z.
    frun_to 0x8cbdc%Z. RDRF RFQ RFF 2%Z.
    frun_to 0x8cbe4%Z. STRF RFQ 2%Z. RFNEXT RFQ ERF RFF 2%Z 2%nat.
    frun_to 0x8cc00%Z. RDQ VAR1 3%Z.
    frun_to 0x8cc20%Z. RDRF RFQ RFF 3%Z.
    frun_to 0x8cc28%Z. STRF RFQ 3%Z. RFNEXT RFQ ERF RFF 3%Z 3%nat.
    frun_to 0x8cc44%Z. RDQ VAR1 4%Z.
    frun_to 0x8cc64%Z. RDRF RFQ RFF 4%Z.
    frun_to 0x8cc6c%Z. STRF RFQ 4%Z. RFNEXT RFQ ERF RFF 4%Z 4%nat.
    frun_to 0x8cc88%Z. RDQ VAR1 5%Z.
    frun_to 0x8cca8%Z. RDRF RFQ RFF 5%Z.
    frun_to 0x8ccb0%Z. STRF RFQ 5%Z. RFNEXT RFQ ERF RFF 5%Z 5%nat.
    frun_to 0x8cccc%Z. RDQ VAR1 6%Z.
    frun_to 0x8ccec%Z. RDRF RFQ RFF 6%Z.
    frun_to 0x8ccf4%Z. STRF RFQ 6%Z. RFNEXT RFQ ERF RFF 6%Z 6%nat.
    frun_to 0x8cd10%Z. RDQ VAR1 7%Z.
    frun_to 0x8cd30%Z. RDRF RFQ RFF 7%Z.
    frun_to 0x8cd38%Z. STRF RFQ 7%Z. RFNEXT RFQ ERF RFF 7%Z 7%nat.
    frun_to 0x8cd54%Z. RDQ VAR1 8%Z.
    frun_to 0x8cd74%Z. RDRF RFQ RFF 8%Z.
    frun_to 0x8cd7c%Z. STRF RFQ 8%Z. RFNEXT RFQ ERF RFF 8%Z 8%nat.
    frun_to 0x8cd98%Z. RDQ VAR1 9%Z.
    frun_to 0x8cdb8%Z. RDRF RFQ RFF 9%Z.
    frun_to 0x8cdc0%Z. STRF RFQ 9%Z. RFNEXT RFQ ERF RFF 9%Z 9%nat.
    frun_to 0x8cddc%Z. RDQ VAR1 10%Z.
    frun_to 0x8cdfc%Z. RDRF RFQ RFF 10%Z.
    frun_to 0x8ce04%Z. STRF RFQ 10%Z. RFNEXT RFQ ERF RFF 10%Z 10%nat.
    frun_to 0x8ce20%Z. RDQ VAR1 11%Z.
    frun_to 0x8ce40%Z. RDRF RFQ RFF 11%Z.
    frun_to 0x8ce48%Z. STRF RFQ 11%Z. RFNEXT RFQ ERF RFF 11%Z 11%nat.
    frun_to 0x8ce64%Z. RDQ VAR1 12%Z.
    frun_to 0x8ce84%Z. RDRF RFQ RFF 12%Z.
    frun_to 0x8ce8c%Z. STRF RFQ 12%Z. RFNEXT RFQ ERF RFF 12%Z 12%nat.
    frun_to 0x8cea8%Z. RDQ VAR1 13%Z.
    frun_to 0x8cec8%Z. RDRF RFQ RFF 13%Z.
    frun_to 0x8ced0%Z. STRF RFQ 13%Z. RFNEXT RFQ ERF RFF 13%Z 13%nat.
    frun_to 0x8ceec%Z. RDQ VAR1 14%Z.
    frun_to 0x8cf0c%Z. RDRF RFQ RFF 14%Z.
    frun_to 0x8cf14%Z. STRF RFQ 14%Z. RFNEXT RFQ ERF RFF 14%Z 14%nat.
    frun_to 0x8cf30%Z. RDQ VAR1 15%Z.
    frun_to 0x8cf50%Z. RDRF RFQ RFF 15%Z.
    frun_to 0x8cf58%Z. STRF RFQ 15%Z. RFNEXT RFQ ERF RFF 15%Z 15%nat.
    frun_to 0x8cf74%Z. RDQ VAR1 16%Z.
    frun_to 0x8cf94%Z. RDRF RFQ RFF 16%Z.
    frun_to 0x8cf9c%Z. STRF RFQ 16%Z. RFNEXT RFQ ERF RFF 16%Z 16%nat.
    frun_to 0x8cfa0%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk' _ _) => enter_with (K mm rfk' _ _ _ _ _ _ _ _) end end;
      [ st_eq | exact RFQ | exact ERF | eapply RFrow_weaken; [exact RFF| lia] | assumption | exact MU | exact WM ].
  Qed.
End FR.
End ACeilS1.
