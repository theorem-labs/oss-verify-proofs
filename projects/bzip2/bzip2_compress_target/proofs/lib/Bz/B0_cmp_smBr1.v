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
  Lemma B0_fr1 : forall (m me : word -> option byte) (rfk : zarr) (xa0 xa2 xa3 xa5 xa7 : word),
    u32arr b0segs m (E + 45448) (ovw rfk (jseg J 45448 6192) 1548) ->
    rfk = sm_rfreq_inc 0 rf0 arr1 bt gs -> RFrow rfk bt A (B + 0) ->
    mem_inv b0segs m -> munch Wrf me m -> wmono b0segs me m ->
    (forall m', munch Wrf me m' -> u8arr b0segs m' A1 (zb8 arr1 ARR1_SIZE)) ->
    shzW b0segs Wrf me A1 (A1 + ARR1_SIZE) -> shzW b0segs Wrf me E (E + ESTATE_SIZE) ->
    frdW b0segs Wrf me (P + 1504) [C8 (Z_to_bv 64 (E + 45448))] ->
    frdW b0segs Wrf me (P + 1544) [C8 (Z_to_bv 64 (1))] ->
    frdW b0segs Wrf me (P + 1552) [C8 (Z_to_bv 64 (A1))] ->
    (forall m' (rfk' : zarr) (ya0 ya2 ya5 : word),
      u32arr b0segs m' (E + 45448) (ovw rfk' (jseg J 45448 6192) 1548) ->
      rfk' = sm_rfreq_inc 17 rf0 arr1 bt gs -> RFrow rfk' bt A (B + 17) ->
      mem_inv b0segs m' -> munch Wrf me m' -> wmono b0segs me m' ->
      evt b0segs Q (MS (mkR ra (Z_to_bv 64 (P)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (P)) ya0 (Z_to_bv 64 (E + 1032 * bt + 45448)) ya2 (Z_to_bv 64 (gs + 17)) a4 ya5 (Z_to_bv 64 (gs)) (Z_to_bv 64 ((-1) * E + (-1032) * bt + 18446744073709506167)) (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
           F (Z_to_bv 64 0x90660) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (mkR ra (Z_to_bv 64 (P)) gp tp t0 t1 t2 s0 (Z_to_bv 64 (P)) xa0 (Z_to_bv 64 (1032 * bt)) xa2 xa3 a4 xa5 (Z_to_bv 64 (gs)) xa7 (Z_to_bv 64 (2147450880)) s3 (Z_to_bv 64 (258)) (Z_to_bv 64 (1032)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
         F (Z_to_bv 64 0x8fadc) fc None m (seg_rom b0segs)).
  Proof.
    intros m me rfk xa0 xa2 xa3 xa5 xa7 RFQ ERF RFF MI MU WM VAR1 SHa SHe V1504 V1544 V1552 K.
    openCX. try clear MA2 MF Mb Mf. clear XA20 XA21 XF0 XF1 Xb0 Xb1 Xf0 Xf1 LJb. unfold ESTATE_SIZE in SHe. assert (HAd : A = (e_nInUse e + 2)%Z) by reflexivity.
    pose proof (jseg_length J 45448 6192 ltac:(lia) ltac:(lia) ltac:(lia)) as LJ8. pose proof (ovw_length rfk (jseg J 45448 6192) 1548 ltac:(lia)) as LRF.
    frun_to 0x8fae0%Z. RDV V1552.
    frun_to 0x8faec%Z. RDV V1544.
    frun_to 0x8faf8%Z. RDV V1552.
    frun_to 0x8fb14%Z. RDV V1552.
    frun_to 0x8fb40%Z. RDQ VAR1 0%Z.
    frun_to 0x8fb4c%Z. RDV V1504.
    frun_to 0x8fb7c%Z. RDRF RFQ RFF 0%Z.
    frun_to 0x8fb9c%Z. STRF RFQ 0%Z. RFNEXT RFQ ERF RFF 0%Z 0%nat.
    frun_to 0x8fbac%Z. RDV V1552.
    frun_to 0x8fbbc%Z. RDV V1552.
    frun_to 0x8fbf8%Z. RDQ VAR1 1%Z.
    frun_to 0x8fc28%Z. RDRF RFQ RFF 1%Z.
    frun_to 0x8fc48%Z. STRF RFQ 1%Z. RFNEXT RFQ ERF RFF 1%Z 1%nat.
    frun_to 0x8fc58%Z. RDV V1552.
    frun_to 0x8fc68%Z. RDV V1552.
    frun_to 0x8fca4%Z. RDQ VAR1 2%Z.
    frun_to 0x8fcd4%Z. RDRF RFQ RFF 2%Z.
    frun_to 0x8fcf4%Z. STRF RFQ 2%Z. RFNEXT RFQ ERF RFF 2%Z 2%nat.
    frun_to 0x8fd04%Z. RDV V1552.
    frun_to 0x8fd14%Z. RDV V1552.
    frun_to 0x8fd50%Z. RDQ VAR1 3%Z.
    frun_to 0x8fd80%Z. RDRF RFQ RFF 3%Z.
    frun_to 0x8fda0%Z. STRF RFQ 3%Z. RFNEXT RFQ ERF RFF 3%Z 3%nat.
    frun_to 0x8fdb0%Z. RDV V1552.
    frun_to 0x8fdc0%Z. RDV V1552.
    frun_to 0x8fdfc%Z. RDQ VAR1 4%Z.
    frun_to 0x8fe2c%Z. RDRF RFQ RFF 4%Z.
    frun_to 0x8fe4c%Z. STRF RFQ 4%Z. RFNEXT RFQ ERF RFF 4%Z 4%nat.
    frun_to 0x8fe5c%Z. RDV V1552.
    frun_to 0x8fe6c%Z. RDV V1552.
    frun_to 0x8fea8%Z. RDQ VAR1 5%Z.
    frun_to 0x8fed8%Z. RDRF RFQ RFF 5%Z.
    frun_to 0x8fef8%Z. STRF RFQ 5%Z. RFNEXT RFQ ERF RFF 5%Z 5%nat.
    frun_to 0x8ff08%Z. RDV V1552.
    frun_to 0x8ff18%Z. RDV V1552.
    frun_to 0x8ff54%Z. RDQ VAR1 6%Z.
    frun_to 0x8ff84%Z. RDRF RFQ RFF 6%Z.
    frun_to 0x8ffa4%Z. STRF RFQ 6%Z. RFNEXT RFQ ERF RFF 6%Z 6%nat.
    frun_to 0x8ffb4%Z. RDV V1552.
    frun_to 0x8ffc4%Z. RDV V1552.
    frun_to 0x90000%Z. RDQ VAR1 7%Z.
    frun_to 0x90030%Z. RDRF RFQ RFF 7%Z.
    frun_to 0x90050%Z. STRF RFQ 7%Z. RFNEXT RFQ ERF RFF 7%Z 7%nat.
    frun_to 0x90060%Z. RDV V1552.
    frun_to 0x90070%Z. RDV V1552.
    frun_to 0x900ac%Z. RDQ VAR1 8%Z.
    frun_to 0x900dc%Z. RDRF RFQ RFF 8%Z.
    frun_to 0x900fc%Z. STRF RFQ 8%Z. RFNEXT RFQ ERF RFF 8%Z 8%nat.
    frun_to 0x9010c%Z. RDV V1552.
    frun_to 0x9011c%Z. RDV V1552.
    frun_to 0x90158%Z. RDQ VAR1 9%Z.
    frun_to 0x90188%Z. RDRF RFQ RFF 9%Z.
    frun_to 0x901a8%Z. STRF RFQ 9%Z. RFNEXT RFQ ERF RFF 9%Z 9%nat.
    frun_to 0x901b8%Z. RDV V1552.
    frun_to 0x901c8%Z. RDV V1552.
    frun_to 0x90204%Z. RDQ VAR1 10%Z.
    frun_to 0x90234%Z. RDRF RFQ RFF 10%Z.
    frun_to 0x90254%Z. STRF RFQ 10%Z. RFNEXT RFQ ERF RFF 10%Z 10%nat.
    frun_to 0x90264%Z. RDV V1552.
    frun_to 0x90274%Z. RDV V1552.
    frun_to 0x902b0%Z. RDQ VAR1 11%Z.
    frun_to 0x902e0%Z. RDRF RFQ RFF 11%Z.
    frun_to 0x90300%Z. STRF RFQ 11%Z. RFNEXT RFQ ERF RFF 11%Z 11%nat.
    frun_to 0x90310%Z. RDV V1552.
    frun_to 0x90320%Z. RDV V1552.
    frun_to 0x9035c%Z. RDQ VAR1 12%Z.
    frun_to 0x9038c%Z. RDRF RFQ RFF 12%Z.
    frun_to 0x903ac%Z. STRF RFQ 12%Z. RFNEXT RFQ ERF RFF 12%Z 12%nat.
    frun_to 0x903bc%Z. RDV V1552.
    frun_to 0x903cc%Z. RDV V1552.
    frun_to 0x90408%Z. RDQ VAR1 13%Z.
    frun_to 0x90438%Z. RDRF RFQ RFF 13%Z.
    frun_to 0x90458%Z. STRF RFQ 13%Z. RFNEXT RFQ ERF RFF 13%Z 13%nat.
    frun_to 0x90468%Z. RDV V1552.
    frun_to 0x90478%Z. RDV V1552.
    frun_to 0x904b4%Z. RDQ VAR1 14%Z.
    frun_to 0x904e4%Z. RDRF RFQ RFF 14%Z.
    frun_to 0x90504%Z. STRF RFQ 14%Z. RFNEXT RFQ ERF RFF 14%Z 14%nat.
    frun_to 0x90514%Z. RDV V1552.
    frun_to 0x90524%Z. RDV V1552.
    frun_to 0x90560%Z. RDQ VAR1 15%Z.
    frun_to 0x90590%Z. RDRF RFQ RFF 15%Z.
    frun_to 0x905b0%Z. STRF RFQ 15%Z. RFNEXT RFQ ERF RFF 15%Z 15%nat.
    frun_to 0x905c0%Z. RDV V1552.
    frun_to 0x905d0%Z. RDV V1552.
    frun_to 0x9060c%Z. RDQ VAR1 16%Z.
    frun_to 0x9063c%Z. RDRF RFQ RFF 16%Z.
    frun_to 0x9065c%Z. STRF RFQ 16%Z. RFNEXT RFQ ERF RFF 16%Z 16%nat.
    frun_to 0x90660%Z.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch type of RFQ with u32arr _ _ _ (ovw ?rfk' _ _) => enter_with (K mm rfk' _ _ _) end end;
      [ st_eq | exact RFQ | exact ERF | eapply RFrow_weaken; [exact RFF| lia] | assumption | exact MU | exact WM ].
  Qed.
End FR.
End ACeilS1.
