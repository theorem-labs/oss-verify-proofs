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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit BzCSmF1.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_sdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_sdD A0_cmp_sdE A0_cmp_sdF A0_cmp_sdC3.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Ltac openCX_d CX SEP CEP :=
  let XF0 := ident:(XF0) in let XF1 := ident:(XF1) in let Xb0 := ident:(Xb0) in let Xb1 := ident:(Xb1) in
  let Xf0 := ident:(Xf0) in let Xf1 := ident:(Xf1) in let ME := ident:(ME) in let MA1 := ident:(MA1) in let MA2 := ident:(MA2) in let MF := ident:(MF) in
  let Mb := ident:(Mb) in let Mf := ident:(Mf) in let LJb := ident:(LJb) in
  let H := fresh "CXL" in pose proof CX as H; bz_ceil; bz_params; unfold cctx_ok, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE, CEIL in H; cbv zeta in H;
  let U := fresh "CEPL" in pose proof CEP as U; unfold CEIL in U;
  cps_destruct H as (?XE0 & ?XE1 & ?XA10 & ?XA11 & ?XA20 & ?XA21 & ?XF0 & ?XF1 & ?Xb0 & ?Xb1 & ?Xf0 & ?Xf1 & ?ME & ?MA1 & ?MA2 & ?MF & ?Mb & ?Mf & ?LJ & ?LJb);
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 ME MA1 MA2 MF Mb Mf LJb;
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDZ.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z) (w16 w24 w208 : word).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Notation INUA := (e_inUse e). Notation SLMA := (e_selectorMtf e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1616 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (A nG nSel : Z) (m0 : word -> option byte).
  Notation WD := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1336, P + 1440); (P + 1472, P + 1488)]%Z.
  Hypothesis VW : sd_vw cx e A nG P FB SHF SHE w16 w24 w208 m0.
  Hypothesis SHe : shzW a0segs WD m0 E (E + ESTATE_SIZE).
  Hypothesis SH1 : shzW a0segs WD m0 A1 (A1 + ARR1_SIZE).
  Hypothesis SH2 : shzW a0segs WD m0 A2 (A2 + ARR2_SIZE).
  Notation MD H i16 b m := (MA3 cx g e A nG nSel P m0 H i16 b m).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (SHE + 14)) cSB (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640))
         (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 10)) s10 (Z_to_bv 64 (SHE + 80)) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation SX L := (L cx g e Q gp tp s0 F fc P SHE FB SHF w16 w24 w208 CX SEP Gmtf Gbs Gzb Hnb CEP PHI AE LIM HLIM A nG nSel m0 VW SHe SH1 SH2).
  (* [comment removed for export] *)
  Notation FLX L f H bs b m := (SX L f H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

  (* [comment removed for export] *)
  Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z.
  Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Variable NM : Z. Hypothesis HNM : (1 <= NM)%Z. Hypothesis HNMe : e_nMTF e = NM. Hypothesis HNMA : (2 * (NM + 50) <= ARR1_SIZE)%Z.
  Hypothesis ZB1 : zbok ARR1.
  Hypothesis MTFVN : forall i, (0 <= i < NM)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Hypothesis INUF : forall k, (0 <= k < 256)%Z -> zdef (e_inUse e) k = true /\ (0 <= zget (e_inUse e) k < 256)%Z.
  Hypothesis SLMF : forall i, (0 <= i < nSel)%Z -> zdef (e_selectorMtf e) i = true /\ (0 <= zget (e_selectorMtf e) i < nG)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SCN : forall b, snd (sm_put_data (Z.to_nat (NM + 1)) b LENA CODA ARR1 SELA NM 0 0) = nSel.
  (* [comment removed for export] *)
  Variable in160 : zarr.
  Hypothesis OK0 : bw_ok (e_bw e).

  (* [comment removed for export] *)
  Definition IN16 : zarr := sm_in16 16 in160 (e_inUse e) 0.
  Definition BA : bw := sm_put_in16 16 (e_bw e) IN16 0.
  Definition BB : bw := sm_put_inuse 16 BA IN16 (e_inUse e) 0.
  Definition BC3 : bw := bsW BB 3 nG.
  Definition BC : bw := bsW BC3 15 nSel.
  Definition BD : bw := sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0.
  Definition BE : bw := sm_put_lens (Z.to_nat nG) BD LENA A 0.
  Definition RF : bw * Z := sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0.
  Hypothesis ELIM : bw_numZ (fst RF) = LIM.

  Lemma IN16R : forall k, (0 <= k < 16)%Z -> zget IN16 k = ROW16 (e_inUse e) k.
  Proof using. intros k Hk. unfold IN16. apply smD_in16_row. exact Hk. Qed.

  (* [comment removed for export] *)
  Lemma NZ_chain : (bw_numZ (e_bw e) <= bw_numZ BA /\ bw_numZ BA <= bw_numZ BB /\ bw_numZ BB <= bw_numZ BC3 /\ bw_numZ BC3 <= bw_numZ BC /\
                    bw_numZ BC <= bw_numZ BD /\ bw_numZ BD <= bw_numZ BE /\ bw_numZ BE <= bw_numZ (fst RF))%Z.
  Proof using.
    repeat split.
    - exact (put_in16_NZM 16 (e_bw e) IN16 0).
    - exact (put_inuse_NZM 16 BA IN16 (e_inUse e) 0).
    - exact (bsW_NZM BB 3 nG).
    - exact (bsW_NZM BC3 15 nSel).
    - exact (put_sels_NZM (Z.to_nat nSel) BC (e_selectorMtf e) 0).
    - exact (put_lens_NZM (Z.to_nat nG) BD LENA A 0).
    - exact (put_data_NZM (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0).
  Qed.
  (* [comment removed for export] *)
  Lemma BB_unfold : sm_put_inuse 16 BA IN16 (e_inUse e) 0 = BB.
  Proof using. unfold BB. reflexivity. Qed.
  #[local] Opaque IN16 BA BB BC3 BC BD BE RF.

  (* [comment removed for export] *)
  Ltac curH k :=
    lazymatch goal with
    | HH : rw_cells _ ?mm (P + 1336)%Z (C8 ?v1 :: C8 ?v2 :: C8 ?v3 :: C8 ?v4 :: _ :: C8 ?v6 :: C8 ?v7 :: _ :: C8 ?v9 :: C8 ?v10 :: _) |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        k (SDW v1 v2 v3 v4 v6 v7 v9 v10)
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_smD_seg : forall (H0 : sdw) (i16 : list byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 : word),
    w1360 H0 = Z_to_bv 64 nSel -> Z.of_nat (length i16) = 16%Z ->
    MD H0 i16 (e_bw e) m0 ->
    (forall m' (H' : sdw) (i16' : list byte) (ra' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' s10' t3' t4' t5' t6' : word),
        MD H' i16' (fst RF) m' -> Z.of_nat (length i16') = 16%Z -> bw_ok (fst RF) ->
        evt a0segs Q (MS (mkR ra' cP gp tp t0' t1' t2' s0 cP a0' a1' a2' a3' a4' a5' a6' a7' (Z_to_bv 64 SHF) (Z_to_bv 64 (SHE + 14)) cSB (Z_to_bv 64 (E + 644)) (Z_to_bv 64 (E + 640))
                              (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 10)) s10' (Z_to_bv 64 (SHE + 80)) t3' t4' t5' t6')
                          F (Z_to_bv 64 0x95440) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 cSB x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 (Z_to_bv 64 E))
                      F (Z_to_bv 64 0x8f4d8) fc None m0 (seg_rom a0segs)).
  Proof using All.
    intros H0 i16 ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x2 x3 x5 x6 x7 x8 x9 x10 x11 t3 t4 t5 HS0 Li16 MEM K.
    cps_pose NZ_chain as (Z0 & Z1 & Z2 & Z3 & Z4 & Z5 & Z6). pose proof HLIM as HLIM'. bz_params. rewrite <- ELIM in HLIM'.
    cps_pose OK0 as (OKb & OKl & OKn).
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    (* [comment removed for export] *)
    do 7 wstep.
    enter_with (SX A0_in16_outer INUF x2 x3 x5 x6 x7 x8 x9 x10 x11 t4 t5 16%nat 0%Z H0 i16 (e_bw e) m0 ra _ _ _ _ _); [st_eq| lia| lia| lia| exact Li16| intros; lia| closeMD|].
    clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m1 bs1 t0_1 t1_1 t2_1 a0_1 a6_1 a7_1 t3_1 MEM L1 ROWS1.
    (* [comment removed for export] *)
    enter_with (SX A0_pin16_pre INUF H0 bs1 (e_bw e) m1 ra _ _ _ _ _ _ _ _ _ _ x2 x3 x5 x6 x7 x8 x9 x10 x11 _ t4 t5); [st_eq| exact MEM|].
    clear MEM. intros m1' H1 t1_1' t2_1' a0_1' a2_1' HS1 MEM.
    enter_with (SX A0_pin16_loop INUF HG HNS 16%nat 0%Z IN16 H1 bs1 (e_bw e) m1' ra _ _ _ _ x10 _ t4 t5);
      [st_eq| lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OK0| change (sm_put_in16 16 (e_bw e) IN16 0) with BA; lia| exact MEM|].
    change (sm_put_in16 16 (e_bw e) IN16 0) with BA. clear MEM.
    intros m2 t1_2 t2_2 a0_2 MEM OKA.
    (* [comment removed for export] *)
    do 6 wstep.
    enter_with (SX A0_pinuse_outer INUF HG HNS 16%nat 0%Z IN16 H1 bs1 BA m2 ra _ _ _ _ _ _ x10 t5);
      [st_eq| lia| lia| lia| exact L1| exact ROWS1| exact IN16R| exact OKA| rewrite BB_unfold; lia| exact MEM|].
    rewrite BB_unfold. clear MEM.
    intros m3 t1_3 t2_3 t3_3 t4_3 a0_3 MEM OKB.
    (* [comment removed for export] *)
    eapply (SX A0_bsw3 HG HNS SLMF H1 bs1 BB m3 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [exact OKB| change (bsW BB 3 nG) with BC3; lia| exact MEM|].
    clear MEM. intros m4 a2_4 a4_4 bB1 EbB1 MEM.
    cps_pose OKB as (OKBb & OKBl & OKBn).
    cps_pose (bs_needw_post BS_FUEL BB OKB ltac:(change (8 * Z.of_nat BS_FUEL)%Z with 40%Z; lia)) as (OKB1 & MB1 & _). rewrite <- EbB1 in OKB1, MB1.
    pose proof (Z.mod_pos_bound (bw_live BB) 8 ltac:(lia)) as MB8.
    assert (OKC3 : bw_ok (bsW BB 3 nG)) by (apply bw_ok_bsW; [exact OKB| lia| lia]).
    assert (LC3 : bw_live (bsW BB 3 nG) = (bw_live bB1 + 3)%Z) by (unfold bsW; rewrite <- EbB1; reflexivity).
    (* [comment removed for export] *)
    eapply (SX A0_bsw15 HG HNS SLMF H1 bs1 (bsW BB 3 nG) (bw_live bB1) m4 _ _ _ _ _ _ _ _ _ _ _ _ _); [rewrite HS1; exact HS0| exact OKC3| exact LC3| cps_destruct OKB1 as (?&?&?); lia| change (bsW (bsW BB 3 nG) 15 nSel) with BC; lia| exact MEM|].
    change (bsW (bsW BB 3 nG) 15 nSel) with BC. clear MEM. intros m5 a0_5 a1_5 a3_5 a4_5 MEM OKC.
    cps_pose OKC as (OKCb & OKCl & OKCn). openMD MEM.
    (* [comment removed for export] *)
    wstep. wstep; if_cases Kz; zify_cond_z Kz; [exfalso; lia|].
    do 7 wstep.
    enter_with (SX A0_sels_outer HG HNS SLMF (Z.to_nat nSel) 0%Z H1 bs1 BC m5 ra _ _ _ _ _ _ x10 _ _ t5);
      [st_eq| lia| lia| lia| exact OKC| change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD; lia| closeMD|].
    change (sm_put_sels (Z.to_nat nSel) BC (e_selectorMtf e) 0) with BD. clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m6 t0_6 t1_6 t2_6 a0_6 a1_6 t3_6 MEM OKD.
    cps_pose OKD as (OKDb & OKDl & OKDn). openMD MEM.
    (* [comment removed for export] *)
    openVW VW. arun_to 0x8fe58%Z. closeVW. wstep. arun_to 0x8fe78%Z.
    curH ltac:(fun HH =>
      enter_with (SX A0_lens_outer HAe HA HG LENF (Z.to_nat nG) 0%Z HH bs1 BD _ ra _ _ _ _ _ x10 _ _);
        [st_eq| lia| lia| lia| exact OKD| change (sm_put_lens (Z.to_nat nG) BD LENA A 0) with BE; lia| closeMD|]).
    change (sm_put_lens (Z.to_nat nG) BD LENA A 0) with BE. clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m7 ra_7 a0_7 a1_7 a2_7 a3_7 a5_7 s10_7 t5_7 t6_7 MEM OKE.
    cps_pose OKE as (OKEb & OKEl & OKEn). openMD MEM. rewrite HNMe in EH2.
    (* [comment removed for export] *)
    openVW VW. arun_to 0x90374%Z. wstep.
    (* [comment removed for export] *)
    arun. closeVW. if_cases Kn; zify_cond_z Kn; [| exfalso; lia].
    (* [comment removed for export] *)
    arun_to 0x903b0%Z. (wstep; lit_store). rewrite <- HNMe in EH2.
    curH ltac:(fun HH =>
      enter_with (SX A0_data_loop HA HG HNS LENF CODF SELF ZB1 NM HNM HNMe HNMA MTFVN (Z.to_nat (NM + 1)) 0%Z 0%Z HH bs1 BE _ _ _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| rewrite SCN; lia| exact OKE| change (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0) with RF; lia| closeMD|]).
    change (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0) with RF. clear EH1 EH2 AR2 HI I16 MI MU WM.
    intros m8 s10v t0_8 a0_8 a1_8 a2_8 a3_8 a4_8 a5_8 a6_8 a7_8 MEM OKF.
    replace (snd RF) with nSel by (change RF with (sm_put_data (Z.to_nat (NM + 1)) BE LENA CODA ARR1 SELA NM 0 0); symmetry; apply SCN).
    openMD MEM.
    (* [comment removed for export] *)
    openVW VW. arun. if_cases Ke; zify_cond_z Ke; [| exfalso; lia]. arun_to 0x95440%Z. closeVW.
    curH ltac:(fun HH =>
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (K mm HH bs1 _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| closeMD| exact L1| exact OKF] end).
  Qed.
End SDZ.
End ACeilS1.
