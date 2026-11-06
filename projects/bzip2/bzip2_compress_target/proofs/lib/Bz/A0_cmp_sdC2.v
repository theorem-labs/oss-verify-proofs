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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_sdB1 A0_cmp_sdB2 A0_cmp_sdB3 A0_cmp_sdB4 A0_cmp_sdB5 A0_cmp_sdB6 A0_cmp_sdC1.

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

Section SDC2.
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
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.
  (* [comment removed for export] *)
  Variables (sc gs : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs)%Z. Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i < gs + 50)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).
  Notation MT := (A1 + 2 * gs)%Z. Notation CR := (E + 39256 + 1032 * sel)%Z. Notation LR := (E + 37708 + 258 * sel)%Z.
  (* [comment removed for export] *)
  Variable xt1 : word.
  Notation RG a1 a2 a6 a7 t0 :=
    (RD (Z_to_bv 64 15) t0 xt1 (Z_to_bv 64 (E + 39256)) (Z_to_bv 64 MT) a1 a2 (Z_to_bv 64 (gs + 50)) (Z_to_bv 64 LR) (Z_to_bv 64 CR) a6 a7
        (Z_to_bv 64 gs) (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)).
  (* [comment removed for export] *)
  Notation RY t0 t1 a0 a1 a2 a3 a4 a5 a6 a7 gs sc :=
    (RD (Z_to_bv 64 15) t0 t1 (Z_to_bv 64 (E + 39256)) a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 gs) (Z_to_bv 64 sc) (Z_to_bv 64 258) (Z_to_bv 64 1032) (Z_to_bv 64 8)).
  (* [comment removed for export] *)
  Notation SXB L := (SX L HA HG HNS LENF CODF SELF ZB1 sc gs Hsc Hgs HgsE MTFV xt1).

  (* [comment removed for export] *)
  Lemma A0_fast50 : forall (SHs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 a1 a2 a4 a5 a6 : word),
    saddr (E + 1704 + sc) SHs ->
    bw_ok b -> (bw_numZ (sm_put_syms 50 b LENA CODA ARR1 sel gs) <= LIM)%Z -> MD H bs b m ->
    (forall m' (t0' a0' a1' a2' a4' a5' a6' a7' : word), MD H bs (sm_put_syms 50 b LENA CODA ARR1 sel gs) m' -> bw_ok (sm_put_syms 50 b LENA CODA ARR1 sel gs) ->
        evt a0segs Q (MS (RY t0' xt1 a0' a1' a2' (Z_to_bv 64 (gs + 50)) a4' a5' a6' a7' gs sc) F (Z_to_bv 64 0x9426c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RY (Z_to_bv 64 SHs) xt1 a0 a1 a2 (Z_to_bv 64 (gs + 50)) a4 a5 a6 (Z_to_bv 64 (E + 1704 + sc)) gs sc) F (Z_to_bv 64 0x90440) fc None m (seg_rom a0segs)).
  Proof using All.
    intros SHs H bs b m a0 a1 a2 a4 a5 a6 AS OK NL MEM K.
    pose proof (SELF sc Hsc) as [SD SR].
    (* [comment removed for export] *)
    set (b1 := bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 0))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 0)))).
    set (b9 := sm_put_syms 8 b1 LENA CODA ARR1 sel (gs + 1)).
    set (b17 := sm_put_syms 8 b9 LENA CODA ARR1 sel (gs + 9)).
    set (b25 := sm_put_syms 8 b17 LENA CODA ARR1 sel (gs + 17)).
    set (b33 := sm_put_syms 8 b25 LENA CODA ARR1 sel (gs + 25)).
    set (b41 := sm_put_syms 8 b33 LENA CODA ARR1 sel (gs + 33)).
    set (b48 := sm_put_syms 7 b41 LENA CODA ARR1 sel (gs + 41)).
    set (b49 := bsW b48 (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))).
    set (b50 := bsW b49 (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))).
    assert (E50 : sm_put_syms 50 b LENA CODA ARR1 sel gs = b50).
    { change 50%nat with (1 + 8 + 8 + 8 + 8 + 8 + 7 + 1 + 1)%nat. rewrite !put_syms_split. rewrite !put_syms_S, !put_syms_0.
      subst b50 b49 b48 b41 b33 b25 b17 b9 b1.
      replace (gs + Z.of_nat 1)%Z with (gs + 1)%Z by lia.
      replace (gs + Z.of_nat (1 + 8))%Z with (gs + 9)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8))%Z with (gs + 17)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8 + 8))%Z with (gs + 25)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8 + 8 + 8))%Z with (gs + 33)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8 + 8 + 8 + 8))%Z with (gs + 41)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8 + 8 + 8 + 8 + 7))%Z with (gs + 48)%Z by lia.
      replace (gs + Z.of_nat (1 + 8 + 8 + 8 + 8 + 8 + 7 + 1))%Z with (gs + 49)%Z by lia.
      replace (gs + 0)%Z with gs by lia. reflexivity. }
    rewrite E50 in NL, K.
    (* [comment removed for export] *)
    pose proof (bsW_NZM b49 (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) as Z49. unfold NZM in Z49. fold b50 in Z49.
    pose proof (bsW_NZM b48 (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))) as Z48. unfold NZM in Z48. fold b49 in Z48.
    pose proof (put_syms_NZM 8 b1 LENA CODA ARR1 sel (gs + 1)) as Z1. unfold NZM in Z1. fold b9 in Z1.
    pose proof (put_syms_NZM 8 b9 LENA CODA ARR1 sel (gs + 9)) as Z9. unfold NZM in Z9. fold b17 in Z9.
    pose proof (put_syms_NZM 8 b17 LENA CODA ARR1 sel (gs + 17)) as Z17. unfold NZM in Z17. fold b25 in Z17.
    pose proof (put_syms_NZM 8 b25 LENA CODA ARR1 sel (gs + 25)) as Z25. unfold NZM in Z25. fold b33 in Z25.
    pose proof (put_syms_NZM 8 b33 LENA CODA ARR1 sel (gs + 33)) as Z33. unfold NZM in Z33. fold b41 in Z33.
    pose proof (put_syms_NZM 7 b41 LENA CODA ARR1 sel (gs + 41)) as Z41. unfold NZM in Z41. fold b48 in Z41.
    (* [comment removed for export] *)
    eapply (SXB blk_0 SHs H bs b m _ _ _ _ _ _ AS); [exact OK| fold b1; lia| exact MEM|].
    fold b1. clear MEM. intros m1 a1_1 a2_1 a6_1 t0_1 MEM.
    assert (OK1 : bw_ok b1).
    { subst b1. pose proof (MTFV (gs + 0) ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia]. }
    (* [comment removed for export] *)
    eapply (SXB blocks_1_8 H bs b1 _ _ _ _ _); [exact OK1| fold b9; lia| exact MEM|].
    fold b9. clear MEM. intros m2 a1_2 a2_2 a6_2 t0_2 MEM OK9.
    (* [comment removed for export] *)
    eapply (SXB blocks_9_16 H bs b9 _ _ _ _ _); [exact OK9| fold b17; lia| exact MEM|].
    fold b17. clear MEM. intros m3 a1_3 a2_3 a6_3 t0_3 MEM OK17.
    (* [comment removed for export] *)
    eapply (SXB blocks_17_24 H bs b17 _ _ _ _ _); [exact OK17| fold b25; lia| exact MEM|].
    fold b25. clear MEM. intros m4 a1_4 a2_4 a6_4 t0_4 MEM OK25.
    (* [comment removed for export] *)
    eapply (SXB blocks_25_32 H bs b25 _ _ _ _ _); [exact OK25| fold b33; lia| exact MEM|].
    fold b33. clear MEM. intros m5 a1_5 a2_5 a6_5 t0_5 MEM OK33.
    (* [comment removed for export] *)
    eapply (SXB blocks_33_40 H bs b33 _ _ _ _ _); [exact OK33| fold b41; lia| exact MEM|].
    fold b41. clear MEM. intros m6 a1_6 a2_6 a6_6 t0_6 MEM OK41.
    (* [comment removed for export] *)
    eapply (SXB blocks_41_47 H bs b41 _ _ _ _ _); [exact OK41| fold b48; lia| exact MEM|].
    fold b48. clear MEM. intros m7 a1_7 a2_7 a6_7 t0_7 MEM OK48.
    (* [comment removed for export] *)
    eapply (SXB blk_48 H bs b48 _ _ _ _ _); [exact OK48| fold b49; lia| exact MEM|].
    fold b49. clear MEM. intros m8 a1_8 a2_8 a7_8 t0_8 MEM.
    assert (OK49 : bw_ok b49).
    { subst b49. pose proof (MTFV (gs + 48) ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK48| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia]. }
    (* [comment removed for export] *)
    eapply (SXB blk_49 H bs b49 _ _ _ _ _); [exact OK49| fold b50; lia| exact MEM|].
    fold b50. clear MEM. intros m9 a0_9 a1_9 a2_9 a4_9 a5_9 a6_9 MEM.
    eapply K; [exact MEM|].
    subst b50. pose proof (MTFV (gs + 49) ltac:(lia)) as MV. apply bw_ok_bsW; [exact OK49| pose proof (LENF sel _ ltac:(lia) MV); lia| pose proof (CODF sel _ ltac:(lia) MV); lia].
  Qed.
End SDC2.
End ACeilS1.
