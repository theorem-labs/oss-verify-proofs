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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzTac BzTac2 BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac CmpArith CmpArith2 BzCNumZ BzWalkArith2 BzWalkArith4 BzCLemmasSd BzCLemmasSd2 CmpFsKit CmpHmKit.
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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_smV.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.CmpArith2.CmpSdArith OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.A Require Import Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdV.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzCSmF1.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import B0_cmp_sdC2.


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
  clear XF0 XF1 Xb0 Xb1 Xf0 Xf1 MF Mb Mf LJb;
  let S := fresh "SP" in pose proof SEP as S; unfold cctx_sep, apart, ESTATE_SIZE, FTAB_WORDS, BZFILE_SIZE in S; cbv zeta in S;
  cps_destruct S as (?AEA1 & ?AEA2 & _ & _ & _ & ?AA12 & _); hide_disj.
Section ACeilS1. Context {BZP : BzParams} {ACEIL__ : ACeil}.

Section SDC3.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp s0 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (P SHE FB SHF : Z) (w64 w72 w104 : word).
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Notation LENA := (e_len e). Notation CODA := (e_code e). Notation ARR1 := (e_arr1 e). Notation SELA := (e_selector e).
  Notation INUA := (e_inUse e). Notation SLMA := (e_selectorMtf e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1712 <= 18446744073709551616)%Z.
  Hypothesis AE : sanchor (c_E cx) SHE.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variables (nG : Z) (m0 : word -> option byte).
  Notation WD := [(E + 116, E + 120); (E + 640, E + 648); (A2, A2 + ARR2_SIZE); (P + 1384, P + 1568); (P + 1576, P + 1592)]%Z.
  Hypothesis VW : sd_vw cx e P FB SHF SHE w64 w72 w104 m0.
  Hypothesis SHe : shzW b0segs WD m0 E (E + ESTATE_SIZE).
  Hypothesis SH1 : shzW b0segs WD m0 A1 (A1 + ARR1_SIZE).
  Hypothesis SH2 : shzW b0segs WD m0 A2 (A2 + ARR2_SIZE).
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cSB := (Z_to_bv 64 2147450880). Notation cP := (Z_to_bv 64 P).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 :=
    (mkR ra cP gp tp t0 t1 t2 s0 cP a0 a1 a2 a3 a4 a5 a6 a7 cSB (Z_to_bv 64 (SHE + 10)) (Z_to_bv 64 (SHE + 80)) (Z_to_bv 64 (E + 116)) (Z_to_bv 64 (E + 644))
         (Z_to_bv 64 (E + 640)) (Z_to_bv 64 (E + 80)) (Z_to_bv 64 (SHE + 80)) s10 (Z_to_bv 64 (SHE + 14)) t3 t4 t5 t6).
  (* [comment removed for export] *)
  Notation SX L := (L cx g e Q gp tp s0 F fc P SHE FB SHF w64 w72 w104 CX SEP Gmtf Gbs Gzb Hnb CEP PHI AE LIM HLIM nG m0 VW SHe SH1 SH2).
  (* [comment removed for export] *)
  Notation FLX L f H bs b m := (SX L f H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _).

  (* [comment removed for export] *)
  Variable A : Z.
  Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z. Variable nSel : Z. Hypothesis HNS : (1 <= nSel <= 18002)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.
  Hypothesis CODF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef CODA (258 * t + v) = true /\ (0 <= zget CODA (258 * t + v) < 4294967296)%Z.
  Hypothesis SELF : forall i, (0 <= i < nSel)%Z -> zdef SELA i = true /\ (0 <= zget SELA i < nG)%Z.
  Hypothesis ZB1 : zbok ARR1.
  Notation NOT z := (Z_to_bv 64 (18446744073709551615 - z)).
  (* [comment removed for export] *)
  Notation RYs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 sc :=
    (RD (Z_to_bv 64 8) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 (Z_to_bv 64 1032) t3 (Z_to_bv 64 sc) (Z_to_bv 64 5) (Z_to_bv 64 258)).
  (* [comment removed for export] *)
  Definition hi_ok (H : sdw) : Prop :=
    w1488 H = Z_to_bv 64 18002 /\ w1496 H = Z_to_bv 64 (E + 39256) /\ w1504 H = NOT (E + 39256) /\ w1520 H = Z_to_bv 64 2147483647.
  Ltac hin HK := let HI := ident:(HI) in
    let a := fresh "HK88" in let b := fresh "HK96" in let c := fresh "HK04" in let d := fresh "HK20" in
    pose proof HK as (a & b & c & d); rewrite a, b, c, d in HI; clear a b c d.
  Ltac hout HK := let HI := ident:(HI) in
    let a := fresh "HK88" in let b := fresh "HK96" in let c := fresh "HK04" in let d := fresh "HK20" in
    pose proof HK as (a & b & c & d); rewrite <- a, <- b, <- c, <- d in HI; clear a b c d.

  Section SLOW.
  (* [comment removed for export] *)
  Variables (sc gs ge : Z).
  Hypothesis Hsc : (0 <= sc < nSel)%Z. Hypothesis Hgs : (0 <= gs <= ge)%Z. Hypothesis Hge : (ge <= gs + 49)%Z.
  Hypothesis HgsE : (2 * (gs + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFV : forall i, (gs <= i <= ge)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.
  Notation sel := (zget SELA sc).

  (* [comment removed for export] *)
  Lemma fl_957ec : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a4' a5' a6' a7' t0' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt b0segs Q (MS (RD ra t0' t1 t2 (Z_to_bv 64 (bw_live b1)) a1 a2 a3 a4' a5' a6' a7' s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x95be8) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RD ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x95ab0) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    brun.
    pose proof (rw_cells_read_byte3 b0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB.
    rewrite unsigned_lit in RB by lia.
    wstep. clear RB. cbv beta delta [zxb]. rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (u8arr_store_ok b0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 b0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    brun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm ra _ t1 t2 _ a1 a2 a3 _ _ _ _ s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' a4' a5' a6' a7' t0' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_slow_tail : forall (i SHs : Z) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (n : nat) (t0 a4 a5 a6 a7 : word),
    (i + Z.of_nat (S n) = ge + 1)%Z -> (gs <= i)%Z -> saddr (E + 1704 + sc) SHs -> hi_ok H ->
    let v := mtfv_at ARR1 i in let nv := zget LENA (258 * sel + v) in let cv := zget CODA (258 * sel + v) in
    let bf := sm_put_syms n (bsW b nv cv) LENA CODA ARR1 sel (i + 1) in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> MD H bs b1 m ->
    (forall (i SHs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 a0 a1 a3 a4 a5 a6 a7 : word),
      (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z -> saddr (E + 1704 + sc) SHs -> hi_ok H ->
      let bf := sm_put_syms n b LENA CODA ARR1 sel i in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
      (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), MD H bs bf m' -> bw_ok bf ->
          evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' sc) F (Z_to_bv 64 0x9d260) fc None m' (seg_rom b0segs))) ->
      evt b0segs Q (MS (RYs t0 (Z_to_bv 64 i) (Z_to_bv 64 (E + 1704 + sc)) a0 a1 (Z_to_bv 64 (ge + 1)) a3 a4 a5 a6 a7 (Z_to_bv 64 SHs) sc) F (Z_to_bv 64 0x959ac) fc None m (seg_rom b0segs))) ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' sc) F (Z_to_bv 64 0x9d260) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RYs t0 (Z_to_bv 64 i) (Z_to_bv 64 (E + 1704 + sc)) (Z_to_bv 64 (bw_live b1)) (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 (ge + 1)) (Z_to_bv 64 nv) a4 a5 a6 a7 (Z_to_bv 64 SHs) sc)
                      F (Z_to_bv 64 0x95be8) fc None m (seg_rom b0segs)).
  Proof using All.
    intros i SHs H bs b b1 m n t0 a4 a5 a6 a7 Hn Hi AS HK. cbv zeta. intros OK Eb1 NL MEM IHn K.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. hin HK.
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    brun.
    rewrite (Z.mod_small (32 - bw_live b1 - nv) 32) in EH2 by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted3 _ _ (bw_buff b1)) by lia.
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    assert (EBW : bsW b nv cv = BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - nv)) mod 4294967296)) (bw_live b1 + nv) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b nv cv)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    hout HK.
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z SHs H bs (bsW b nv cv) mm t0 _ _ _ _ _ _ _); [st_eq| lia| lia| lia| exact AS| exact HK| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. rewrite put_syms_0 in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma B0_slow_loop : forall (n : nat) (i SHs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 a0 a1 a3 a4 a5 a6 a7 : word),
    (1 <= n)%nat -> (i + Z.of_nat n = ge + 1)%Z -> (gs <= i)%Z -> saddr (E + 1704 + sc) SHs -> hi_ok H ->
    let bf := sm_put_syms n b LENA CODA ARR1 sel i in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' sc) F (Z_to_bv 64 0x9d260) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RYs t0 (Z_to_bv 64 i) (Z_to_bv 64 (E + 1704 + sc)) a0 a1 (Z_to_bv 64 (ge + 1)) a3 a4 a5 a6 a7 (Z_to_bv 64 SHs) sc) F (Z_to_bv 64 0x959ac) fc None m (seg_rom b0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros i SHs H bs b m t0 a0 a1 a3 a4 a5 a6 a7 _ Hn Hi AS HK. cbv zeta. intros OK NL MEM K.
    rewrite put_syms_S in NL, K.
    set (v := mtfv_at ARR1 i) in *. set (nv := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (put_syms_NZM n (bsW b nv cv) LENA CODA ARR1 sel (i + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b nv cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. hin HK.
    cps_pose OK as (OKb & OKl & OKn).
    pose proof (MTFV i ltac:(lia)) as MV. fold v in MV. pose proof (SELF sc Hsc) as [SD SR].
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG]. fold nv in LD, LRG. fold cv in CD, CRG.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    openVW VW. brun.
    pose proof (ovb_read1 b0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD ltac:(unfold wa; f_equal; lia)) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 sel) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (zb8_read2 b0segs m A1 ARR1 ARR1_SIZE (2 * i) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD1.
    change (rd16 ARR1 (2 * i)) with (mtfv_at ARR1 i) in RD1. fold v in RD1.
    wstep. clear RD1. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (ovb_read1 b0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. cbv beta. fold nv. rewrite (unsigned_lit8 nv) by lia.
    (* [comment removed for export] *)
    brun.
    pose proof (ovw_read b0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD3.
    wstep. clear RD3. fold cv.
    closeVW.
    (* [comment removed for export] *)
    brun. hout HK. if_cases Kc; zify_cond_z Kc.
    - enter_with (B0_slow_tail i SHs H bs b b m n t0 _ _ _ _); [st_eq| lia| lia| exact AS| exact HK| exact OK| | exact NL| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (fl_957ec BS_FUEL H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b nv cv) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a4' a5' a6' a7' t0' Eb1 MEM' L1.
      enter_with (B0_slow_tail i SHs H bs b b1 m' n t0' _ _ _ _); [st_eq| lia| lia| exact AS| exact HK| exact OK| exact Eb1| exact NL| exact MEM'| exact IH| exact K].
  Qed.
  End SLOW.

  (* [comment removed for export] *)
  Variable NM : Z.
  Hypothesis HNM : (1 <= NM)%Z. Hypothesis HNMe : e_nMTF e = NM. Hypothesis HNMA : (2 * (NM + 50) <= ARR1_SIZE)%Z.
  Hypothesis MTFVN : forall i, (0 <= i < NM)%Z -> (0 <= mtfv_at ARR1 i < A)%Z.

  (* [comment removed for export] *)
  Lemma B0_group_tail : forall (sc gs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    hi_ok H -> w1528 H = Z_to_bv 64 gs -> w1512 H = Z_to_bv 64 (ge + 1) ->
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), MD H bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' sc) F (Z_to_bv 64 0x9d260) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RYs t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 sc) F (Z_to_bv 64 0x9568c) fc None m (seg_rom b0segs)).
  Proof using All.
    intros sc gs H bs b m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 Hsc Hgs. cbv zeta. intros HK HW28 HW12 OK NL MEM K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    set (ge := GE NM gs) in *.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. hin HK. rewrite HW28, HW12 in HI.
    cps_pose OK as (OKb & OKl & OKn). pose proof (SELF sc Hsc) as [SD SR].
    (* [comment removed for export] *)
    openVW VW. brun.
    pose proof (ovb_read1 b0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD ltac:(unfold wa; f_equal; lia)) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 (zget SELA sc)) by lia.
    pose proof (saddr_intro (E + 1704 + sc)) as AS. set (SHs := ((E + 1704 + sc) / 8 + 2147450880)%Z) in *. clearbody SHs.
    (* [comment removed for export] *)
    brun. if_cases Ka; zify_cond_z Ka; [| exfalso; lia].
    (* [comment removed for export] *)
    assert (SLOWP : forall (y0 y1 y2 y3 y4 y5 y6 y7 y8 : word),
      evt b0segs Q (MS (RYs y0 (Z_to_bv 64 gs) (Z_to_bv 64 (E + 1704 + sc)) y1 y2 y3 y4 y5 y6 y7 y8 (Z_to_bv 64 SHs) sc) F (Z_to_bv 64 0x95994) fc None m (seg_rom b0segs))).
    { intros y0 y1 y2 y3 y4 y5 y6 y7 y8.
      wstep. wstep. wstep; if_cases K1; zify_cond_z K1; [exfalso; lia|]. wstep. wstep; if_cases K2; zify_cond_z K2; [|exfalso; lia].
      closeVW. hout HK. rewrite <- HW28 in HI. rewrite <- HW12 in HI.
      enter_with (B0_slow_loop sc gs ge Hsc ltac:(lia) ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply MTFVN; lia)
                    (Z.to_nat (ge - gs + 1)) gs SHs H bs b m _ _ _ _ _ _ _ _);
        [st_eq| lia| lia| lia| exact AS| exact HK| exact OK| exact NL| closeMD|].
      intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' MEM' OK'.
      exact (K m' _ _ _ _ _ _ _ _ _ _ _ _ MEM' OK'). }
    (* [comment removed for export] *)
    brun. if_cases K6.
    { (* [comment removed for export] *) enter_with (SLOWP _ _ _ _ _ _ _ _ _); st_eq. }
    (* [comment removed for export] *)
    brun. if_cases K50; zify_cond_z K50.
    { enter_with (SLOWP _ _ _ _ _ _ _ _ _); st_eq. }
    (* [comment removed for export] *)
    replace (Z.to_nat (ge - gs + 1)) with 50%nat in NL, K by lia.
    closeVW. hout HK. rewrite <- HW12 in HI. rewrite <- HW28 in HI.
    pose proof HK as (_ & HW96 & HW04 & _).
    enter_with (SX B0_fast50 A HA HG nSel HNS LENF CODF SELF ZB1 sc gs Hsc ltac:(lia) ltac:(lia) ltac:(intros i Hi; apply MTFVN; lia) SHs H bs b m _ _ _ _ _ _ _ _ _ _ AS HW28 HW96 HW04);
      [st_eq| exact OK| exact NL| closeMD|].
    intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' MEM' OK'.
    exact (K m' _ _ _ _ _ _ _ _ _ _ _ _ MEM' OK').
  Qed.

  (* [comment removed for export] *)
  Lemma B0_group : forall (sc gs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 : word),
    (0 <= sc < nSel)%Z -> (0 <= gs < NM)%Z ->
    let ge := GE NM gs in
    let bf := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs in
    hi_ok H ->
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (H' : sdw) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), hi_ok H' -> w1512 H' = Z_to_bv 64 (ge + 1) -> w1448 H' = w1448 H -> MD H' bs bf m' -> bw_ok bf ->
        evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' sc) F (Z_to_bv 64 0x9d260) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RYs t0 t1 t2 (Z_to_bv 64 NM) a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 t3 sc) F (Z_to_bv 64 0x9566c) fc None m (seg_rom b0segs)).
  Proof using All.
    intros sc gs H bs b m t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 Hsc Hgs. cbv zeta. intros HK OK NL MEM K.
    cps_pose (GE_facts NM gs Hgs) as (G1 & G2 & G3).
    set (ge := GE NM gs) in *.
    set (H' := SDW (w1400 H) (w1408 H) (w1416 H) (w1424 H) (w1432 H) (w1448 H) (w1456 H) (w1472 H) (w1488 H) (w1496 H) (w1504 H) (Z_to_bv 64 (ge + 1)) (w1520 H) (Z_to_bv 64 gs)).
    assert (HK' : hi_ok H') by exact HK.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    (* [comment removed for export] *)
    brun_to 0x9567c%Z. wstep. wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep.
      assert (Ege : (ge + 1 = gs + 50)%Z) by (subst ge; unfold GE, BZ_G_SIZE; destruct (Z.leb_spec NM (gs + 50 - 1)); lia).
      replace (Z_to_bv 64 (gs + 50)) with (Z_to_bv 64 (ge + 1)) in HI by (f_equal; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_group_tail sc gs H' bs b mm _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact Hsc| exact Hgs| exact HK'| reflexivity| reflexivity| exact OK| exact NL| closeMD|] end.
      intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' MEM' OK'.
      exact (K m' H' _ _ _ _ _ _ _ _ _ _ _ _ HK' eq_refl eq_refl MEM' OK').
    - (* [comment removed for export] *)
      wstep. wstep.
      assert (Ege : (ge + 1 = NM)%Z) by (subst ge; unfold GE, BZ_G_SIZE; destruct (Z.leb_spec NM (gs + 50 - 1)); lia).
      replace (Z_to_bv 64 NM) with (Z_to_bv 64 (ge + 1)) in HI by (f_equal; lia).
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (B0_group_tail sc gs H' bs b mm _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact Hsc| exact Hgs| exact HK'| reflexivity| reflexivity| exact OK| exact NL| closeMD|] end.
      intros m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' MEM' OK'.
      exact (K m' H' _ _ _ _ _ _ _ _ _ _ _ _ HK' eq_refl eq_refl MEM' OK').
  Qed.

  (* [comment removed for export] *)
  Lemma B0_data_loop : forall (f : nat) (gs sc : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 : word),
    (0 <= sc)%Z -> (0 <= gs < NM)%Z -> (NM - gs <= Z.of_nat f)%Z ->
    let r := sm_put_data f b LENA CODA ARR1 SELA NM gs sc in
    (snd r <= nSel)%Z -> hi_ok H ->
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
    (forall m' (H' : sdw) (t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' : word), hi_ok H' -> w1448 H' = w1448 H -> MD H' bs (fst r) m' -> bw_ok (fst r) ->
        evt b0segs Q (MS (RYs t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' (snd r)) F (Z_to_bv 64 0x9e47c) fc None m' (seg_rom b0segs))) ->
    evt b0segs Q (MS (RYs t0 t1 t2 (Z_to_bv 64 NM) a1 a2 a3 (Z_to_bv 64 gs) a5 a6 a7 t3 sc) F (Z_to_bv 64 0x9566c) fc None m (seg_rom b0segs)).
  Proof using All.
    induction f as [|f IH]; [lia|].
    intros gs sc H bs b m t0 t1 t2 a1 a2 a3 a5 a6 a7 t3 Hsc Hgs Hf. cbv zeta. intros SCN HK OK NL MEM K.
    pose proof (put_data_snd_step f b LENA CODA ARR1 SELA NM gs sc ltac:(lia)) as SC1.
    rewrite put_data_S in SCN, NL, K, SC1. fold BZ_G_SIZE in SCN, NL, K, SC1.
    destruct (Z.leb_spec NM gs) as [Xg|Xg]; [lia|]. cbv zeta in SCN, NL, K, SC1.
    change (if NM <=? gs + BZ_G_SIZE - 1 then NM - 1 else gs + BZ_G_SIZE - 1)%Z with (GE NM gs) in SCN, NL, K, SC1.
    cps_pose (GE_facts NM gs ltac:(lia)) as (G1 & G2 & G3). set (ge := GE NM gs) in *.
    set (b1 := sm_put_syms (Z.to_nat (ge - gs + 1)) b LENA CODA ARR1 (zget SELA sc) gs) in *.
    pose proof (put_data_NZM f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as NZ1. unfold NZM in NZ1.
    pose proof (put_data_snd_ge f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1)) as SG.
    eapply (B0_group sc gs H bs b m _ _ _ _ _ _ _ _ _ _); [lia| lia| exact HK| exact OK| subst ge b1; lia| exact MEM|].
    fold ge. fold b1. clear MEM HK. revert K. generalize (w1448 H) as v48. clear H. intros v48 K m1 H t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' HK HW12 HW48 MEM OK1.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. rewrite HNMe in EH2. rewrite HW12 in HI. cps_pose OK1 as (OK1b & OK1l & OK1n).
    (* [comment removed for export] *)
    openVW VW. brun. closeVW. rewrite <- HW12 in HI. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IH (ge + 1)%Z (sc + 1)%Z H bs b1 mm _ _ _ _ _ _ _ _ _ _); [st_eq| lia| lia| lia| exact SCN| exact HK| exact OK1| exact NL| rewrite <- HNMe in EH2; closeMD|] end.
      intros m' H' t0'' t1'' t2'' a0'' a1'' a2'' a3'' a4'' a5'' a6'' a7'' t3'' HK' HW48' MEM' OK'. exact (K m' H' _ _ _ _ _ _ _ _ _ _ _ _ HK' (eq_trans HW48' HW48) MEM' OK').
    - (* [comment removed for export] *)
      assert (ER : sm_put_data f b1 LENA CODA ARR1 SELA NM (ge + 1) (sc + 1) = (b1, (sc + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_data_S. destruct (Z.leb_spec NM (ge + 1)); [reflexivity| lia]. }
      rewrite ER in K. cbn [fst snd] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm H _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact HK| exact HW48| rewrite <- HNMe in EH2; closeMD| exact OK1] end.
  Qed.
End SDC3.
End ACeilS1.
