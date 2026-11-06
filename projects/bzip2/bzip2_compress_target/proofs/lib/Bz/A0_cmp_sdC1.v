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

Section SDC1.
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

  Lemma Hsel : (0 <= sel < 6)%Z. Proof using SELF Hsc HG. pose proof (SELF sc Hsc). lia. Qed.

  (* [comment removed for export] *)
  Lemma fl_901bc : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (t0' a7' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt a0segs Q (MS (RD (Z_to_bv 64 15) t0' t1 t2 a0 (Z_to_bv 64 (bw_live b1)) a2 a3 a4 a5 a6 a7' s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x90744) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RD (Z_to_bv 64 15) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x904d8) fc None m (seg_rom a0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    arun.
    pose proof (rw_cells_read_byte3 a0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB.
    rewrite unsigned_lit in RB by lia.
    wstep. clear RB. cbv beta delta [zxb]. rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (u8arr_store_ok a0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 a0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    arun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm _ t1 t2 a0 _ a2 a3 a4 a5 a6 _ s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' t0' a7' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_0_tail : forall (H : sdw) (bs : list byte) (b1 : bw) (n cv : Z) (m : word -> option byte) (t0 a7 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    MD H bs b1 m ->
    (forall m' (a1' a2' t0' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD H bs b' m' ->
        evt a0segs Q (MS (RG a1' a2' (Z_to_bv 64 n) (Z_to_bv 64 (bw_live b1 + n)) t0') F (Z_to_bv 64 0x90778) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RG (Z_to_bv 64 (bw_live b1)) (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) a7 t0) F (Z_to_bv 64 0x90744) fc None m (seg_rom a0segs)).
  Proof using All.
    intros H bs b1 n cv m t0 a7 OK L1 Hn Hcv MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    arun_to 0x90778%Z.
    rewrite (neg_shift_amount (bw_live b1) n) in EH2 by lia.
    replace (bw_live b1 + n =? 32)%Z with false in EH2 by (symmetry; apply Z.eqb_neq; lia).
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia| lia]).
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _); [st_eq| closeMD] end.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_0 : forall (SHs : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a0 a1 a2 a4 a5 a6 : word),
    saddr (E + 1704 + sc) SHs ->
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 0))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 0)))) <= LIM)%Z -> MD H bs b m ->
    (forall m' (a1' a2' a6' t0' : word), MD H bs (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 0))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 0)))) m' ->
        evt a0segs Q (MS (RG a1' a2' a6' (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 0))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 0)))))) t0') F (Z_to_bv 64 0x90778) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RY (Z_to_bv 64 SHs) xt1 a0 a1 a2 (Z_to_bv 64 (gs + 50)) a4 a5 a6 (Z_to_bv 64 (E + 1704 + sc)) gs sc) F (Z_to_bv 64 0x90440) fc None m (seg_rom a0segs)).
  Proof using All.
    intros SHs H bs b m a0 a1 a2 a4 a5 a6 AS OK NL MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 0) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 0)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    openVW VW. arun.
    pose proof (ovb_read1 a0segs m (E + 1704) SELA (jseg J 1704 18002) 18002 sc _ SEL ltac:(lia) SD ltac:(unfold wa; f_equal; lia)) as RD0.
    wstep. clear RD0. cbv beta. rewrite (unsigned_lit8 sel) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (zb8_read2 a0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 0)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 0))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (ovb_read1 a0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (ovw_read a0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    closeVW.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - enter_with (blk_0_tail H bs b n cv m _ _); [st_eq| exact OK| lia| lia| lia| closeMD|].
      intros m' a1' a2' t0' b' MEM'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K m' _ _ _ _); [st_eq| exact MEM'].
    - enter_with (fl_901bc BS_FUEL H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' t0' a7' Eb1 MEM' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      enter_with (blk_0_tail H bs b1 n cv m' _ _); [st_eq| exact OK1| lia| lia| lia| exact MEM'|].
      intros m'' a1'' a2'' t0'' b' MEM''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K m'' _ _ _ _); [st_eq| exact MEM''].
  Qed.

  (* [comment removed for export] *)
  Lemma fl_93d44 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a1' t0' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt a0segs Q (MS (RD (Z_to_bv 64 15) t0' t1 t2 a0 a1' a2 a3 a4 a5 a6 (Z_to_bv 64 (bw_live b1)) s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x94104) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RD (Z_to_bv 64 15) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x94060) fc None m (seg_rom a0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    arun.
    pose proof (rw_cells_read_byte3 a0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB.
    rewrite unsigned_lit in RB by lia.
    wstep. clear RB. cbv beta delta [zxb]. rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (u8arr_store_ok a0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 a0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    arun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm _ t1 t2 a0 _ a2 a3 a4 a5 a6 _ s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' a1' t0' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_48_tail : forall (H : sdw) (bs : list byte) (b1 : bw) (n cv : Z) (m : word -> option byte) (a1 t0 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    MD H bs b1 m ->
    (forall m' (a1' a2' a7' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD H bs b' m' ->
        evt a0segs Q (MS (RG a1' a2' (Z_to_bv 64 (bw_live b1 + n)) a7' t0) F (Z_to_bv 64 0x94138) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RG a1 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) (Z_to_bv 64 (bw_live b1)) t0) F (Z_to_bv 64 0x94104) fc None m (seg_rom a0segs)).
  Proof using All.
    intros H bs b1 n cv m a1 t0 OK L1 Hn Hcv MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    arun_to 0x94138%Z.
    rewrite (neg_shift_amount (bw_live b1) n) in EH2 by lia.
    replace (bw_live b1 + n =? 32)%Z with false in EH2 by (symmetry; apply Z.eqb_neq; lia).
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia| lia]).
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _); [st_eq| closeMD] end.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_48 : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a1 a2 a6 t0 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))) <= LIM)%Z -> MD H bs b m ->
    (forall m' (a1' a2' a7' t0' : word), MD H bs (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))) m' ->
        evt a0segs Q (MS (RG a1' a2' (Z_to_bv 64 (bw_live (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 48))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 48)))))) a7' t0') F (Z_to_bv 64 0x94138) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RG a1 a2 a6 (Z_to_bv 64 (bw_live b)) t0) F (Z_to_bv 64 0x94004) fc None m (seg_rom a0segs)).
  Proof using All.
    intros H bs b m a1 a2 a6 t0 OK NL MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 48) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 48)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose OK as (OKb & OKl & OKn).
    openVW VW.
    arun.
    pose proof (zb8_read2 a0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 48)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 48))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    arun.
    pose proof (ovb_read1 a0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    arun.
    pose proof (ovw_read a0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    closeVW.
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      eapply (blk_48_tail H bs b n cv m _ _); [exact OK| lia| lia| lia| closeMD|].
      intros m' a1' a2' a7' b' MEM'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K m' _ _ _ _); [st_eq| exact MEM'].
    - enter_with (fl_93d44 BS_FUEL H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a1' t0' Eb1 MEM' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      eapply (blk_48_tail H bs b1 n cv m' _ _); [exact OK1| lia| lia| lia| exact MEM'|].
      intros m'' a1'' a2'' a7'' b' MEM''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K m'' _ _ _ _); [st_eq| exact MEM''].
  Qed.

  (* [comment removed for export] *)
  Lemma fl_93e78 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a0' a5' a4' : word), b1 = bs_needw f b -> MD H i16 b1 m' -> (0 <= bw_live b1 < 8)%Z ->
        evt a0segs Q (MS (RD (Z_to_bv 64 15) t0 t1 t2 a0' a1 a2 a3 a4' a5' (Z_to_bv 64 (bw_live b1)) a7 s10 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x94238) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RD (Z_to_bv 64 15) t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x94194) fc None m (seg_rom a0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 s10 t3 t4 t5 t6 OK L8 Lf NL MEM K; [lia|].
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    pose proof (bw_emit_byte b ltac:(lia)) as BB. rewrite shiftr_div24 in BB.
    (* [comment removed for export] *)
    arun.
    pose proof (rw_cells_read_byte3 a0segs m (E + 640) _ 0%nat _ _ EH2 eq_refl eq_refl) as RB.
    rewrite unsigned_lit in RB by lia.
    wstep. clear RB. cbv beta delta [zxb]. rewrite (unsigned_lit8 (bw_buff b / 16777216)) by lia.
    (* [comment removed for export] *)
    arun.
    pose proof (u8arr_store_ok a0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    wstep.
    match goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 a0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    (* [comment removed for export] *)
    arun.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z. { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) (bv_unsigned (Z_to_bv 64 (bw_buff b / 16777216))))
      with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. rewrite shiftr_div24. rewrite unsigned_lit by lia. reflexivity. }
    if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm t0 t1 t2 _ a1 a2 a3 _ _ _ a7 s10 t3 t4 t5 t6); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| closeMD|] end.
      intros b1 m' a0' a5' a4' Eb1 MEM' L1. eapply K; [|exact MEM'| exact L1].
      rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - wstep. (* [comment removed for export] *)
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm _ _ _); [st_eq| | closeMD| lia] end.
      cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
      destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_49_tail : forall (H : sdw) (bs : list byte) (b1 : bw) (n cv : Z) (m : word -> option byte) (t0 a0 a4 a5 a7 : word),
    bw_ok b1 -> (0 <= bw_live b1 < 8)%Z -> (1 <= n <= 17)%Z -> (0 <= cv < 4294967296)%Z ->
    MD H bs b1 m ->
    (forall m' (a0' a1' a2' a4' : word),
        let b' := BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1) in
        MD H bs b' m' ->
        evt a0segs Q (MS (RY t0 xt1 a0' a1' a2' (Z_to_bv 64 (gs + 50)) a4' a5 (Z_to_bv 64 (bw_live b1)) a7 gs sc) F (Z_to_bv 64 0x9426c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RY t0 xt1 a0 (sx32 (Z_to_bv 64 cv)) (Z_to_bv 64 n) (Z_to_bv 64 (gs + 50)) a4 a5 (Z_to_bv 64 (bw_live b1)) a7 gs sc) F (Z_to_bv 64 0x94238) fc None m (seg_rom a0segs)).
  Proof using All.
    intros H bs b1 n cv m t0 a0 a4 a5 a7 OK L1 Hn Hcv MEM K.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_destruct OK as (OKb & OKl & OKn).
    arun_to 0x9426c%Z.
    rewrite (neg_shift_amount (bw_live b1) n) in EH2 by lia.
    replace (bw_live b1 + n =? 32)%Z with false in EH2 by (symmetry; apply Z.eqb_neq; lia).
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296))%Z.
    { rewrite (low32_or_shifted _ _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia| lia]).
      rewrite (shl_mod32_congr _ cv) by (first [lia| rewrite low32_sx32, low32_lit; reflexivity]).
      rewrite low32_small; [reflexivity|].
      change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K mm _ _ _ _); [st_eq| closeMD] end.
  Qed.

  (* [comment removed for export] *)
  Lemma blk_49 : forall (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (a1 a2 a7 t0 : word),
    bw_ok b -> (bw_numZ (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) <= LIM)%Z -> MD H bs b m ->
    (forall m' (a0' a1' a2' a4' a5' a6' : word), MD H bs (bsW b (zget LENA (258 * sel + mtfv_at ARR1 (gs + 49))) (zget CODA (258 * sel + mtfv_at ARR1 (gs + 49)))) m' ->
        evt a0segs Q (MS (RY t0 xt1 a0' a1' a2' (Z_to_bv 64 (gs + 50)) a4' a5' a6' a7 gs sc) F (Z_to_bv 64 0x9426c) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RG a1 a2 (Z_to_bv 64 (bw_live b)) a7 t0) F (Z_to_bv 64 0x94138) fc None m (seg_rom a0segs)).
  Proof using All.
    intros H bs b m a1 a2 a7 t0 OK NL MEM K.
    pose proof Hsel as HS6. pose proof (SELF sc Hsc) as [SD SR].
    pose proof (MTFV (gs + 49) ltac:(lia)) as MV. set (v := mtfv_at ARR1 (gs + 49)) in *.
    destruct (LENF sel v ltac:(lia) MV) as [LD LRG]. destruct (CODF sel v ltac:(lia) MV) as [CD CRG].
    set (n := zget LENA (258 * sel + v)) in *. set (cv := zget CODA (258 * sel + v)) in *.
    pose proof (bsW_NZM b n cv) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose OK as (OKb & OKl & OKn).
    openVW VW.
    arun.
    pose proof (zb8_read2 a0segs m A1 ARR1 ARR1_SIZE (2 * (gs + 49)) _ AR1 ltac:(lia) ltac:(lia) ZB1 ltac:(unfold wa; f_equal; lia)) as RD.
    change (rd16 ARR1 (2 * (gs + 49))) with v in RD.
    wstep. clear RD. rewrite zx16_small by lia.
    arun.
    pose proof (ovb_read1 a0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * sel + v) _ LEN ltac:(lia) LD ltac:(unfold wa; f_equal; lia)) as RD1.
    wstep. clear RD1. cbv beta. fold n. rewrite (unsigned_lit8 n) by lia.
    arun.
    pose proof (ovw_read a0segs m (E + 39256) CODA (jseg J 39256 6192) 1548 (258 * sel + v) _ COD ltac:(lia) CD ltac:(unfold wa; f_equal; lia)) as RD2.
    wstep. clear RD2. fold cv.
    closeVW.
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (blk_49_tail H bs b n cv m _ _ _ _ _); [exact OK| lia| lia| lia| closeMD|].
      intros m' a0' a1' a2' a4' b' MEM'. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b) ((Z.shiftl cv (32 - bw_live b - n)) mod 4294967296)) (bw_live b + n) (bw_numZ b) (bw_zb b)) in K
        by (unfold bsW, BS_FUEL; cbn [bs_needw]; replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia); reflexivity).
      enter_with (K m' _ _ _ _ _ _); [st_eq| exact MEM'].
    - enter_with (fl_93e78 BS_FUEL H bs b m _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b n cv) as [BB _]. rewrite <- BB. exact NL. }
      intros b1 m' a0' a5' a4' Eb1 MEM' L1.
      cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1). rewrite <- Eb1 in OK1, M1, N1.
      eapply (blk_49_tail H bs b1 n cv m' _ _ _ _ _); [exact OK1| lia| lia| lia| exact MEM'|].
      intros m'' a0'' a1'' a2'' a4'' b' MEM''. subst b'.
      replace (bsW b n cv) with (BW (Z.lor (bw_buff b1) ((Z.shiftl cv (32 - bw_live b1 - n)) mod 4294967296)) (bw_live b1 + n) (bw_numZ b1) (bw_zb b1)) in K
        by (unfold bsW; rewrite <- Eb1; reflexivity).
      enter_with (K m'' _ _ _ _ _ _); [st_eq| exact MEM''].
  Qed.
End SDC1.
End ACeilS1.
