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
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import A0_cmp_sdFL2.

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

Section SDF.
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

  Hypothesis HAe : (e_nInUse e + 2 = A)%Z. Hypothesis HA : (3 <= A <= 258)%Z. Hypothesis HG : (2 <= nG <= 6)%Z.
  Hypothesis LENF : forall t v, (0 <= t < nG)%Z -> (0 <= v < A)%Z -> zdef LENA (258 * t + v) = true /\ (1 <= zget LENA (258 * t + v) <= 17)%Z.

  (* [comment removed for export] *)
  Notation LR t := (E + 37708 + 258 * t)%Z.
  Notation RL ra a0 a1 a2 a3 t a5v s10 curr i :=
    (RD ra (Z_to_bv 64 27) (Z_to_bv 64 (-1)) (Z_to_bv 64 30) a0 a1 a2 a3 (Z_to_bv 64 t) (Z_to_bv 64 a5v) (Z_to_bv 64 8) (Z_to_bv 64 15) s10 (Z_to_bv 64 2) (Z_to_bv 64 3) curr i).

  (* [comment removed for export] *)
  Ltac rdlen t i tgt Htgt ZD ZR :=
    let LEN := ident:(LEN) in let RD := ident:(RD) in
    openVW VW;
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      pose proof (ovb_read1 a0segs mm (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD end;
    closeVW;
    wstep; clear RD; cbv beta; rewrite <- ?Htgt; rewrite (unsigned_lit8 tgt) by lia.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_up_tail : forall (t i curr tgt SHl : Z) (f : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a0 a3 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
    (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat (S f))%Z ->
    let r := sm_put_up f (bsW b 2 2) (curr + 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall (t i curr tgt SHl : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
      (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat f)%Z ->
      let r := sm_put_up f b curr tgt in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' a0' a2' a3' : word),
          MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
          evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) a2' a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900c0) fc None m' (seg_rom a0segs))) ->
      evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x8ffb0) fc None m (seg_rom a0segs))) ->
    (forall m' (ra' a0' a2' a3' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
        evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) a2' a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900c0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b1)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x90058) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t i curr tgt SHl f H bs b b1 m ra a0 a3 Ht Hi Htgt AS Hc Hf. cbv zeta. intros OK Eb1 NL L1 MEM IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 2 2 = BW (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 2)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    arun.
    rewrite (Z.mod_small (30 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 2 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_shifted 2 _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia | lia]).
      replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rdlen t i tgt Htgt ZD ZR.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      destruct f as [|f']; [exfalso; lia|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn t i (curr + 1)%Z tgt SHl H bs (bsW b 2 2) mm _ _ _);
        [st_eq; rewrite ?EBW; reflexivity| exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - (* [comment removed for export] *)
      assert (ER : sm_put_up f (bsW b 2 2) (curr + 1) tgt = (bsW b 2 2, (curr + 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_up_S. replace (curr + 1 <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2| lia] end.
  Qed.

  Lemma A0_up_loop : forall (f : nat) (t i curr tgt SHl : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
    (1 <= curr < tgt)%Z -> (tgt - curr <= Z.of_nat f)%Z ->
    let r := sm_put_up f b curr tgt in
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
    (forall m' (ra' a0' a2' a3' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
        evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) a2' a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900c0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x8ffb0) fc None m (seg_rom a0segs)).
  Proof using All.
    induction f as [|f IH]; [lia|].
    intros t i curr tgt SHl H bs b m ra a0 a3 Ht Hi Htgt AS Hc Hf. cbv zeta. intros OK NL MEM K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_up_S in NL, K. replace (curr <? tgt)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_up_NZM f (bsW b 2 2) (curr + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 2) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (A0_up_tail t i curr tgt SHl f H bs b b m _ _ _); [exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK| | exact NL| lia| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX fl_8fc98 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b 2 2) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a3' ra' a0' Eb1 MEM' L1.
      eapply (A0_up_tail t i curr tgt SHl f H bs b b1 m' _ _ _); [exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma A0_down_tail : forall (t i curr tgt SHl : Z) (f : nat) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a0 a3 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
    (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat (S f))%Z ->
    let r := sm_put_down f (bsW b 2 3) (curr - 1) tgt in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ (fst r) <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall (t i curr tgt SHl : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 : word),
      (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
      (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat f)%Z ->
      let r := sm_put_down f b curr tgt in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' a0' a3' : word),
          MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
          evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live (fst r))) a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x901ec) fc None m' (seg_rom a0segs))) ->
      evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900dc) fc None m (seg_rom a0segs))) ->
    (forall m' (ra' a0' a3' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
        evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live (fst r))) a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x901ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b1)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x90184) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t i curr tgt SHl f H bs b b1 m ra a0 a3 Ht Hi Htgt AS Hc Hf. cbv zeta. intros OK Eb1 NL L1 MEM IHn K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    assert (EBW : bsW b 2 3 = BW (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296)) (bw_live b1 + 2) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 2 3)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    arun.
    rewrite (Z.mod_small (30 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl 3 (32 - bw_live b1 - 2) mod 4294967296))%Z.
    { rewrite (low32_or_shifted 3 _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia | lia]).
      replace (30 - bw_live b1)%Z with (32 - bw_live b1 - 2)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    rdlen t i tgt Htgt ZD ZR.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - destruct f as [|f']; [exfalso; lia|].
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn t i (curr - 1)%Z tgt SHl H bs (bsW b 2 3) mm _ _ _);
        [st_eq; rewrite ?EBW; reflexivity| exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (ER : sm_put_down f (bsW b 2 3) (curr - 1) tgt = (bsW b 2 3, (curr - 1)%Z)).
      { destruct f; [reflexivity|]. rewrite put_down_S. replace (tgt <? curr - 1)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ER in K. cbn [fst snd] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _); [st_eq; rewrite ?EBW; reflexivity| rewrite EBW; closeMD| exact OK2| lia] end.
  Qed.

  Lemma A0_down_loop : forall (f : nat) (t i curr tgt SHl : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a3 : word),
    (0 <= t < nG)%Z -> (0 <= i < A)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
    (tgt < curr <= 17)%Z -> (curr - tgt <= Z.of_nat f)%Z ->
    let r := sm_put_down f b curr tgt in
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
    (forall m' (ra' a0' a3' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) -> snd r = tgt ->
        evt a0segs Q (MS (RL ra' a0' (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live (fst r))) a3' t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x901ec) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) (Z_to_bv 64 (bw_live b)) a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900dc) fc None m (seg_rom a0segs)).
  Proof using All.
    induction f as [|f IH]; [lia|].
    intros t i curr tgt SHl H bs b m ra a0 a3 Ht Hi Htgt AS Hc Hf. cbv zeta. intros OK NL MEM K.
    destruct (LENF t i Ht Hi) as [ZD ZR]. rewrite <- Htgt in ZR.
    rewrite put_down_S in NL, K. replace (tgt <? curr)%Z with true in NL, K by (symmetry; apply Z.ltb_lt; lia).
    pose proof (put_down_NZM f (bsW b 2 3) (curr - 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM b 2 3) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    pose proof (Z.mod_pos_bound (bw_live b) 8 ltac:(lia)) as MB.
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (A0_down_tail t i curr tgt SHl f H bs b b m _ _ _); [exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK| | exact NL| lia| closeMD| exact IH| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX fl_8fdc4 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b 2 3) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a0' a3' ra' Eb1 MEM' L1.
      eapply (A0_down_tail t i curr tgt SHl f H bs b b1 m' _ _ _); [exact Ht| exact Hi| exact Htgt| exact AS| lia| lia| exact OK| exact Eb1| exact NL| exact L1| exact MEM'| exact IH| exact K].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Definition LROW (n : nat) (t : Z) : Prop :=
    forall (i curr : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a1 a2 a3 s10 : word),
      (0 <= t < nG)%Z -> (i + Z.of_nat n = A)%Z -> (0 <= i)%Z -> (1 <= n)%nat -> (1 <= curr <= 17)%Z ->
      let r := sm_put_lens_row n b LENA t i curr in
      bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' a0' a1' a2' a3' s10' t5' : word),
          MD H bs (fst r) m' -> bw_ok (fst r) ->
          evt a0segs Q (MS (RL ra' a0' a1' a2' a3' t (LR t) s10' t5' (Z_to_bv 64 A)) F (Z_to_bv 64 0x902f0) fc None m' (seg_rom a0segs))) ->
      evt a0segs Q (MS (RL ra a0 a1 a2 a3 t (LR t) s10 (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x8ff88) fc None m (seg_rom a0segs)).

  (* [comment removed for export] *)
  Lemma A0_lens_fin : forall (t i tgt : Z) (n : nat) (H : sdw) (bs : list byte) (bo b1 : bw) (m : word -> option byte) (ra a0 a1 a3 s10 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> b1 = bs_needw BS_FUEL bo -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b1 m ->
    LROW n t ->
    (forall m' (ra' a0' a1' a2' a3' s10' t5' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt a0segs Q (MS (RL ra' a0' a1' a2' a3' t (LR t) s10' t5' (Z_to_bv 64 A)) F (Z_to_bv 64 0x902f0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 a1 (Z_to_bv 64 (bw_live b1)) a3 t (LR t) s10 (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x90294) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t i tgt n H bs bo b1 m ra a0 a1 a3 s10 Ht Hi Hi0 Htg. cbv zeta. intros OK Eb1 NL MEM IHn K.
    pose proof (put_lens_row_NZM n (bsW bo 1 0) LENA t (i + 1) tgt) as NZ1. unfold NZM in NZ1.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    pose proof (Z.mod_pos_bound (bw_live bo) 8 ltac:(lia)) as MB.
    assert (EBW : bsW bo 1 0 = BW (bw_buff b1) (bw_live b1 + 1) (bw_numZ b1) (bw_zb b1)).
    { unfold bsW. rewrite <- Eb1. f_equal. change 4294967296%Z with M32. rewrite lor_shl0. reflexivity. }
    assert (OK2 : bw_ok (bsW bo 1 0)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (IHn (i + 1)%Z tgt H bs (bsW bo 1 0) mm _ _ _ _ _ _);
        [st_eq| exact Ht| lia| lia| lia| exact Htg| exact OK2| exact NL| rewrite EBW; closeMD| exact K] end.
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens_row fst snd] in K. wstep.
      lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      enter_with (K mm _ _ _ _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_lens_pre : forall (t i tgt : Z) (n : nat) (H : sdw) (bs : list byte) (bo : bw) (m : word -> option byte) (ra a0 a1 a3 s10 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (1 <= tgt <= 17)%Z ->
    let r := sm_put_lens_row n (bsW bo 1 0) LENA t (i + 1) tgt in
    bw_ok bo -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs bo m ->
    LROW n t ->
    (forall m' (ra' a0' a1' a2' a3' s10' t5' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt a0segs Q (MS (RL ra' a0' a1' a2' a3' t (LR t) s10' t5' (Z_to_bv 64 A)) F (Z_to_bv 64 0x902f0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 a1 (Z_to_bv 64 (bw_live bo)) a3 t (LR t) s10 (Z_to_bv 64 tgt) (Z_to_bv 64 i)) F (Z_to_bv 64 0x901ec) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t i tgt n H bs bo m ra a0 a1 a3 s10 Ht Hi Hi0 Htg. cbv zeta. intros OK NL MEM IHn K.
    pose proof (put_lens_row_NZM n (bsW bo 1 0) LENA t (i + 1) tgt) as NZ1. unfold NZM in NZ1.
    pose proof (bsW_NZM bo 1 0) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL bo OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (A0_lens_fin t i tgt n H bs bo bo m _ _ _ _ _); [exact Ht| lia| lia| exact Htg| exact OK| | exact NL| closeMD| exact IHn| exact K].
      unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live bo)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
    - enter_with (FLX fl_8fed4 BS_FUEL H bs bo m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes bo 1 0) as [BB _]. rewrite <- BB. lia. }
      intros b1 m' a1' a0' a3' Eb1 MEM' L1.
      eapply (A0_lens_fin t i tgt n H bs bo b1 m' _ _ _ _ _); [exact Ht| lia| lia| exact Htg| exact OK| exact Eb1| exact NL| exact MEM'| exact IHn| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_lens_mid : forall (t i curr tgt SHl : Z) (n : nat) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a2 a3 : word),
    (0 <= t < nG)%Z -> (i + Z.of_nat (S n) = A)%Z -> (0 <= i)%Z -> (tgt = zget LENA (258 * t + i)) -> saddr (LR t + i) SHl ->
    (tgt <= curr <= 17)%Z ->
    let rd := sm_put_down 40 b curr tgt in
    let r := sm_put_lens_row n (bsW (fst rd) 1 0) LENA t (i + 1) (snd rd) in
    bw_ok b -> (bw_numZ (fst r) <= LIM)%Z -> MD H bs b m ->
    LROW n t ->
    (forall m' (ra' a0' a1' a2' a3' s10' t5' : word),
        MD H bs (fst r) m' -> bw_ok (fst r) ->
        evt a0segs Q (MS (RL ra' a0' a1' a2' a3' t (LR t) s10' t5' (Z_to_bv 64 A)) F (Z_to_bv 64 0x902f0) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (LR t + i)) a2 a3 t (LR t) (Z_to_bv 64 SHl) (Z_to_bv 64 curr) (Z_to_bv 64 i)) F (Z_to_bv 64 0x900c0) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t i curr tgt SHl n H bs b m ra a0 a2 a3 Ht Hi Hi0 Htgt AS Hc. cbv zeta. intros OK NL MEM IHn K.
    destruct (LENF t i Ht ltac:(lia)) as [ZD ZR]. rewrite <- Htgt in ZR.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    arun.
    rdlen t i tgt Htgt ZD ZR.
    (* [comment removed for export] *)
    arun. if_cases Kc2; zify_cond_z Kc2.
    - (* [comment removed for export] *)
      assert (ED : sm_put_down 40 b curr tgt = (b, curr)).
      { change 40%nat with (S 39). rewrite put_down_S. replace (tgt <? curr)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite ED in NL, K. cbn [fst snd] in NL, K. assert (Ec : curr = tgt) by lia. subst curr.
      eapply (A0_lens_pre t i tgt n H bs b m _ _ _ _ _); [exact Ht| lia| lia| lia| exact OK| exact NL| closeMD| exact IHn| exact K].
    - (* [comment removed for export] *)
      destruct (sm_put_down 40 b curr tgt) as [b2 c2] eqn:ED. cbn [fst snd] in NL, K.
      pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1.
      pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
      enter_with (A0_down_loop 40%nat t i curr tgt SHl H bs b m _ _ _); [st_eq| exact Ht| lia| exact Htgt| exact AS| lia| cbn; lia| exact OK| rewrite ED; cbn [fst]; lia| closeMD|].
      rewrite ED. cbn [fst snd]. intros m' ra' a0' a3' MEM' OK' ->.
      eapply (A0_lens_pre t i tgt n H bs b2 m' _ _ _ _ _); [exact Ht| lia| lia| lia| exact OK'| exact NL| exact MEM'| exact IHn| exact K].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_lens_inner : forall (n : nat) (t : Z), LROW n t.
  Proof using All.
    induction n as [|n IH]; intros t; unfold LROW; [lia|].
    intros i curr H bs b m ra a0 a1 a2 a3 s10 Ht Hi Hi0 _ Hc. cbv zeta. intros OK NL MEM K.
    destruct (LENF t i Ht ltac:(lia)) as [ZD ZR].
    rewrite put_lens_row_S in NL, K. cbv zeta in NL, K.
    set (tgt := zget LENA (258 * t + i)) in *.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    (* [comment removed for export] *)
    arun.
    openVW VW.
    pose proof (ovb_read1 a0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + i) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta. fold tgt. rewrite (unsigned_lit8 tgt) by lia.
    pose proof (saddr_intro (LR t + i)) as AS. set (SHl := ((LR t + i) / 8 + 2147450880)%Z) in *. clearbody SHl.
    (* [comment removed for export] *)
    wstep; if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      assert (EU : sm_put_up 40 b curr tgt = (b, curr)).
      { change 40%nat with (S 39). rewrite put_up_S. replace (curr <? tgt)%Z with false by (symmetry; apply Z.ltb_ge; lia). reflexivity. }
      rewrite EU in NL, K.
      eapply (A0_lens_mid t i curr tgt SHl n H bs b m _ _ _ _); [exact Ht| lia| lia| reflexivity| exact AS| lia| exact OK| | closeMD| exact (IH t)| ].
      + destruct (sm_put_down 40 b curr tgt) as [b2 c2]. cbn [fst snd]. exact NL.
      + destruct (sm_put_down 40 b curr tgt) as [b2 c2]. cbn [fst snd]. exact K.
    - (* [comment removed for export] *)
      destruct (sm_put_up 40 b curr tgt) as [b1 c1] eqn:EU.
      pose proof (put_down_NZM 40 b1 c1 tgt) as NZd. unfold NZM in NZd.
      destruct (sm_put_down 40 b1 c1 tgt) as [b2 c2] eqn:ED.
      pose proof (put_lens_row_NZM n (bsW b2 1 0) LENA t (i + 1) c2) as NZ1. unfold NZM in NZ1. cbn [fst] in NZd, NZ1.
      pose proof (bsW_NZM b2 1 0) as NZ0. unfold NZM in NZ0.
      arun_to 0x8ffb0%Z.
      enter_with (A0_up_loop 40%nat t i curr tgt SHl H bs b m _ _ _); [st_eq| exact Ht| lia| reflexivity| exact AS| lia| cbn; lia| exact OK| rewrite EU; cbn [fst]; lia| closeMD|].
      rewrite EU. cbn [fst snd]. intros m' ra' a0' a2' a3' MEM' OK' Ec1. subst c1.
      eapply (A0_lens_mid t i tgt tgt SHl n H bs b1 m' _ _ _ _); [exact Ht| lia| lia| reflexivity| exact AS| lia| exact OK'| | exact MEM'| exact (IH t)| ].
      + rewrite ED. cbn [fst snd]. exact NL.
      + rewrite ED. cbn [fst snd]. exact K.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Notation RLo ra a0 a1 a2 a3 t a5 s10 t5 t6 :=
    (RD ra (Z_to_bv 64 27) (Z_to_bv 64 (-1)) (Z_to_bv 64 30) a0 a1 a2 a3 (Z_to_bv 64 t) a5 (Z_to_bv 64 8) (Z_to_bv 64 15) s10 (Z_to_bv 64 2) (Z_to_bv 64 3) t5 t6).

  Lemma A0_lens5_tail : forall (t curr : Z) (H : sdw) (bs : list byte) (b b1 : bw) (m : word -> option byte) (ra a0 a2 a3 s10 t6 : word),
    (0 <= t < nG)%Z -> (curr = zget LENA (258 * t + 0)) ->
    let bf := bsW b 5 curr in
    bw_ok b -> b1 = bs_needw BS_FUEL b -> (bw_numZ bf <= LIM)%Z -> (0 <= bw_live b1 < 8)%Z -> MD H bs b1 m ->
    (forall m' (a0' a1' a2' a3' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt a0segs Q (MS (RL ra a0' a1' a2' a3' t (LR t) s10 (Z_to_bv 64 curr) (Z_to_bv 64 0)) F (Z_to_bv 64 0x8ff88) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 (Z_to_bv 64 (bw_live b1)) a2 a3 t (LR t) s10 (Z_to_bv 64 curr) t6) F (Z_to_bv 64 0x8ff50) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t curr H bs b b1 m ra a0 a2 a3 s10 t6 Ht Hc. cbv zeta. intros OK Eb1 NL L1 MEM K.
    destruct (LENF t 0 Ht ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe.
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(cps_destruct OK as (?&?&?); unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    rewrite <- Eb1 in OK1, M1, N1. cps_destruct OK1 as (OK1b & OK1l & OK1n). cps_pose OK as (OKb & OKl & OKn).
    assert (EBW : bsW b 5 curr = BW (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296)) (bw_live b1 + 5) (bw_numZ b1) (bw_zb b1))
      by (unfold bsW; rewrite <- Eb1; reflexivity).
    assert (OK2 : bw_ok (bsW b 5 curr)) by (apply bw_ok_bsW; [exact OK| lia| lia]).
    assert (XR : (0 <= Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296) < 4294967296)%Z).
    { change 4294967296%Z with (2^32)%Z. apply lor_lt_pow2; [lia| apply Z.mod_pos_bound; lia]. }
    (* [comment removed for export] *)
    arun_to 0x8ff7c%Z.
    rewrite (Z.mod_small (27 - bw_live b1) 32) in * by lia.
    reword_C4 EH2 0%nat (Z.lor (bw_buff b1) (Z.shiftl curr (32 - bw_live b1 - 5) mod 4294967296))%Z.
    { rewrite (low32_or_shifted curr _ (sx32 (Z_to_bv 64 (bw_buff b1))) (bw_buff b1)) by (first [rewrite low32_sx32, low32_lit; apply Z.mod_small; lia | lia]).
      replace (27 - bw_live b1)%Z with (32 - bw_live b1 - 5)%Z by lia.
      rewrite low32_small; [reflexivity| exact XR]. }
    (* [comment removed for export] *)
    openVW VW. wstep. closeVW. wstep; if_cases Kc; zify_cond_z Kc; [exfalso; lia|]. wstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    enter_with (K mm _ _ _ _); [st_eq| rewrite EBW; closeMD| exact OK2] end.
  Qed.

  (* [comment removed for export] *)
  Lemma A0_lens_body : forall (t curr : Z) (b1 : bw) (c1 : Z) (n : nat) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a1 a2 a3 s10 : word),
    (t + Z.of_nat (S n) = nG)%Z -> (0 <= t)%Z -> (curr = zget LENA (258 * t + 0)) ->
    sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr = (b1, c1) ->
    let bf := sm_put_lens n b1 LENA A (t + 1) in
    bw_ok (bsW b 5 curr) -> (bw_numZ bf <= LIM)%Z -> MD H bs (bsW b 5 curr) m ->
    (* [comment removed for export] *)
    (forall (t : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a1 a2 a3 a5 s10 t5 t6 : word),
      (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
      let bf := sm_put_lens n b LENA A t in
      bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
      (forall m' (ra' a0' a1' a2' a3' a5' s10' t5' t6' : word),
          MD H bs bf m' -> bw_ok bf ->
          evt a0segs Q (MS (RLo ra' a0' a1' a2' a3' nG a5' s10' t5' t6') F (Z_to_bv 64 0x90334) fc None m' (seg_rom a0segs))) ->
      evt a0segs Q (MS (RLo ra a0 a1 a2 a3 t a5 s10 t5 t6) F (Z_to_bv 64 0x8fe78) fc None m (seg_rom a0segs))) ->
    (forall m' (ra' a0' a1' a2' a3' a5' s10' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt a0segs Q (MS (RLo ra' a0' a1' a2' a3' nG a5' s10' t5' t6') F (Z_to_bv 64 0x90334) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RL ra a0 a1 a2 a3 t (LR t) s10 (Z_to_bv 64 curr) (Z_to_bv 64 0)) F (Z_to_bv 64 0x8ff88) fc None m (seg_rom a0segs)).
  Proof using All.
    intros t curr b1 c1 n H bs b m ra a0 a1 a2 a3 s10 Ht Ht0 Hc ER. cbv zeta. intros OK NL MEM IHn K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR]. rewrite <- Hc in ZR.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    eapply (A0_lens_inner (Z.to_nat A) t 0%Z curr H bs (bsW b 5 curr) m); [lia| lia| lia| lia| lia| exact OK| rewrite ER; cbn [fst]; lia| exact MEM|].
    rewrite ER. cbn [fst]. clear MEM. intros m' ra' a0' a1' a2' a3' s10' t5' MEM OK1.
    openCX. openMD MEM. cps_pose OK1 as (OK1b & OK1l & OK1n).
    (* [comment removed for export] *)
    wstep. openVW VW. wstep. closeVW. wstep; if_cases Kc; zify_cond_z Kc.
    - eapply (IHn (t + 1)%Z H bs b1 m' _ _ _ _ _ _ _ _ _); [lia| lia| lia| exact OK1| exact NL| closeMD| exact K].
    - assert (n = 0%nat) by lia. subst n. cbn [sm_put_lens] in K. wstep.
      enter_with (K m' _ _ _ _ _ _ _ _ _); [st_eq| closeMD| exact OK1].
  Qed.

  (* [comment removed for export] *)
  Lemma A0_lens_outer : forall (n : nat) (t : Z) (H : sdw) (bs : list byte) (b : bw) (m : word -> option byte) (ra a0 a1 a2 a3 a5 s10 t5 t6 : word),
    (t + Z.of_nat n = nG)%Z -> (0 <= t)%Z -> (1 <= n)%nat ->
    let bf := sm_put_lens n b LENA A t in
    bw_ok b -> (bw_numZ bf <= LIM)%Z -> MD H bs b m ->
    (forall m' (ra' a0' a1' a2' a3' a5' s10' t5' t6' : word),
        MD H bs bf m' -> bw_ok bf ->
        evt a0segs Q (MS (RLo ra' a0' a1' a2' a3' nG a5' s10' t5' t6') F (Z_to_bv 64 0x90334) fc None m' (seg_rom a0segs))) ->
    evt a0segs Q (MS (RLo ra a0 a1 a2 a3 t a5 s10 t5 t6) F (Z_to_bv 64 0x8fe78) fc None m (seg_rom a0segs)).
  Proof using All.
    induction n as [|n IH]; [lia|].
    intros t H bs b m ra a0 a1 a2 a3 a5 s10 t5 t6 Ht Ht0 _. cbv zeta. intros OK NL MEM K.
    destruct (LENF t 0 ltac:(lia) ltac:(lia)) as [ZD ZR].
    rewrite put_lens_S in NL, K. cbv zeta in NL, K.
    set (curr := zget LENA (258 * t + 0)) in *.
    destruct (sm_put_lens_row (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as [b1 c1] eqn:ER.
    pose proof (put_lens_NZM n b1 LENA A (t + 1)) as NZ2. unfold NZM in NZ2.
    pose proof (put_lens_row_NZM (Z.to_nat A) (bsW b 5 curr) LENA t 0 curr) as NZ1. rewrite ER in NZ1. unfold NZM in NZ1. cbn [fst] in NZ1.
    pose proof (bsW_NZM b 5 curr) as NZ0. unfold NZM in NZ0.
    openCX. openMD MEM. unfold ESTATE_SIZE in SHe. cps_pose OK as (OKb & OKl & OKn).
    cps_pose (bs_needw_post BS_FUEL b OK ltac:(unfold BS_FUEL; cbn; lia)) as (OK1 & M1 & N1).
    (* [comment removed for export] *)
    openVW VW. arun.
    pose proof (ovb_read1 a0segs m (E + 37708) LENA (jseg J 37708 1548) 1548 (258 * t + 0) _ LEN ltac:(lia) ZD ltac:(cbv delta [wa]; f_equal; lia)) as RD.
    closeVW.
    wstep. clear RD. cbv beta. fold curr. rewrite (unsigned_lit8 curr) by lia.
    (* [comment removed for export] *)
    arun. if_cases Kc; zify_cond_z Kc.
    - (* [comment removed for export] *)
      enter_with (A0_lens5_tail t curr H bs b b m _ _ _ _ _ _); [st_eq| lia| reflexivity| exact OK| | lia| lia| closeMD|].
      { unfold BS_FUEL. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity. }
      intros m' a0' a1' a2' a3' MEM' OK'.
      eapply (A0_lens_body t curr b1 c1 n H bs b m' _ _ _ _ _ _); [lia| lia| reflexivity| exact ER| exact OK'| exact NL| exact MEM'| exact IH| exact K].
    - (* [comment removed for export] *)
      enter_with (FLX fl_8fb90 BS_FUEL H bs b m); [st_eq| exact OK| lia| unfold BS_FUEL; cbn; lia| | closeMD|].
      { pose proof (bsW_bytes b 5 curr) as [BB _]. rewrite <- BB. lia. }
      intros b0 m' t6' a2' a3' Eb0 MEM' L1.
      enter_with (A0_lens5_tail t curr H bs b b0 m' _ _ _ _ _ _); [st_eq| lia| reflexivity| exact OK| exact Eb0| lia| exact L1| exact MEM'|].
      intros m'' a0'' a1'' a2'' a3'' MEM'' OK''.
      eapply (A0_lens_body t curr b1 c1 n H bs b m'' _ _ _ _ _ _); [lia| lia| reflexivity| exact ER| exact OK''| exact NL| exact MEM''| exact IH| exact K].
  Qed.
End SDF.
End ACeilS1.
