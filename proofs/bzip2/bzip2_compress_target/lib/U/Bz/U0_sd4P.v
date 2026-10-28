(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import PropExec.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import Tac WalkLib.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require Import SegsS0.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzTac BzTac2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzArr BzCMem BzCStream BzCState BzCMtf BzArrD BzCLemmas1 CmpMem BzSepTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut CmpCutSM CmpCutSmA CmpCutSD CmpSdKit CmpSdTac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpArith.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import BzCNumZ BzCLemmasSd BzCLemmasSd2.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpArith2 BzWalkArith2 BzWalkArith4.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StepFast.
From Ltac2 Require Import Ltac2.
Set Default Proof Mode "Classic".
From Stdlib Require Lia. Unset Lia Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeilTac.
Import ListNotations. Open Scope bv_scope.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib Require Import ACeil.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import BzParams.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import CmpCut6.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require Import CmpLiaP.
Local Ltac Lib.Step.step_core segs R F pc fc rv m ro ::= StepFast.sf_step_core.
Local Ltac Lib.Step.zstep ::= StepFast.sf_zstep.
#[local] Ltac2 Set StepFast.sf_foldgoal := Ltac2.Init.true.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require StoreFast StoreFastZ StoreFastC.
Local Ltac Lib.Step.transport_chunks segs m a bs ::= StoreFast.transport_chunks_fast segs m a bs.
Local Ltac Lib.Tac.footprint_after_store segs m a bs ::= StoreFast.footprint_after_store_fast segs m a bs.
Local Ltac Lib.Step.mem_after_store ::= first [ StoreFastC.mem_after_store_fastzc | StoreFastZ.mem_after_store_fastz | StoreFast.mem_after_store_fast ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpFast.
Local Ltac U.Bz.BzTac.mlia ::= CmpFast.mlia_fast.
Local Ltac Lib.ZBridge.mlia ::= CmpFast.mlia_fast.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Lib Require RangeFast RangeFastEnv.
#[local] Ltac2 Set RangeFast.RF.rc_atom_facts := RangeFastEnv.env_atom_facts.
Local Ltac Lib.ZBridge.flia ::= RangeFast.rc_decide ltac:(first [ assumption | Lib.ZBridge.slim; lia | lia ]).
Local Ltac Lib.ZBridge.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
Local Ltac U.Bz.BzTac.mlia ::= RangeFast.rc_decide ltac:(CmpFast.mlia_fast).
#[local] Ltac2 Set RangeFast.RF.rc_or_boxes := fun () => [constr:(@id); constr:(Lib.StoreFast.sf_hide)].
Local Ltac Lib.StoreFast.tlia ::= first [ Zify.zify; xlia zchecker | RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | lia ] ].
Local Ltac Bz.BzSepTac.tlia2 ::= first [ RangeFast.rc_prune_lia | Lib.StoreFast.sf_unhide; Bz.BzSepTac.unhide_disj; first [ Lib.StoreFast.zify_prune_neg; Zify.zify; xlia zchecker | Lib.StoreFast.zify_prune_plain; Zify.zify; xlia zchecker | Zify.zify; xlia zchecker ] ].
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpLiaC.
Local Ltac lia ::= CmpLiaC.lia_c.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Bz Require CmpSepV.
Local Ltac Lib.Step.slia ::= CmpSepV.slia_v.
Local Ltac Lib.StoreFast.tslia ::= CmpSepV.tslia_v.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require CmpStEq.
Local Ltac U.Bz.BzTac.st_eq ::= CmpStEq.st_eq_fast.
Local Ltac simpl_arr_sizes ::= CmpFast.sas10_all.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.Lib Require Import CpsOpen.
Import OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.CmpArith2.CmpSdArith OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz.BzCLemmasSd2.BzCLemmasSd3.
From OssFuzzTheorems.Proofs.bzip2.bzip2_compress_target.lib.U.Bz Require Import UKit.

Record sdw := SDW { h888 : word; h896 : word; h904 : word; h912 : word; h920 : word; h928 : word; h936 : word; h944 : word;
                    h952 : word; h960 : word; h968 : word; h976 : word; h984 : word; h992 : word; h1000 : word; h1008 : word;
                    h1016 : word; h1024 : word; h1032 : word }.
Definition sd_hc (H : sdw) : list cell :=
  [C8 (h888 H); C8 (h896 H); C8 (h904 H); C8 (h912 H); C8 (h920 H); C8 (h928 H); C8 (h936 H); C8 (h944 H); C8 (h952 H);
   C8 (h960 H); C8 (h968 H); C8 (h976 H); C8 (h984 H); C8 (h992 H); C8 (h1000 H); C8 (h1008 H); C8 (h1016 H); C8 (h1024 H);
   C8 (h1032 H)].

Section ACeilS0. Context {BZP : BzParams} {ACEIL__ : ACeil}.
Definition sdWP (cx : cctx) (P : Z) : list (Z * Z) :=
  [(c_E cx + 116, c_E cx + 120); (c_E cx + 640, c_E cx + 648); (c_A2 cx, c_A2 cx + ARR2_SIZE); (P + 888, P + 1040); (P + 1044, P + 1060)].
Definition MA3 (cx : cctx) (g : eg) (e : est) (nG P : Z) (m0 : word -> option byte) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte) : Prop :=
  rw_cells s0segs m (c_E cx) (EHEAD1 cx g (est_set_bw e b)) /\
  rw_cells s0segs m (c_E cx + 640) (EHEAD2 cx g (est_set_bw e b)) /\
  u8arr s0segs m (c_A2 cx) (zb8 (zbl (e_arr2 e) (e_nblock e) b) ARR2_SIZE) /\
  rw_cells s0segs m (P + 888) (sd_hc H) /\
  u8arr s0segs m (P + 1044) i16 /\
  mem_inv s0segs m /\
  munch (sdWP cx P) m0 m /\ wmono s0segs m0 m.
Definition sd_ro (cx : cctx) (e : est) (m : word -> option byte) : Prop :=
  u8arr s0segs m (c_A1 cx) (zb8 (e_arr1 e) ARR1_SIZE) /\
  u8arr s0segs m (c_E cx + 128) (ovb (e_inUse e) (jseg (c_J cx) 128 256) 256) /\
  u8arr s0segs m (c_E cx + 19706) (ovb (e_selectorMtf e) (jseg (c_J cx) 19706 18002) 18002) /\
  u8arr s0segs m (c_E cx + 1704) (ovb (e_selector e) (jseg (c_J cx) 1704 18002) 18002) /\
  u8arr s0segs m (c_E cx + 37708) (ovb (e_len e) (jseg (c_J cx) 37708 1548) 1548) /\
  u32arr s0segs m (c_E cx + 39256) (ovw (e_code e) (jseg (c_J cx) 39256 6192) 1548) /\
  True.
Definition sd_vw (cx : cctx) (e : est) (P : Z) (m0 : word -> option byte) : Prop :=
  forall m : word -> option byte, munch (sdWP cx P) m0 m -> sd_ro cx e m.
End ACeilS0.
Ltac openVW VW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      lazymatch goal with
      | MU' : munch _ _ mm |- _ => pose proof (VW mm ltac:(unfold sdWP; exact MU')) as (AR1 & INU & SLM & SEL & LEN & COD & LOA)
      end
  end.
Ltac closeVW :=
  let AR1 := ident:(AR1) in let INU := ident:(INU) in let SLM := ident:(SLM) in let SEL := ident:(SEL) in let LEN := ident:(LEN) in
  let COD := ident:(COD) in let LOA := ident:(LOA) in
  clear AR1 INU SLM SEL LEN COD LOA.

Ltac cbn_est_in H :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw] in H.
Ltac cbn_est :=
  cbn [e_mode e_state e_avail_in_expect e_arr1 e_arr2 e_ftab e_origPtr e_state_in_ch e_state_in_len e_nblock e_state_out_pos
       e_nInUse e_inUse e_unseqToSeq e_bw e_blockCRC e_combinedCRC e_blockNo e_nMTF e_mtfFreq e_selector e_selectorMtf
       e_len e_code e_rfreq e_len_pack est_set_bw].
Ltac openMA3 Gmtf Gbs Gzb H :=
  let EH1 := ident:(EH1) in let EH2 := ident:(EH2) in let HI := ident:(HI) in let MU := ident:(MU) in
  cps_destruct H as (?EH1 & ?EH2 & ?AR2 & ?HI & ?I16 & ?MI & ?MU & ?WM);
  unfold sdWP in MU; unfold sd_hc in HI;
  unfold EHEAD1, EHEAD2 in EH1, EH2; cbn_est_in EH1; cbn_est_in EH2;
  rewrite Gbs, Gmtf in EH2; rewrite Gzb, Gmtf in EH1.
Ltac closeMA3 Gmtf Gbs Gzb :=
  split; [|split; [| repeat (split; [eassumption|]); eassumption]];
  [ unfold EHEAD1; cbn_est; rewrite Gzb, Gmtf; eassumption
  | unfold EHEAD2; cbn_est; rewrite Gbs, Gmtf; eassumption ].

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

Section SDFL.
  Variables (cx : cctx) (g : eg) (e : est) (Q : machine_state -> Prop).
  Variables (gp tp : word) (F : bvmap 5 word) (fc : bv 32).
  Variable P : Z.
  Notation E := (c_E cx). Notation A1 := (c_A1 cx). Notation A2 := (c_A2 cx). Notation J := (c_J cx).
  Notation nblock := (e_nblock e).
  Hypothesis CX : cctx_ok cx. Hypothesis SEP : cctx_sep cx.
  Hypothesis Gmtf : g_mtf g = true. Hypothesis Gbs : g_bs g = true. Hypothesis Gzb : g_zbits g = Z_to_bv 64 (A2 + nblock).
  Hypothesis Hnb : (0 <= nblock)%Z.
  Hypothesis CEP : (CEIL <= P)%Z. Hypothesis PHI : (P + 1200 <= 18446744073709551616)%Z.
  Variable LIM : Z. Hypothesis HLIM : (nblock + LIM <= ARR2_SIZE)%Z.
  Variable m0 : word -> option byte.
  Variable nG : Z.
  Notation MD H i16 b m := (MA3 cx g e nG P m0 H i16 b m).
  Notation cP := (Z_to_bv 64 P). Notation cE := (Z_to_bv 64 E). Notation c7 := (Z_to_bv 64 7).
  Ltac openCX := openCX_d CX SEP CEP.
  Ltac openMD H := openMA3 Gmtf Gbs Gzb H.
  Ltac closeMD := closeMA3 Gmtf Gbs Gzb.
  Ltac fl_byte X4 := rewrite X4, shiftr_div24; rewrite unsigned_lit by lia; reflexivity.

  Lemma ufl_1b718 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned t5 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s1' s2' t5' t6' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned t5' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1' a0 (Z_to_bv 64 (bw_numZ b1)) a2 a3 a4 a5 a6 c7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (bw_live b1)) t5' t6')
                         F (Z_to_bv 64 0x1b790) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 (Z_to_bv 64 (bw_numZ b)) a2 a3 a4 a5 a6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b718) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1b754%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1b78c%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s1' s2' t5' t6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1b7d4 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned t5 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s1' s2' t5' t6' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned t5' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1' a0 (Z_to_bv 64 (bw_numZ b1)) a2 a3 a4 a5 a6 c7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 (Z_to_bv 64 (bw_live b1)) t5' t6')
                         F (Z_to_bv 64 0x1b84c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 (Z_to_bv 64 (bw_numZ b)) a2 a3 a4 a5 a6 c7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b7d4) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a2 a3 a4 a5 a6 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1b810%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1b848%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s1' s2' t5' t6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1b8e8 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s3' s4' s5' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned s2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 c7 t2 cE (Z_to_bv 64 (bw_live b1)) a0 (Z_to_bv 64 (bw_numZ b1)) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1b960) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 c7 t2 cE s1 a0 (Z_to_bv 64 (bw_numZ b)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b8e8) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1b924%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1b95c%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s3' s4' s5' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1b9a4 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s3' s4' s5' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned s2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 c7 t2 cE (Z_to_bv 64 (bw_live b1)) a0 (Z_to_bv 64 (bw_numZ b1)) a2 a3 a4 a5 a6 a7 s2' s3' s4' s5' s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1ba1c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 c7 t2 cE s1 a0 (Z_to_bv 64 (bw_numZ b)) a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1b9a4) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t2 s1 a0 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1b9e0%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1ba18%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s3' s4' s5' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1ba94 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a4 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a4' a5' a6' a7' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned a4' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b1)) a1 c7 (Z_to_bv 64 (bw_live b1)) a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1bb0c) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b)) a1 c7 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1ba94) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bad0%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bb08%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a4' a5' a6' a7' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1bb60 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned a2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (a2' a4' a5' a6' a7' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned a2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b1)) a1 a2' c7 a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (bw_live b1)) t6)
                         F (Z_to_bv 64 0x1bbd8) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b)) a1 a2 c7 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1bb60) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a1 a2 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bb9c%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bbd4%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' a2' a4' a5' a6' a7' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1bc84 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned t2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (t2' s2' s3' s4' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned t2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2' cE s1 (Z_to_bv 64 (bw_numZ b1)) a1 a2 a3 c7 a5 a6 a7 s2' s3' s4' s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (bw_live b1)) t6)
                         F (Z_to_bv 64 0x1bcfc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b)) a1 a2 a3 c7 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1bc84) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bcc0%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bcf8%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' t2' s2' s3' s4' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1bd48 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned t2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (t2' s1' s2' t6' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned t2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2' cE s1' (Z_to_bv 64 (bw_numZ b1)) a1 a2 a3 c7 a5 a6 a7 s2' s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 (Z_to_bv 64 (bw_live b1)) t6')
                         F (Z_to_bv 64 0x1bdc0) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 (Z_to_bv 64 (bw_numZ b)) a1 a2 a3 c7 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1bd48) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a1 a2 a3 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bd84%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bdbc%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' t2' s1' s2' t6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1be6c : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned t5 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s5' t5' t6' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned t5' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2' (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5' s6 s7 s8 s9 s10 s11 t3 t4 t5' t6')
                         F (Z_to_bv 64 0x1bee4) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2 (Z_to_bv 64 (bw_numZ b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1be6c) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bea8%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bee0%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s5' t5' t6' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1bf54 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s6' s8' s10' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned s2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2' (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5 s6' s7 s8' s9 s10' s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1bfcc) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2 (Z_to_bv 64 (bw_numZ b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1bf54) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1bf90%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1bfc8%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s6' s8' s10' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1c018 : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s6' s8' s10' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned s2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2' (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5 s6' s7 s8' s9 s10' s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1c090) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2 (Z_to_bv 64 (bw_numZ b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1c018) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1c054%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1c08c%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s6' s8' s10' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

  Lemma ufl_1c0dc : forall (f : nat) (H : sdw) (i16 : list byte) (b : bw) (m : word -> option byte)
      (ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word),
    bw_ok b -> (8 <= bw_live b)%Z -> (bw_live b < 8 * Z.of_nat f)%Z -> (bw_numZ (bs_needw f b) <= LIM)%Z ->
    (bv_unsigned s2 mod 4294967296 = bw_buff b)%Z ->
    MD H i16 b m ->
    (forall b1 m' (s2' s5' s6' s8' : word), b1 = bs_needw f b -> MD H i16 b1 m' ->
        (bv_unsigned s2' mod 4294967296 = bw_buff b1)%Z -> (0 <= bw_live b1 < 8)%Z ->
        evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2' (Z_to_bv 64 (bw_numZ b1)) (Z_to_bv 64 (bw_live b1)) s5' s6' s7 s8' s9 s10 s11 t3 t4 t5 t6)
                         F (Z_to_bv 64 0x1c154) fc None m' (seg_rom s0segs))) ->
    evt s0segs Q (MS (mkR ra cP gp tp t0 t1 t2 cE s1 a0 a1 a2 a3 a4 c7 a6 a7 s2 (Z_to_bv 64 (bw_numZ b)) s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x1c0dc) fc None m (seg_rom s0segs)).
  Proof using All.
    induction f as [|f IH]; intros H i16 b m ra t0 t1 t2 s1 a0 a1 a2 a3 a4 a6 a7 s2 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 OK L8 Lf NL X4 MEM K; [lia|].
    openCX. openMD MEM.
    cps_destruct OK as (OKb & OKl & OKn).
    pose proof (needw_NZM f (bw_emit b)) as NZ1. unfold NZM in NZ1. cbn [bs_needw] in NL.
    replace (8 <=? bw_live b)%Z with true in NL by (symmetry; apply Z.leb_le; lia).
    cps_pose (bw_emit_shape b) as (Es1 & Es2 & Es3).
    pose proof (zb8_length (zbl (e_arr2 e) nblock b) ARR2_SIZE ltac:(lia)) as LA2.
    urun_to 0x1c118%Z.
    pose proof (u8arr_store_ok s0segs m A2 _ (nblock + bw_numZ b) _ AR2 ltac:(rewrite zb8_length_nat; lia) eq_refl) as SO.
    ustep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ (write_to_mem _ _ (le1 ?w)) _) =>
      pose proof (zb8_write1 s0segs m A2 (zbl (e_arr2 e) nblock b) ARR2_SIZE (nblock + bw_numZ b) w AR2 ltac:(lia)) as AR2' end.
    clear AR2. store_done. rename AR2' into AR2.
    urun_to 0x1c150%Z.
    reword_C4 EH2 0%nat ((Z.shiftl (bw_buff b) 8) mod 4294967296)%Z.
    { rewrite low32_mod. apply low32_shl8_sx32. }
    replace (bw_live b + -8)%Z with (bw_live b - 8)%Z in EH2 by lia.
    lazymatch type of AR2 with u8arr _ _ _ (zb8 (wr8 _ _ ?v) _) =>
      replace (wr8 (zbl (e_arr2 e) nblock b) (nblock + bw_numZ b) v) with (zbl (e_arr2 e) nblock (bw_emit b)) in AR2 end.
    2:{ rewrite zbl_emit by lia. unfold wr8. f_equal. fl_byte X4. }
    ustep; if_cases Kc; zify_cond_z Kc.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
        enter_with (IH H i16 (bw_emit b) mm); [st_eq| unfold bw_ok; lia| lia| lia| exact NL| | closeMD|] end.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
      + intros b1 m' s2' s5' s6' s8' Eb1 MEM' X4' L1. eapply K; [|exact MEM'| exact X4'| exact L1].
        rewrite Eb1. cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia). reflexivity.
    - lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) => enter_with (K (bw_emit b) mm); [st_eq| | closeMD| | lia] end.
      + cbn [bs_needw]. replace (8 <=? bw_live b)%Z with true by (symmetry; apply Z.leb_le; lia).
        destruct f; cbn [bs_needw]; [reflexivity|]. replace (8 <=? bw_live (bw_emit b))%Z with false by (symmetry; apply Z.leb_gt; lia). reflexivity.
      + unfold bw_emit. cbn [bw_buff]. apply low32_shl8_sx32.
  Qed.

End SDFL.
End ACeilS1.
