(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-11. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Tac Image Arr Frame Mem MState.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Malloc Require Import MallocBlocks Malloc_iface.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.MallocU Require Import RMallocRep.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Spec Require Import Prelim ZApi ZHarness ZInst Stdio.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.U Require Import Zlib_iface Z_dview Z_drep Z_dkit Z_zrd Z_trees_iface Z_defl_iface Z_defl_path Z_defl Z_slow Z_dinit_kit.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require ZIface DeflateState Deflate DeflateSafe RefDeflateRel RefDeflSafeI1 RefDeflSafeI2.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require RefDeflSafeLF.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require BoundSlow.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z Require BoundCall BoundPat ZApiInst ZApiOk ZTaint ZPat.
Import OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZIface OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateState OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.Deflate OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.DeflateSafe OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflateRel OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI1 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeI2 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.RefDeflSafeLF.RefDeflSafeI4 OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundSlow.BoundFw OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundCall OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.BoundPat OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiInst OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZApiOk OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZTaint OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Z.ZPat.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.Lib Require Import Ceiling.
From OSSVerify.Proofs.zlib.example_small_fuzzer.lib.ubsan_halts_any_exit.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wq := (Z_to_bv 64).


Lemma upd_nat_app : forall (pre post : list Z) x b, upd_nat (pre ++ x :: post) (length pre) b = pre ++ b :: post.
Proof. induction pre as [|a pre IH]; intros post x b; cbn; [reflexivity| rewrite IH; reflexivity]. Qed.

Lemma zstore_split : forall (bs pre post : list Z), (length bs <= length post)%nat ->
  zstore (pre ++ post) (Z.of_nat (length pre)) bs = pre ++ bs ++ skipn (length bs) post.
Proof.
  induction bs as [|b bs IH]; intros pre post HL; cbn; [reflexivity|].
  destruct post as [|x post]; [cbn in HL; lia|]. cbn in HL.
  unfold zupd. replace (Z.of_nat (length pre) <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
  rewrite Nat2Z.id, upd_nat_app.
  replace (pre ++ b :: post) with ((pre ++ [b]) ++ post) by (rewrite <- app_assoc; reflexivity).
  replace (Z.of_nat (length pre) + 1) with (Z.of_nat (length (pre ++ [b]))) by (rewrite length_app; cbn; lia).
  rewrite IH by lia. rewrite <- app_assoc. reflexivity.
Qed.

Lemma zstore_at : forall out o bs, 0 <= o -> (Z.to_nat o + length bs <= length out)%nat ->
  zstore out o bs = firstn (Z.to_nat o) out ++ bs ++ skipn (length bs) (skipn (Z.to_nat o) out).
Proof.
  intros out o bs Ho HL.
  pose proof (zstore_split bs (firstn (Z.to_nat o) out) (skipn (Z.to_nat o) out) ltac:(rewrite length_skipn; lia)) as E.
  rewrite firstn_skipn, length_firstn, Nat.min_l, Z2Nat.id in E by lia. exact E.
Qed.

Lemma to_bytes_app : forall l1 l2, to_bytes (l1 ++ l2) = to_bytes l1 ++ to_bytes l2.
Proof. intros. unfold to_bytes. apply map_app. Qed.
Lemma to_bytes_firstn : forall n l, to_bytes (firstn n l) = firstn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply firstn_map. Qed.
Lemma to_bytes_skipn : forall n l, to_bytes (skipn n l) = skipn n (to_bytes l).
Proof. intros. unfold to_bytes. symmetry. apply skipn_map. Qed.
Lemma to_bytes_length : forall l, length (to_bytes l) = length l.
Proof. intros. unfold to_bytes. apply length_map. Qed.

Lemma Forall_firstn_skipn : forall (P : Z -> Prop) n k l, Forall P l -> Forall P (firstn n (skipn k l)).
Proof.
  intros P n k l H. rewrite <- (firstn_skipn k l) in H. apply Forall_app in H. destruct H as [_ H].
  rewrite <- (firstn_skipn n (skipn k l)) in H. apply Forall_app in H. exact (proj1 H).
Qed.

Lemma nth_error_outv_tail : forall rest0 c i, (length (cs_out_rev c) <= length rest0)%nat -> (length (cs_out_rev c) <= i)%nat ->
  nth_error (outv rest0 c) i = nth_error rest0 i.
Proof.
  intros rest0 c i HL Hi. unfold outv.
  assert (L1 : length (zb8 (rev (cs_out_rev c))) = length (cs_out_rev c)) by (rewrite zb8_length, length_rev; reflexivity).
  rewrite nth_error_app2 by lia. rewrite L1, nth_error_skipn. f_equal. lia.
Qed.


Section PURE.
  Variables (sa : deflate_state) (d : list Z) (x : dstream) (ai ao flush : Z).
  Hypothesis DR : DREL sa x.
  Hypothesis PT : PAT sa.
  Hypothesis ZOK : zstrm_okP (dz_z x).
  Hypothesis HAI : 0 <= ai <= 1.
  Hypothesis HTIN : zs_total_in (dz_z x) + ai <= zlength d.
  Hypothesis HDL : zlength d < 2 ^ 63.
  Hypothesis HAO : 0 <= ao <= 1.
  Hypothesis HD : Forall (fun c => 0 <= c < 256) d.
  Hypothesis HFL : flush = Z_NO_FLUSH \/ flush = Z_FINISH.

  Definition czc : ZCall := zd_zcall d x ai ao.
  Definition cd0 : deflate_state := set_strm sa (cstrm_of_call czc).

  Lemma czc_len : zlength (zc_input czc) = ai.
  Proof.
    unfold czc, zd_zcall. cbn [zc_input]. unfold zfirstn, zskipn, zlength. rewrite length_firstn, length_skipn.
    unfold zlength in HTIN. destruct ZOK as ((T0 & _) & _). lia.
  Qed.

  Lemma czc_wf : dcall_wf czc.
  Proof.
    unfold dcall_wf. rewrite czc_len. split; [exact ZOK|]. split; [cbn [czc zd_zcall zc_avail_out]; lia|]. split; [lia|].
    unfold bytes_okP, czc, zd_zcall. cbn [zc_input]. unfold zfirstn, zskipn. apply Forall_firstn_skipn. exact HD.
  Qed.

  Lemma czc_path : defl_path (zc_input czc) flush (deflate_core cd0 flush) cd0.
  Proof.
    destruct (DREL_facts sa x DR) as (_ & HDD & _).
    apply (defl_path_intro sa czc flush HDD czc_wf PT HFL); [rewrite czc_len; lia| cbn [czc zd_zcall zc_avail_out]; lia].
  Qed.

  Lemma czc_SV : SV (cstrm_of_call czc) (fst (deflate_core cd0 flush)) /\ PAT (fst (deflate_core cd0 flush)) /\ fwT (fst (deflate_core cd0 flush)) = zs_total_in (dz_z x).
  Proof.
    destruct (DREL_facts sa x DR) as (_ & HDD & _). pose proof czc_wf as Hzc.
    pose proof (C0OK'_of_call czc Hzc) as HC0.
    assert (H0 : DC (cstrm_of_call czc) cd0) by (split; [apply DD_set_strm; exact HDD | apply SV_entry; exact Hzc]).
    pose proof (PAT_set_strm sa (cstrm_of_call czc) PT) as P0.
    pose proof (BoundPat.pat_core (cstrm_of_call czc) cd0 HC0 eq_refl (proj1 (proj1 H0)) flush (conj (conj H0 eq_refl) P0) HFL) as ((DCF & _) & PF).
    split; [exact (proj2 DCF)|]. split; [exact PF|].
    destruct czc_path as [[_ E] _]. rewrite E. unfold fwT, cd0. cbn [ds_strm set_strm cstrm_of_call cs_total_in cs_next_in].
    unfold czc, zd_zcall. cbn [zc_strm]. rewrite Z.sub_0_r. rewrite wrap64_mod. apply Z.mod_small. destruct ZOK as ((T0 & T1) & _). lia.
  Qed.

  Lemma zd_call_facts :
    let sF := fst (deflate_core cd0 flush) in let cF := ds_strm sF in
    let '(x', ai', ao', bs, rc) := zd_deflate d x ai ao flush in
    DREL sF x' /\ PAT sF /\ zstrm_okP (dz_z x')
    /\ rc = snd (deflate_core cd0 flush) /\ bs = rev (cs_out_rev cF)
    /\ zs_total_in (dz_z x') = cs_total_in cF /\ zs_total_out (dz_z x') = cs_total_out cF
    /\ zs_msg (dz_z x') = cs_msg cF /\ zs_data_type (dz_z x') = cs_data_type cF /\ zs_adler (dz_z x') = cs_adler cF
    /\ cs_total_in cF = zs_total_in (dz_z x) + cs_next_in cF
    /\ 0 <= cs_next_in cF <= ai /\ cs_avail_in cF = ai - cs_next_in cF /\ ai' = ai - cs_next_in cF
    /\ cs_total_out cF = wrap64 (zs_total_out (dz_z x) + Z.of_nat (length (cs_out_rev cF)))
    /\ cs_avail_out cF = ao - Z.of_nat (length (cs_out_rev cF)) /\ ao' = ao - Z.of_nat (length (cs_out_rev cF))
    /\ zlength bs = Z.of_nat (length (cs_out_rev cF))
    /\ Forall (fun c => 0 <= c < 256) bs.
  Proof.
    cbv zeta. destruct (DREL_facts sa x DR) as (_ & HDD & _). pose proof czc_wf as Hzc.
    pose proof (DREL_zd sa d x ai ao flush DR Hzc HFL) as ZD. cbv zeta in ZD. fold czc in ZD.
    destruct (zd_deflate d x ai ao flush) as [[[[x' ai'] ao'] bs] rc].
    destruct czc_SV as (SVF & PATF & FT).
    unfold deflate_m in ZD. fold cd0 in ZD.
    destruct (deflate_core cd0 flush) as [sF rcF] eqn:EC. cbn [fst snd] in *.
    destruct ZD as (DR' & EZ & EAI & EAO & EBS & ERC).
    unfold zret_of_cs in EZ, EAI, EAO, EBS, ERC. cbn [zr_strm zr_consumed zr_output zr_rc] in EZ, EAI, EAO, EBS, ERC.
    rewrite czc_len in EAI.
    pose proof (sv_inlen _ _ SVF) as I1. pose proof (sv_nin _ _ SVF) as I2. pose proof (sv_ain _ _ SVF) as I3.
    pose proof (sv_out _ _ SVF) as O1. pose proof (sv_aout _ _ SVF) as O2. pose proof (sv_tout _ _ SVF) as O3.
    pose proof (sv_tin _ _ SVF) as T1. pose proof (sv_outb _ _ SVF) as OB.
    assert (IL : arr_len (cs_input (cstrm_of_call czc)) = ai) by (cbn [cstrm_of_call cs_input]; rewrite arr_len_of_list; exact czc_len).
    rewrite IL in I1.
    assert (EO0 : cs_out_rev (cstrm_of_call czc) = [] /\ cs_avail_out (cstrm_of_call czc) = ao /\ cs_total_out (cstrm_of_call czc) = zs_total_out (dz_z x))
      by (unfold czc, zd_zcall; cbn; repeat split; reflexivity).
    destruct EO0 as (EO1 & EO2 & EO3). rewrite EO1, EO2 in O1. rewrite EO1, EO3 in O3. cbn [zlen length Z.of_nat] in O1, O3. rewrite Z.sub_0_r in O3.
    assert (LBS : zlength bs = Z.of_nat (length (cs_out_rev (ds_strm sF)))).
    { rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. unfold zlength. rewrite length_rev. reflexivity. }
    unfold zlen in O1, O3. cbn [length Z.of_nat] in O1. rewrite <- EBS, LBS in EAO.
    unfold fwT in FT.
    assert (TI : cs_total_in (ds_strm sF) = zs_total_in (dz_z x) + cs_next_in (ds_strm sF)).
    { apply (BoundCall.wrap64_sub_inj _ _ _ ltac:(rewrite FT; symmetry; apply wrap64_id; destruct ZOK as ((A0 & A1) & _); lia) T1).
      destruct ZOK as ((A0 & A1) & _). unfold zlength in HTIN, HDL. lia. }
    split; [exact DR'|]. split; [exact PATF|].
    split. { rewrite <- EZ. unfold zstrm_okP, zstrm_of_cs. cbn [zs_total_in zs_total_out zs_adler zs_data_type].
             split; [exact T1|]. split; [rewrite O3; apply wrap64_range|]. split; [exact (sv_adler _ _ SVF)| exact (sv_dt _ _ SVF)]. }
    split; [exact ERC|].
    split; [rewrite EBS; unfold cs_output; rewrite rev_append_rev, app_nil_r; reflexivity|].
    rewrite <- EZ. unfold zstrm_of_cs. cbn [zs_total_in zs_total_out zs_msg zs_data_type zs_adler].
    split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
    split; [exact TI|]. split; [lia|]. split; [lia|]. split; [exact EAI|]. split; [exact O3|]. split; [lia|]. split; [exact EAO|]. split; [exact LBS|].
    rewrite EBS. unfold cs_output. rewrite rev_append_rev, app_nil_r. apply Forall_rev. exact OB.
  Qed.
End PURE.

Definition dl_io (L : dlay) (ni no : Z) : dlay := U.Z_drep.mkDL (dl_S L) (dl_As L) (dl_Aw L) (dl_Ap L) (dl_Ah L) (dl_Ab L) ni no.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Lemma DST_io : forall m L s ni no, DST m L s -> DST m (dl_io L ni no) s.
Proof.
  intros m L s ni no [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay]. destruct L as [LS LAs LAw LAp LAh LAb LNI LNO]. unfold dl_io. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab].
  constructor; [exact HA| exact HB0| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| exact Hlens |].
  destruct Hlay. constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *; assumption.
Qed.
Lemma DST_io_back : forall m L s ni no, DST m (dl_io L ni no) s -> DST m L s.
Proof.
  intros m L s ni no [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay]. destruct L as [LS LAs LAw LAp LAh LAb LNI LNO]. unfold dl_io in *. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *.
  constructor; [exact HA| exact HB0| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| exact Hlens |].
  destruct Hlay. constructor; cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab] in *; assumption.
Qed.
Lemma DST_unstrm : forall m L s c, DST m L (set_strm s c) -> DST m L s.
Proof.
  intros m L s c [HA HB0 HC HD Hlt Hdt Hbt Hblc Hheap Hdep Hwin Hprev Hhead Hpend Hlens Hlay].
  constructor; [exact HA| exact HB0| exact HC| exact HD| exact Hlt| exact Hdt| exact Hbt| exact Hblc| exact Hheap| exact Hdep
               | exact Hwin| exact Hprev| exact Hhead| exact Hpend| | exact Hlay].
  destruct Hlens as [L1 L2 L3 L4 L5 L6 L7 L8 L9 L10 L11 L12 L13].
  constructor; [exact L1| exact L2| exact L3| exact L4| exact L5| exact L6| exact L7| exact L8| exact L9| exact L10| exact L11| exact L12| exact L13].
Qed.

Lemma munch_shrink : forall W W' (m m' : mem), munch W m m' -> (forall x : word, outside W' (bv_unsigned x) -> outside W (bv_unsigned x) \/ m' x = m x) -> munch W' m m'.
Proof. intros W W' m m' MU H x Hx. destruct (H x Hx) as [O|E]; [exact (MU x O)| exact E]. Qed.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].
Local Transparent the_zapi.

Section CLOSE.
  Hypothesis HFW : fill_window_stmt.
  Hypothesis HTFBLK : tr_flush_block_stmtE.
  Hypothesis HTFB : tr_flush_bits_stmt.

  Theorem deflate_proof : forall R : zreps, Zlib_iface.zr_d R = U.Z_zrd.zr_d -> deflate_stmt R.
  Proof.
    intros R RD. unfold deflate_stmt. intros until B.
    intros ZP ZR PB PF PD PD2 CO CL CP CP2 HAI HTIN HAO HFL SEPC SEPD CIMG SBC SBD SDC ROOM ZLS SIF STK CEIL GLO LOSP SP16 SPB B63 MI -> ->.
    rewrite RD in ZR. unfold deflate_post. rewrite RD.
    cbn [d_total_in d_total_out d_deflate the_zapi zinst] in *.
    destruct ZR as (L & sa & b & ELB & ES & DQ & DR & PT & DCL & ZOK). subst LBz.
    assert (HDL : Prelim.zlength d < 2 ^ 63) by (clear - PD PD2; lia).
    pose proof (zd_call_facts sa d ds ai ao flush DR PT ZOK HAI HTIN HDL HAO PF HFL) as FACTS.
    pose proof (czc_path sa d ds ai ao flush DR PT ZOK HAI HTIN HAO PF HFL) as PATH.
    pose proof (czc_len d ds ai ao ZOK HAI HTIN) as LAI.
    cbv zeta in FACTS.
    destruct (zd_deflate d ds ai ao flush) as [[[[x' ai'] ao'] bs] rc]. cbn [fst snd] in ROOM.
    remember (fst (deflate_core (cd0 sa d ds ai ao) flush)) as sF eqn:EsF.
    remember (snd (deflate_core (cd0 sa d ds ai ao) flush)) as rcF eqn:ErcF.
    destruct FACTS as (DR' & PT' & ZOK' & Erc & Ebs & Etin' & Etout' & Emsg' & Edt' & Ead' & TI & NI & AI & Eai' & TO & AOU & Eao' & LBS & BSB).
    set (tin := zs_total_in (dz_z ds)) in *. set (tout := zs_total_out (dz_z ds)) in *.
    pose proof ZOK as (Rti & Rto & _). fold tin in Rti. fold tout in Rto.
    unfold Prelim.zlength in *. unfold zlength in LAI, LBS.
    assert (LOUT : length (to_bytes out) = length out) by apply to_bytes_length.
    remember (dl_io L (D + tin) (C + tout)) as L' eqn:EL'.
    pose proof (st_lay _ _ _ _ (proj2 DQ)) as LAY.
    destruct b as [[[[psp pw] pp] ph] pb]. unfold zd_blocks in SBC, SBD. unfold zd_blocks.
    assert (INb : forall y, In y [(pb, dl_Ab L, 65536); (ph, dl_Ah L, 65536); (pp, dl_Ap L, 65536); (pw, dl_Aw L, 65536); (psp, dl_As L, 5968)] ->
                  (blk_addr y + blk_size y <= C \/ C + cl <= blk_addr y) /\ (blk_addr y + blk_size y <= D \/ D + Z.of_nat (length d) <= blk_addr y))
      by (intros y Hy; split; [exact (SBC y Hy)| exact (SBD y Hy)]).
    pose proof (INb _ ltac:(left; reflexivity)) as Yb. pose proof (INb _ ltac:(right; left; reflexivity)) as Yh.
    pose proof (INb _ ltac:(do 2 right; left; reflexivity)) as Yp. pose proof (INb _ ltac:(do 3 right; left; reflexivity)) as Yw.
    pose proof (INb _ ltac:(do 4 right; left; reflexivity)) as Ys. clear INb SBC SBD. cbn [blk_addr blk_size fst snd] in Yb, Yh, Yp, Yw, Ys.
    apply box in Yb. apply box in Yh. apply box in Yp. apply box in Yw. apply box in Ys. apply box in CIMG. apply box in SDC.
    unfold dlay_ceil in DCL. unfold strm_in_frame, ZS_SIZEOF in SIF. unfold Z_DEFLATE_STACK in LOSP. unfold Layout.GLOBALS_TOP in GLO.
    pose proof CO as CO'. rewrite <- (firstn_skipn (Z.to_nat tout) (to_bytes out)) in CO'. apply u8arr_app in CO'. destruct CO' as [OPRE OREST].
    rewrite length_firstn, Nat.min_l in OREST by (clear - LOUT CL ROOM LBS Rto; lia). replace (Z.of_nat (Z.to_nat tout)) with tout in OREST by (clear - Rto; lia).
    remember (skipn (Z.to_nat tout) (to_bytes out)) as rest0 eqn:Erest0.
    assert (LR0 : Z.of_nat (length rest0) = cl - tout) by (subst rest0; rewrite length_skipn; clear - LOUT CL ROOM LBS Rto; lia).
    assert (DREP0 : DREP m L' (cd0 sa d ds ai ao)).
    { split.
      - destruct (proj1 DQ) as (p3 & resv & ZQ). exists p1, p2, p3, resv.
        assert (ZS : rw_cells usegs m S (zs_pub (D + tin) ai tin (C + tout) ao tout p1 p2 ++ zs_priv_cells L (zs_msg (dz_z ds)) (zs_data_type (dz_z ds)) (zs_adler (dz_z ds)) p3 resv)).
        { apply (proj2 (Startup_glue.rw_cells_app usegs m S _ _)). split; [exact ZP|]. rewrite ES in ZQ.
          lazymatch goal with |- rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 by reflexivity end. exact ZQ. }
        subst L'. unfold dl_io, zs_call_cells, zs_priv_cells, cd0, czc, zd_zcall. cbn [dl_S dl_As dl_NI dl_NO ds_strm set_strm cstrm_of_call zc_input zc_avail_out zc_strm
          cs_next_in cs_avail_in cs_total_in cs_out_rev cs_avail_out cs_total_out cs_msg cs_data_type cs_adler length Z.of_nat app].
        rewrite ES. unfold zs_pub, zs_priv_cells in ZS. cbn [app] in ZS.
        unfold czc, zd_zcall in LAI. cbn [zc_input] in LAI. fold tin. fold tout. unfold zlength. rewrite LAI.
        close_cells ZS.
      - subst L'. apply DST_io. apply DST_set_strm; [intros H; exact H| exact (proj2 DQ)]. }
    assert (DIN0 : din m L' (zc_input (czc d ds ai ao))).
    { subst L'. unfold din, dl_io, czc, zd_zcall. cbn [dl_NI zc_input]. unfold zfirstn, zskipn, zb8. fold tin.
      rewrite <- firstn_map, <- skipn_map. change (map (Z_to_bv 8) d) with (to_bytes d).
      replace (D + tin) with (D + Z.of_nat (Z.to_nat tin)) by (clear - Rti; lia).
      pose proof PB as PB'. rewrite <- (firstn_skipn (Z.to_nat tin) (to_bytes d)) in PB'. apply bytes_at_app in PB'. destruct PB' as [_ PB'].
      rewrite length_firstn, Nat.min_l in PB' by (rewrite to_bytes_length; clear - Rti HTIN HAI; lia).
      rewrite <- (firstn_skipn (Z.to_nat ai) (skipn (Z.to_nat tin) (to_bytes d))) in PB'. apply bytes_at_app in PB'. exact (proj1 PB'). }
    assert (DOUT0 : dout m L' rest0 (ds_strm (cd0 sa d ds ai ao))).
    { subst L'. unfold dout, outv, dl_io, cd0, czc, zd_zcall. cbn [dl_NO ds_strm set_strm cstrm_of_call cs_out_rev rev zb8 map length skipn app]. exact OREST. }
    pose proof (relro_clean_of_zl _ ZLS) as RC.
    pose proof (bv_unsigned_in_range 64 sp) as RSP. unfold bv_modulus in RSP. cbn in RSP.
    assert (BEL : dlay_below L' lo (bv_unsigned sp)).
    { subst L'. unfold dlay_below, dl_io. cbn [dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab]. rewrite ES. clear - DCL CEIL GLO SIF. lia. }
    assert (IO : dio_sep L' (ZIface.zlength (zc_input (czc d ds ai ao))) (Z.of_nat (length rest0)) lo).
    { pose proof (czc_len d ds ai ao ZOK HAI HTIN) as LAI2. rewrite LAI2, LR0. subst L'. unfold dl_io.
      pose proof (unbox _ Yb) as Xb. pose proof (unbox _ Yh) as Xh. pose proof (unbox _ Yp) as Xp. pose proof (unbox _ Yw) as Xw. pose proof (unbox _ Ys) as Xs.
      pose proof (unbox _ CIMG) as XI. pose proof (unbox _ SDC) as XDC.
      constructor; cbn [dl_NI dl_NO dl_As dl_Aw dl_Ap dl_Ah dl_Ab]; unfold apart.
      - clear - PD Rti HAI HTIN SEPD. lia.
      - clear - CP Rto ROOM LBS SEPC. lia.
      - clear - XI Rto ROOM LBS. lia.
      - clear - XDC Rti Rto HAI HTIN ROOM LBS. lia.
      - clear - Xs Rti HAI HTIN. lia. - clear - Xw Rti HAI HTIN. lia. - clear - Xp Rti HAI HTIN. lia. - clear - Xh Rti HAI HTIN. lia. - clear - Xb Rti HAI HTIN. lia.
      - clear - Xs Rto ROOM LBS. lia. - clear - Xw Rto ROOM LBS. lia. - clear - Xp Rto ROOM LBS. lia. - clear - Xh Rto ROOM LBS. lia. - clear - Xb Rto ROOM LBS. lia. }
    assert (ROOM' : (length (cs_out_rev (ds_strm (fst (deflate_core (cd0 sa d ds ai ao) flush)))) <= length rest0)%nat).
    { rewrite <- EsF. clear - ROOM LBS LR0. lia. }
    eapply evt_mono.
    { eapply (deflate_in_spec (deflate_slow_spec HFW HTFBLK HTFB) HTFB L' (cd0 sa d ds ai ao) flush (zc_input (czc d ds ai ao)) rest0 lo);
        [ exact DREP0 | exact DIN0 | exact DOUT0 | exact MI | exact RC | exact STK
        | unfold Z_DEFLATE_IN_STACK, Z_SLOW_STACK; clear - LOSP; lia | exact SP16 | exact BEL | exact IO | exact HFL | exact PATH | exact ROOM'
        | subst L'; unfold dl_io; cbn [dl_S]; rewrite ES; reflexivity | reflexivity ]. }
    intros ms' POST. cbv beta.
    destruct POST as (u0 & u1 & u2 & c1 & c2 & c3 & c4 & c5 & c6 & c7 & u3 & u4 & u5 & u6 & m' & -> & MU & WM & MI' & STK' & DREP' & DIN' & DOUT').
    rewrite <- EsF, <- ErcF in *.
    destruct DREP' as [ZS' ST']. destruct ZS' as (q1 & q2 & q3 & qr & ZS').
    subst L'. unfold zs_call_cells, zs_priv_cells, dl_io in ZS'. cbn [dl_S dl_NI dl_NO dl_As app] in ZS'. rewrite ES in ZS'.
    lazymatch type of ZS' with rw_cells _ _ _ ?cs =>
      let a := eval cbv beta iota delta [firstn] in (firstn 8 cs) in let b' := eval cbv beta iota delta [skipn] in (skipn 8 cs) in
      change (rw_cells usegs m' S (a ++ b')) in ZS' end.
    apply Startup_glue.rw_cells_app in ZS'. destruct ZS' as [ZP' ZQ'].
    lazymatch type of ZQ' with rw_cells _ _ (_ + Z.of_nat ?n) _ => replace (Z.of_nat n) with 48 in ZQ' by reflexivity end.
    unfold dout, dl_io in DOUT'. cbn [dl_NO] in DOUT'.
    assert (TOX : cs_total_out (ds_strm sF) = tout + Z.of_nat (length (cs_out_rev (ds_strm sF)))).
    { rewrite TO. apply wrap64_id. clear - Rto ROOM LBS CP CP2. lia. }
    do 15 eexists. exists m', q1, q2.
    split; [reflexivity|].
    split.
    {
      pose proof (unbox _ CIMG) as XI.
      apply (munch_shrink _ _ _ _ MU). intros y OUT. cbn [map app blk_addr blk_size fst snd outside dl_io dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab dl_NO] in OUT |- *.
      rewrite ES. unfold ZS_SIZEOF in OUT. pose proof (bv_unsigned_in_range 64 y) as Ry. unfold bv_modulus in Ry. cbn in Ry.
      destruct (Z.le_gt_cases (C + tout + Z.of_nat (length bs)) (bv_unsigned y)) as [H1|H1]; [destruct (Z.lt_ge_cases (bv_unsigned y) (C + cl)) as [H2|H2]|].
      - right.
        set (i := Z.to_nat (bv_unsigned y - (C + tout))).
        assert (Ei : wa (C + tout + Z.of_nat i) = y) by (subst i; apply bv_eq; rewrite wa_unsigned by (clear - H1 H2 Ry LBS CP Rto; lia); clear - H1 H2 Ry LBS CP Rto; lia).
        destruct OREST as [(_ & _ & B1) _]. destruct DOUT' as [(_ & _ & B2) _].
        assert (Li : (i < length rest0)%nat) by (subst i; clear - H1 H2 LR0 LBS Rto; lia).
        pose proof (B1 i Li) as Q1. pose proof (B2 i ltac:(rewrite outv_length; [exact Li| exact ROOM'])) as Q2.
        rewrite (nth_error_outv_tail rest0 _ i ROOM') in Q2 by (subst i; clear - H1 LBS Rto CP; lia).
        rewrite Ei in Q1, Q2.
        assert (ROM : seg_rom usegs y = None) by (apply RMallocRep.ref_seg_rom_none; clear - XI H1 H2 Rto CP LBS; lia).
        unfold mrd in Q1, Q2. rewrite ROM in Q1, Q2. rewrite <- Q1 in Q2. destruct (m y), (m' y); congruence.
      - left. clear - OUT H1 H2 LR0 Rto LBS ROOM. lia.
      - left. clear - OUT H1 LR0 Rto LBS ROOM. lia. }
    split; [exact WM|]. split; [exact MI'|]. split; [exact STK'|].
    split; [rewrite Erc; unfold wint, MallocRep.wz; reflexivity|].
    split.
    { unfold zs_pub. rewrite Etin', Etout', Eai', Eao'. close_cells ZP'. }
    split.
    { rewrite <- ES. apply (zr_d_intro m' L sF (psp, pw, pp, ph, pb) x').
      - split; [| exact (DST_io_back _ _ _ _ _ ST')]. exists q3, qr. rewrite Emsg', Edt', Ead'. unfold zs_priv_cells. rewrite ES. exact ZQ'.
      - exact DR'.
      - exact PT'.
      - exact DCL.
      - exact ZOK'. }
    split.
    {
      assert (OPRE' : u8arr usegs m' C (firstn (Z.to_nat tout) (to_bytes out))).
      { eapply U.Z_dview.u8arr_agree; [exact OPRE|]. rewrite length_firstn, Nat.min_l by (clear - LOUT CL ROOM LBS Rto; lia).
        apply (agree_on_of_munch _ _ _ _ _ MU WM); [clear - CP; lia| clear - CP CP2 Rto CL LOUT ROOM LBS; lia|].
        cbn [disjoint_from dl_io dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab dl_NO]. rewrite ES.
        destruct (unbox _ Yb) as [Xb _]. destruct (unbox _ Yh) as [Xh _]. destruct (unbox _ Yp) as [Xp _]. destruct (unbox _ Yw) as [Xw _]. destruct (unbox _ Ys) as [Xs _].
        split; [clear - SEPC Rto CP ROOM LBS; lia|]. split; [clear - SEPC LOSP SIF Rto CP ROOM LBS; lia|].
        split; [clear - Xs Rto ROOM LBS CP; lia|]. split; [clear - Xw Rto ROOM LBS CP; lia|]. split; [clear - Xp Rto ROOM LBS CP; lia|].
        split; [clear - Xh Rto ROOM LBS CP; lia|]. split; [clear - Xb Rto ROOM LBS CP; lia|]. split; [clear - Rto CP; lia| exact I]. }
      assert (OUT : u8arr usegs m' C (firstn (Z.to_nat tout) (to_bytes out) ++ outv rest0 (ds_strm sF))).
      { apply (proj2 (u8arr_app m' C _ _)). split; [exact OPRE'|]. rewrite length_firstn, Nat.min_l by (clear - LOUT CL ROOM LBS Rto; lia).
        replace (Z.of_nat (Z.to_nat tout)) with tout by (clear - Rto; lia). exact DOUT'. }
      replace (to_bytes (zstore out tout bs)) with (firstn (Z.to_nat tout) (to_bytes out) ++ outv rest0 (ds_strm sF)); [exact OUT|].
      rewrite zstore_at by (clear - Rto CL ROOM LBS LOUT; lia).
      rewrite to_bytes_app, to_bytes_app, to_bytes_firstn, to_bytes_skipn, to_bytes_skipn. f_equal.
      unfold outv. subst rest0. rewrite Ebs. unfold zb8, to_bytes. rewrite length_rev. reflexivity. }
    eapply bytes_at_agree; [exact PB|]. rewrite to_bytes_length.
    apply (agree_on_of_munch _ _ _ _ _ MU WM); [clear - PD; lia| clear - PD PD2; lia|].
    cbn [disjoint_from dl_io dl_S dl_As dl_Aw dl_Ap dl_Ah dl_Ab dl_NO]. rewrite ES.
    destruct (unbox _ Yb) as [_ Xb]. destruct (unbox _ Yh) as [_ Xh]. destruct (unbox _ Yp) as [_ Xp]. destruct (unbox _ Yw) as [_ Xw]. destruct (unbox _ Ys) as [_ Xs].
    pose proof (unbox _ SDC) as XDC.
    split; [clear - SEPD PD; lia|]. split; [clear - SEPD LOSP SIF PD; lia|].
    split; [clear - Xs PD; lia|]. split; [clear - Xw PD; lia|]. split; [clear - Xp PD; lia|].
    split; [clear - Xh PD; lia|]. split; [clear - Xb PD; lia|]. split; [clear - XDC PD LR0 Rto ROOM LBS; lia| exact I].
  Qed.
End CLOSE.
End WithCeiling0.
