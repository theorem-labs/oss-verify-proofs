(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem ALib.Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require I_asan_memcpy.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib Defs DefsA DefsB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB MemFX RstageCtr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV GlueA CtrPre CtrFrame CtrNoDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require UnreggGeo UnreggPre.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import MemOps RangeC BlobC PayloadC MemsetFX RangePre MemsetPre MemsetPost RegRepl RstageSound RstagePost ZoneB BlobSound PayloadSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require ReadPost.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA PayloadC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.I_memcpy.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma payload_post_shape : forall st st1 r kd, payload_post st st1 r kd =
  let C := clobber st1 in
  SS r (rf_set (s_rf C) X10 (getr st X10)) (s_ff C) (s_resv C)
     (IMap.add kd (Region 0%uint63 (getr st X12) true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs C))
     (s_facts C) (s_ops C) (s_priv C) (s_next C).
Proof. intros st st1 r kd. unfold payload_post. cbv zeta. generalize (clobber st1). intros C. destruct C. reflexivity. Qed.

Lemma apayload_leaf_ok : PayloadSound.apayload_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold PayloadSound.apayload_leaf.
  intros st K E ms mo r hargs wnl st1 kd ks rd wlend wlens L RNG sta LBa aw offZ HS HPB HK PRE G10 NKK FD WLd WLs OT CBd LOd RWd CP FS CF AH MI
         BOT LO SPT POSn LEWd LOWD HID NEA0 EA0 EA2 SRC5 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (Dd := bv_unsigned (ev E kd)) in *. set (Ds := bv_unsigned (ev E ks)) in *.
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlend)) in *.
  set (m := ms_mem ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.E' E st Fv Gv).
  destruct (HeapCtr.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.reg_of_X1, (GlueA.getr_RA asegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.den_wlit. }
  assert (EMS' : ms' = CtrFrame.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  destruct (CtrFrame.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
  assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
  assert (Vn : sv_vars_below (s_next st) nsv = true) by exact (PlanS.rf_allb_get _ _ _ RFB X12).
  assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.getr_RA asegs OPS E st ms mo HS X10). }

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' Dd nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) (or_introl HID) ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA. fold m in HSA.
  set (mj := mjoinR Dd (Dd + nZ) m m') in *.
  idtac "BP-A".

  pose proof CF as CF0.
  destruct CF0 as (LB & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl kd wlend CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLd)) as (Kd0 & _ & _ & INWd).
  assert (Kd0' : PrimInt63.eqb kd 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kd0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct (CallA.sp_region_inv st ks0 offs rss SPR) as (_ & Hrs & _).
  assert (NKS : kd <> ks0).
  { intros Q. rewrite Q, Hrs in FD. injection FD as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LOd, KZ0 in FLOOR.
    rewrite <- Q in FLOOR. fold Dd in FLOOR. lia. }
  assert (FD1 : IMap.find kd (s_regs st1) = Some rd).
  { rewrite (CtrFrame.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp).
    rewrite IMap.find_add_other; [exact FD| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }
  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kd wlend CtrLib.K_BLOCK 0 wlenZ CF WLd KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  fold Dd in BA1, BA2.
  assert (UBW : forall a, Dd <= a < Dd + wlenZ -> uband a).
  { intros a Ha. exact (Op.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
  pose proof (bv_unsigned_in_range 64 (ev E kd)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Dd in RDb.
  assert (A64 : forall a, Dd <= a < Dd + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x62f000 <= a).
  { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }
  idtac "BP-B0".

  assert (OWIN : forall k len kdw, CtrA.win_lookup wnl k = Some (len, kdw) -> k <> kd ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ (Dd <= x < Dd + wlenZ)).
  { intros k len kdw WLk NKd x Hx INX. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WLk) as Ik.
    pose proof (proj1 (forallb_forall _ _) OT _ Ik) as Q. cbv beta iota in Q.
    replace (PrimInt63.eqb k kd) with false in Q by (symmetry; apply Uint63.eqb_false_spec; exact NKd). cbn [orb] in Q.
    pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH0.
    apply orb_prop in Q as [Q|QFT]. 2:{

      apply weqb_eq in QFT. subst kdw.
      destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len RangeC.K_FTWIN NW Ik) as (_ & _ & _ & INW).
      destruct TI as (_ & _ & _ & _ & T5 & _). destruct (T5 _ INW eq_refl) as (b & VFb & EIV). unfold w_iv, fsh_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
      pose proof ARW as [HWW _].
      destruct (LB_fsh_facts AI ACCT UNIV AI_fake W _ LB (ms_mem ms) mo b HWW VFb) as (T1 & T2' & _).
      pose proof (UBW x INX) as U. unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
    apply orb_prop in Q as [Q|QFR]. 2:{

      apply weqb_eq in QFR. subst kdw.
      destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len RangeC.K_FRAME NW Ik) as (_ & _ & _ & INW).
      apply (win_noframe_k Cw Cw_sub_ghost W _ _ _ _ _ (Win Dd wlenZ (w2Z CtrLib.K_BLOCK)) (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z RangeC.K_FRAME)) TI HC INWd INW
               eq_refl ltac:(vm_compute; split; [discriminate| reflexivity]) x);
        unfold in_iv, w_iv; cbn [w_lo w_len fst snd]; lia. }
    apply orb_prop in Q as [Q|Q].
    -
      apply Uint63.eqb_correct in Q. subst k. rewrite WLs in WLk. injection WLk as <- <-.
      assert (INd : In (Dd, wlenZ) LB).
      { pose proof (proj1 (Forall_forall _ _) WF _ INWd) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
          [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
      destruct (HeapCtrB.nonstack_windows_In E nn rest wnl ks wlens CtrLib.K_BLOCK NW (HeapCtrB.win_lookup_In _ _ _ _ WLs)) as (_ & _ & _ & INWs).
      assert (INs : In (Ds, bv_unsigned (den E wlens)) LB).
      { pose proof (proj1 (Forall_forall _ _) WF _ INWs) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
          [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
      assert (NEA : Ds <> Dd) by exact NEA0.
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake _ LB _ _ (Ds, bv_unsigned (den E wlens)) (Dd, wlenZ) x AWH0 INs INd); [cbn [fst]; exact NEA| |];
        unfold in_iv; cbn [fst snd]; fold Ds; lia.
    -
      apply weqb_eq in Q. subst kdw.
      destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
      destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
      pose proof ARW as [HWW _].
      destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
      pose proof (UBW x INX) as U. unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  idtac "BP-B1a".

  set (rd' := Region 0%uint63 nsv true (BGBlob 5%uint63 0%uint63) IMap.empty).
  destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv kd rd FD) as (EKd & _ & _ & _). fold E' in EKd.
  assert (EHI : hiZ E' rd' = nZ).
  { unfold hiZ, rd'. cbn [rg_hi]. unfold E'. rewrite (CtrFrame.den_E' E st Fv Gv _ Vn). reflexivity. }
  assert (EL : loZ rd' = 0) by reflexivity.
  assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (Dd <= a < Dd + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
  { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.wa_u a Ha). unfold in_rng. replace ((Dd <=? a) && (a <? Dd + nZ)) with false by lia. reflexivity. }
  assert (COPIED : forall o, 0 <= o < nZ -> rb asegs m' (Dd + o) = Some (nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0))).
  { intros o Ho. rewrite <- (SRC5 o Ho). destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY). rewrite pay_src_len in BY.
    rewrite (GlueA.rb_mrdA asegs). replace (Dd + o) with (Dd + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
    apply nth_error_nth'. rewrite pay_src_len. lia. }
  assert (MAPPED : forall a, Dd <= a < Dd + nZ -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha. pose proof (COPIED (a - Dd) ltac:(lia)) as C. replace (Dd + (a - Dd)) with a in C by lia.
    rewrite (raw_of_view m' a _ ltac:(pose proof (A64 a ltac:(lia)); lia) C). discriminate. }
  assert (RO' : region_ok asegs (s_priv st) E' m' kd rd').
  { constructor; rewrite ?EHI, ?EL, ?EKd; fold Dd.
    - cbn. exact I.
    - intros _. unfold two64. lia.
    - intros _ a Ha. pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6].
      split; [| split].
      + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      + intros _. apply (GlueA.wb_wviewA asegs). rewrite (AImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.wa_u a AR). lia.
      + exact (UnreggPre.no_seg_above a A6).
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kd0'). unfold bg_byte. cbn [rd' rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      change (eb E' 5%uint63) with (eb E 5%uint63). apply COPIED. lia. }
  idtac "BP-B1b".
  assert (REGT : forall k2 r2, IMap.find k2 (s_regs st1) = Some r2 ->
            exists r2', IMap.find k2 (s_regs st) = Some r2' /\ loZ r2 = loZ r2' /\ hiZ E' r2 = hiZ E r2' /\ ev E' k2 = ev E k2).
  { intros k2 r2 H. rewrite (CtrFrame.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp) in H. destruct (Uint63.eqb ks0 k2) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k2. rewrite IMap.find_add_same in H by exact (so_bst _ _ _ _ _ _ HS). injection H as <-.
      destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv ks0 rss Hrs) as (EK & EH & _). exists rss. split; [exact Hrs|]. split; [reflexivity|]. split; [exact EH| exact EK].
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact (so_bst _ _ _ _ _ _ HS) || exact Q).
      destruct (CtrFrame.reg_E' OPS E st ms mo HS FOK Fv Gv k2 r2 H) as (EK & EH & _). exists r2. split; [exact H|]. split; [reflexivity|]. split; [exact EH| exact EK]. }
  assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply (CtrFrame.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
  assert (HS1 : st_ok asegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom asegs)) mo').
  { apply (st_ok_based_replace_g asegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom asegs) mo' kd rd rd' HSA FD1 Kd0').
    - intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
      assert (INB : Dd <= a < Dd + wlenZ).
      { destruct NC as [RGa|CH]; [rewrite EHI, EL, EKd in RGa; fold Dd in RGa; lia|].
        destruct (Z_lt_le_dec a Dd) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
        destruct (Z_lt_le_dec a (Dd + nZ)) as [L2|G2]; [lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
      pose proof (UBW a INB) as UB. split; [| split].
      + intros k2 r2 H2 NK2 K20 RG2. destruct (REGT k2 r2 H2) as (r2' & F2 & L2 & H2' & EK2). rewrite L2, H2', EK2 in RG2.
        exact (zone_regions_g AI ACCT UNIV Cw OPS E st ms mo HS r hargs wnl L RNG sta LBa aw CF kd wlend OWIN a INB UB k2 r2' F2 NK2 K20 RG2).
      + exact (UnreggPre.no_seg_above a (proj2 (A64 a INB))).
      + intros o Ho FP. rewrite (ARGT o Ho) in FP.
        exact (zone_ops AI IMGX ACCT UNIV Cw OPS OPS_fp1 OPS_fp_other E st ms mo r hargs wnl L RNG sta LBa aw CF kd wlend WLd a ltac:(unfold two64; lia) INB UB o Ho FP).
    - intros x H. unfold mj, mjoinR in H. destruct (in_rng Dd (Dd + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
      unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. lia.
    - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
    - exact RO'.
    - intros a RGa. rewrite EHI, EL, EKd in RGa. fold Dd in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
      + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.find_op_In _ _ _ Hf).
      + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
        split; [exact (CtrFrame.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
        unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWd| reflexivity]|].
        unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Dd wlenZ. lia. }
  idtac "BP-B1".
  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold CtrFrame.ms'.
  rewrite (payload_post_shape st st1 r kd). cbv zeta. rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1.
  exact HS1.
Qed.
End Leaf.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB ABase.TwinB AMalloc_iface.TwinB.
Import AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Defs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsB.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import MemOps.TwinB RangeC.TwinB BlobC.TwinB PayloadC.TwinB MemsetFX.TwinB RangePre.TwinB MemsetPre.TwinB MemsetPost.TwinB RegRepl.TwinB RstageSound.TwinB RstagePost.TwinB ZoneB.TwinB BlobSound.TwinB PayloadSound.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP StepB CtrFX ActrA PayloadC.TwinB.PayloadC.
Module IMC := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.I_asan_memcpy.TwinB.I_memcpy.

Section Leaf.
Context {rc : runConstT}.
Variable AI : AMallocIface2.
Variable IMGX : list iv.
Hypothesis IMGX_aci : imgx_ok AI IMGX.
Variable ACCT : word -> alayout -> footprint -> astate -> list ablock -> Model -> Prop.
Variable UNIV : list (list Z).
Variable Cw : client_world.
Variable OPS : optable.
Hypothesis AI_fake : AI_fake_law AI.
Hypothesis OPS_holds1 : forall args m mo, op_holds OPS HEAP_ID args m mo <-> heap_holdsX AI ACCT UNIV Cw args m mo.
Hypothesis OPS_fp1 : forall args, op_fp OPS HEAP_ID args = heap_fp IMGX args.
Hypothesis OPS_cov1 : forall args z, op_cov1 OPS HEAP_ID args z <-> Op.TwinB.cov1 HEAP_ID args z.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.
Hypothesis Cw_sub_ghost : forall md ca LB ws m w g a, cw_holds Cw md ca LB ws m -> In w ws -> In g ws ->
  K_SUB <= w_kind w < K_GHOST -> K_GHOST <= w_kind g -> in_iv (w_iv w) a -> in_iv (w_iv g) a -> False.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.

Lemma payload_post_shape : forall st st1 r kd, payload_post st st1 r kd =
  let C := clobber st1 in
  SS r (rf_set (s_rf C) X10 (getr st X10)) (s_ff C) (s_resv C)
     (IMap.add kd (Region 0%uint63 (getr st X12) true (BGBlob 5%uint63 0%uint63) IMap.empty) (s_regs C))
     (s_facts C) (s_ops C) (s_priv C) (s_next C).
Proof. intros st st1 r kd. unfold payload_post. cbv zeta. generalize (clobber st1). intros C. destruct C. reflexivity. Qed.

Lemma apayload_leaf_ok : PayloadSound.TwinB.apayload_leaf AI ACCT UNIV Cw OPS OTHER MP PB.
Proof.
  unfold PayloadSound.TwinB.apayload_leaf.
  intros st K E ms mo r hargs wnl st1 kd ks rd wlend wlens L RNG sta LBa aw offZ HS HPB HK PRE G10 NKK FD WLd WLs OT CBd LOd RWd CP FS CF AH MI
         BOT LO SPT POSn LEWd LOWD HID NEA0 EA0 EA2 SRC5 ms' mo' HQ HMP' HMI' OTH ACP.
  set (R := ms_regs ms) in *. set (Dd := bv_unsigned (ev E kd)) in *. set (Ds := bv_unsigned (ev E ks)) in *.
  set (nsv := getr st X12) in *. set (nZ := bv_unsigned (den E nsv)) in *. set (wlenZ := bv_unsigned (den E wlend)) in *.
  set (m := ms_mem ms) in *.
  destruct HQ as (t0 & t1 & t2 & a1' & a2' & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & m' & EMS & MU & WM & MINV' & STK' & DSTP & SRCP).
  rewrite EA0, EA2 in MU, DSTP.
  pose proof atop_range as ATR. pose proof (so_facts _ _ _ _ _ _ HS) as Hfs.
  match type of EMS with ms' = MS ?RR _ _ _ _ _ _ => set (R' := RR) in * end.
  set (Fv := CtrFree.TwinB.cfvF R'). set (Gv := fun (_ _ : Z) => Z_to_bv 8 0). set (E' := CtrFrame.TwinB.E' E st Fv Gv).
  destruct (HeapCtr.TwinB.call_pre_inv st r CP) as (FOK & ra0 & Hra0 & WT0 & LT0 & ER).
  assert (RAEQ : AP.getr R 1%bv = Z_to_bv 64 (to_Z r)).
  { unfold R. rewrite <- HeapCtr.TwinB.reg_of_X1, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X1), Hra0, ER.
    assert (ERA : ra0 = wlit (wl ra0)) by (destruct ra0 as [t l]; cbn in WT0 |- *; subst t; reflexivity). rewrite ERA at 1. apply HeapCtr.TwinB.den_wlit. }
  assert (EMS' : ms' = CtrFrame.TwinB.ms' ms r R' m').
  { rewrite EMS. unfold CtrFrame.TwinB.ms'. f_equal. rewrite RAEQ. apply ret_pc_even.
    - pose proof (int_range r) as RR. rewrite two63_eq in RR. lia.
    - pose proof (HeapCtr.TwinB.call_pre_even st r CP) as EV.
      pose proof (land_mk r 1%uint63 ltac:(change (to_Z 1%uint63) with 1; lia)) as LM.
      change (PrimInt63.sub (PrimInt63.lsl 1 1) 1)%uint63 with 1%uint63 in LM. rewrite EV in LM. change (to_Z 0%uint63) with 0 in LM.
      change (2 ^ to_Z 1%uint63) with 2 in LM. lia. }
  destruct (clobber_fields st1) as (_ & FF & RV & RG & FS0 & OP & PV & NXc).
  destruct (CtrFrame.TwinB.st1_fields st st1 FS) as (_ & _ & FF1 & RV1 & FS1 & OP1 & PV1 & NX1).
  destruct (CtrFrame.TwinB.SVB_parts st FOK) as (RFB & _ & _ & _ & _ & OPB).
  assert (VB10 : sv_vars_below (s_next st) (getr st X10) = true) by exact (PlanS.rf_allb_get _ _ _ RFB X10).
  assert (Vn : sv_vars_below (s_next st) nsv = true) by exact (PlanS.rf_allb_get _ _ _ RFB X12).
  assert (DVP : den E' (getr st X10) = AP.getr R' 10%bv).
  { unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ VB10). symmetry. exact (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X10). }

  pose proof (phaseA_ms AI IMGX IMGX_aci ACCT UNIV Cw OPS AI_fake OPS_holds1 OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
                st E ms mo r hargs wnl st1 L RNG sta LBa aw m' R' mo' Dd nZ 2240 (getr st X10) (s_next (clobber st1)) HS CP FS CF AH BOT LO SPT
                ltac:(unfold AIMG_HI in *; lia) (or_introl HID) ltac:(lia) MU WM MI MINV' STK'
                ltac:(intros rg Hrg; unfold CtrFrame.TwinB.kept_regsA in Hrg; cbn [In] in Hrg; repeat (destruct Hrg as [<-|Hrg]; [reflexivity|]); destruct Hrg)
                DVP OTH HMI' ACP) as HSA.
  fold Fv Gv E' in HSA. fold m in HSA.
  set (mj := mjoinR Dd (Dd + nZ) m m') in *.
  idtac "BP-A".

  pose proof CF as CF0.
  destruct CF0 as (LB & ks0 & offs & rss & ksp & nn & md & A & nw & rest & SPR & Hksp & SPE & K16 & LOSP & FLOOR & Hf & Hc & Eh & Tnw & Nn & Ln & N255
                   & NW & AN & AJ & TS & WF & HC & AWden & (W & WOF & ARW & TI)).
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl kd wlend CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLd)) as (Kd0 & _ & _ & INWd).
  assert (Kd0' : PrimInt63.eqb kd 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kd0).
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  destruct (CallA.TwinB.sp_region_inv st ks0 offs rss SPR) as (_ & Hrs & _).
  assert (NKS : kd <> ks0).
  { intros Q. rewrite Q, Hrs in FD. injection FD as Q2. rewrite Q2 in FLOOR. unfold loZ in FLOOR. rewrite LOd, KZ0 in FLOOR.
    rewrite <- Q in FLOOR. fold Dd in FLOOR. lia. }
  assert (FD1 : IMap.find kd (s_regs st1) = Some rd).
  { rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp).
    rewrite IMap.find_add_other; [exact FD| exact (so_bst _ _ _ _ _ _ HS)| intros Q; apply NKS; symmetry; exact Q]. }
  assert (KT : W64.weqb CtrLib.K_BLOCK ActrA.K_TWIN = false) by reflexivity.
  destruct (window_block_k AI ACCT UNIV Cw AI_fake Cw_sub_ghost E st ms mo r hargs wnl L RNG sta LBa aw kd wlend CtrLib.K_BLOCK 0 wlenZ CF WLd KT
              ltac:(vm_compute; congruence) ltac:(vm_compute; congruence) ltac:(vm_compute; split; [discriminate| reflexivity]) ltac:(lia) ltac:(lia) ltac:(unfold wlenZ; lia)) as (p & Ab & nb & HINB & BA1 & BA2).
  fold Dd in BA1, BA2.
  assert (UBW : forall a, Dd <= a < Dd + wlenZ -> uband a).
  { intros a Ha. exact (Op.TwinB.blk_band AI AI_fake L RNG sta LBa m (HB p Ab nb) a AH HINB ltac:(cbn [ab_addr ab_size]; lia)). }
  pose proof (bv_unsigned_in_range 64 (ev E kd)) as RDb. change (bv_modulus 64) with (2 ^ 64) in RDb. fold Dd in RDb.
  assert (A64 : forall a, Dd <= a < Dd + wlenZ -> 0 <= a < 2 ^ 64 /\ 0x631000 <= a).
  { intros a Ha. pose proof (UBW a Ha) as U. unfold uband, AIMG_HI, KLS in U. lia. }
  idtac "BP-B0".

  assert (OWIN : forall k len kdw, CtrA.win_lookup wnl k = Some (len, kdw) -> k <> kd ->
            forall x, bv_unsigned (ev E k) <= x < bv_unsigned (ev E k) + bv_unsigned (den E len) -> ~ (Dd <= x < Dd + wlenZ)).
  { intros k len kdw WLk NKd x Hx INX. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLk) as Ik.
    pose proof (proj1 (forallb_forall _ _) OT _ Ik) as Q. cbv beta iota in Q.
    replace (PrimInt63.eqb k kd) with false in Q by (symmetry; apply Uint63.eqb_false_spec; exact NKd). cbn [orb] in Q.
    pose proof (aw_real_holds AI ACCT UNIV _ _ _ _ _ ARW) as AWH0.
    apply orb_prop in Q as [Q|QFT]. 2:{

      apply weqb_eq in QFT. subst kdw.
      destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len RangeC.TwinB.RangeC.K_FTWIN NW Ik) as (_ & _ & _ & INW).
      destruct TI as (_ & _ & _ & _ & T5 & _). destruct (T5 _ INW eq_refl) as (b & VFb & EIV). unfold w_iv, fsh_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
      pose proof ARW as [HWW _].
      destruct (LB_fsh_facts AI ACCT UNIV AI_fake W _ LB (ms_mem ms) mo b HWW VFb) as (T1 & T2' & _).
      pose proof (UBW x INX) as U. unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
    apply orb_prop in Q as [Q|QFR]. 2:{

      apply weqb_eq in QFR. subst kdw.
      destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len RangeC.TwinB.RangeC.K_FRAME NW Ik) as (_ & _ & _ & INW).
      apply (win_noframe_k Cw Cw_sub_ghost W _ _ _ _ _ (Win Dd wlenZ (w2Z CtrLib.K_BLOCK)) (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z RangeC.TwinB.RangeC.K_FRAME)) TI HC INWd INW
               eq_refl ltac:(vm_compute; split; [discriminate| reflexivity]) x);
        unfold in_iv, w_iv; cbn [w_lo w_len fst snd]; lia. }
    apply orb_prop in Q as [Q|Q].
    -
      apply Uint63.eqb_correct in Q. subst k. rewrite WLs in WLk. injection WLk as <- <-.
      assert (INd : In (Dd, wlenZ) LB).
      { pose proof (proj1 (Forall_forall _ _) WF _ INWd) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
          [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
      destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl ks wlens CtrLib.K_BLOCK NW (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLs)) as (_ & _ & _ & INWs).
      assert (INs : In (Ds, bv_unsigned (den E wlens)) LB).
      { pose proof (proj1 (Forall_forall _ _) WF _ INWs) as (_ & _ & _ & [[KS0 _]|[[KB B]|[KS2 _]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *;
          [exfalso; vm_compute in KS0; discriminate KS0| exact B| exfalso; change (w2Z CtrLib.K_BLOCK) with 1 in KS2; unfold K_SUB in KS2; lia]. }
      assert (NEA : Ds <> Dd) by exact NEA0.
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake _ LB _ _ (Ds, bv_unsigned (den E wlens)) (Dd, wlenZ) x AWH0 INs INd); [cbn [fst]; exact NEA| |];
        unfold in_iv; cbn [fst snd]; fold Ds; lia.
    -
      apply weqb_eq in Q. subst kdw.
      destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len K_TWIN NW Ik) as (_ & _ & _ & INW).
      destruct TI as (_ & T2 & _). destruct (T2 _ INW eq_refl) as (b & HbT & EIV). unfold w_iv, twin_iv in EIV. cbn [w_lo w_len] in EIV. injection EIV as E1 E2.
      pose proof ARW as [HWW _].
      destruct (LB_twin_facts AI ACCT UNIV W _ LB (ms_mem ms) mo b HWW HbT) as (T1 & T2' & _).
      pose proof (UBW x INX) as U. unfold uband, AIMG_HI, KLS in U. rewrite E1, E2 in Hx. lia. }
  idtac "BP-B1a".

  set (rd' := Region 0%uint63 nsv true (BGBlob 5%uint63 0%uint63) IMap.empty).
  destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv kd rd FD) as (EKd & _ & _ & _). fold E' in EKd.
  assert (EHI : hiZ E' rd' = nZ).
  { unfold hiZ, rd'. cbn [rg_hi]. unfold E'. rewrite (CtrFrame.TwinB.den_E' E st Fv Gv _ Vn). reflexivity. }
  assert (EL : loZ rd' = 0) by reflexivity.
  assert (OUTSIDE : forall a, 0 <= a < 2 ^ 64 -> ~ (Dd <= a < Dd + nZ) -> mj (AM.wa a) = m' (AM.wa a)).
  { intros a Ha N. unfold mj, mjoinR. rewrite (ReadPost.TwinB.wa_u a Ha). unfold in_rng. replace ((Dd <=? a) && (a <? Dd + nZ)) with false by lia. reflexivity. }
  assert (COPIED : forall o, 0 <= o < nZ -> rb bsegs m' (Dd + o) = Some (nth (Z.to_nat o) (eb E 5%uint63) (Z_to_bv 8 0))).
  { intros o Ho. rewrite <- (SRC5 o Ho). destruct DSTP as [[_ BY] _]. cbn [cells_bytes cbytes] in BY. rewrite app_nil_r in BY. destruct BY as (_ & _ & BY). rewrite pay_src_len in BY.
    rewrite (GlueA.TwinB.rb_mrdA bsegs). replace (Dd + o) with (Dd + Z.of_nat (Z.to_nat o)) by lia. rewrite BY by lia.
    apply nth_error_nth'. rewrite pay_src_len. lia. }
  assert (MAPPED : forall a, Dd <= a < Dd + nZ -> m' (Z_to_bv 64 a) <> None).
  { intros a Ha. pose proof (COPIED (a - Dd) ltac:(lia)) as C. replace (Dd + (a - Dd)) with a in C by lia.
    rewrite (raw_of_view m' a _ ltac:(pose proof (A64 a ltac:(lia)); lia) C). discriminate. }
  assert (RO' : region_ok bsegs (s_priv st) E' m' kd rd').
  { constructor; rewrite ?EHI, ?EL, ?EKd; fold Dd.
    - cbn. exact I.
    - intros _. unfold two64. lia.
    - intros _ a Ha. pose proof (MAPPED a ltac:(lia)) as MP1. destruct (A64 a ltac:(lia)) as [AR A6].
      split; [| split].
      + unfold rb. destruct (m' (Z_to_bv 64 a)); [discriminate| exfalso; exact (MP1 eq_refl)].
      + intros _. apply (GlueA.TwinB.wb_wviewA bsegs). rewrite (BImg.ref_wview_overlay m' (AM.wa a)); [exact MP1|]. right. rewrite (ReadPost.TwinB.wa_u a AR). lia.
      + exact (UnreggPre.TwinB.no_seg_above a A6).
    - intros g gr Hg. cbn in Hg. discriminate Hg.
    - intros g gr c ii Hg. cbn in Hg. discriminate Hg.
    - intros o H1 _ _. specialize (H1 Kd0'). unfold bg_byte. cbn [rd' rg_bg]. change (to_Z 0%uint63) with 0. rewrite Z.sub_0_r.
      change (eb E' 5%uint63) with (eb E 5%uint63). apply COPIED. lia. }
  idtac "BP-B1b".
  assert (REGT : forall k2 r2, IMap.find k2 (s_regs st1) = Some r2 ->
            exists r2', IMap.find k2 (s_regs st) = Some r2' /\ loZ r2 = loZ r2' /\ hiZ E' r2 = hiZ E r2' /\ ev E' k2 = ev E k2).
  { intros k2 r2 H. rewrite (CtrFrame.TwinB.st1_regs st st1 FS ks0 offs rss ksp SPR Hksp) in H. destruct (Uint63.eqb ks0 k2) eqn:Q.
    - apply Uint63.eqb_correct in Q. subst k2. rewrite IMap.find_add_same in H by exact (so_bst _ _ _ _ _ _ HS). injection H as <-.
      destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv ks0 rss Hrs) as (EK & EH & _). exists rss. split; [exact Hrs|]. split; [reflexivity|]. split; [exact EH| exact EK].
    - apply Uint63.eqb_false_spec in Q. rewrite IMap.find_add_other in H by (exact (so_bst _ _ _ _ _ _ HS) || exact Q).
      destruct (CtrFrame.TwinB.reg_E' OPS E st ms mo HS FOK Fv Gv k2 r2 H) as (EK & EH & _). exists r2. split; [exact H|]. split; [reflexivity|]. split; [exact EH| exact EK]. }
  assert (ARGT : forall o, In o (s_ops st) -> map (den E') (op_args o) = map (den E) (op_args o)).
  { intros o Ho. apply (CtrFrame.TwinB.map_den_E' E st Fv Gv). exact (proj1 (forallb_forall _ _) OPB o Ho). }
  assert (HS1 : st_ok bsegs OPS E'
            (SS r (rf_set (s_rf (clobber st1)) X10 (getr st X10)) (s_ff st) (s_resv st) (IMap.add kd rd' (s_regs st1)) (s_facts st) (s_ops st) (s_priv st) (s_next (clobber st1)))
            (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None m' (seg_rom bsegs)) mo').
  { apply (st_ok_based_replace_g bsegs OPS E' _ R' (ms_fregs ms) (Z_to_bv 64 (to_Z r)) (ms_fcsr ms) None mj m' (seg_rom bsegs) mo' kd rd rd' HSA FD1 Kd0').
    - intros a Ha NC. unfold two64 in Ha. cbn [s_regs s_ops] in *.
      assert (INB : Dd <= a < Dd + wlenZ).
      { destruct NC as [RGa|CH]; [rewrite EHI, EL, EKd in RGa; fold Dd in RGa; lia|].
        destruct (Z_lt_le_dec a Dd) as [L1|G1]; [exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia|].
        destruct (Z_lt_le_dec a (Dd + nZ)) as [L2|G2]; [lia| exfalso; apply CH; symmetry; apply (OUTSIDE a ltac:(lia)); lia]. }
      pose proof (UBW a INB) as UB. split; [| split].
      + intros k2 r2 H2 NK2 K20 RG2. destruct (REGT k2 r2 H2) as (r2' & F2 & L2 & H2' & EK2). rewrite L2, H2', EK2 in RG2.
        exact (zone_regions_g AI ACCT UNIV Cw OPS E st ms mo HS r hargs wnl L RNG sta LBa aw CF kd wlend OWIN a INB UB k2 r2' F2 NK2 K20 RG2).
      + exact (UnreggPre.TwinB.no_seg_above a (proj2 (A64 a INB))).
      + intros o Ho FP. rewrite (ARGT o Ho) in FP.
        exact (zone_ops AI IMGX ACCT UNIV Cw OPS OPS_fp1 OPS_fp_other E st ms mo r hargs wnl L RNG sta LBa aw CF kd wlend WLd a ltac:(unfold two64; lia) INB UB o Ho FP).
    - intros x H. unfold mj, mjoinR in H. destruct (in_rng Dd (Dd + nZ) (bv_unsigned x)) eqn:IS; [| exact H].
      unfold in_rng in IS. rewrite <- (Z_to_bv_bv_unsigned x). apply MAPPED. lia.
    - intros x b Hx seg Hs. pose proof (MINV' x b Hx) as RO. unfold AM.ro_addr in RO. rewrite Hs in RO. apply negb_false_iff in RO. exact RO.
    - exact RO'.
    - intros a RGa. rewrite EHI, EL, EKd in RGa. fold Dd in RGa. right. apply Exists_exists. exists (HEAP_ID, map (den E') hargs). split.
      + unfold insts. apply in_map_iff. exists (OpI HEAP_ID hargs). split; [reflexivity|]. cbn [s_ops]. exact (UnreggPre.TwinB.find_op_In _ _ _ Hf).
      + cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _.
        split; [exact (CtrFrame.TwinB.DEC' E st FOK Fv Gv nn rest hargs md A nw Hf Eh Tnw Nn Ln)| left].
        unfold in_ws, heap_ws. apply in_ivs_In. eexists. split; [apply in_map; apply filter_In; split; [exact INWd| reflexivity]|].
        unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. fold Dd wlenZ. lia. }
  idtac "BP-B1".
  apply (HK _ (or_introl eq_refl) E' ms' mo' (CtrFrame.TwinB.EXT E st Fv Gv) HMP').
  rewrite EMS'. unfold CtrFrame.TwinB.ms'.
  rewrite (payload_post_shape st st1 r kd). cbv zeta. rewrite FF, RV, RG, FS0, OP, PV, FF1, RV1, FS1, OP1, PV1.
  exact HS1.
Qed.
End Leaf.
End TwinB.
