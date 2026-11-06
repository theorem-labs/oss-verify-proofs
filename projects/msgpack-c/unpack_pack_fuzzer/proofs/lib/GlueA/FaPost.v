(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From Stdlib Require Import Permutation.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto ABase AMalloc_iface.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CtrPre GlueA FrameV CtrDelta CtrFree.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.GlueA Require Import ActrB FfShape FaC FaShape.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma KF7 : w2Z ActrB.K_FRAME = K_FRAMEz. Proof. reflexivity. Qed.
Lemma KFT8 : w2Z ActrB.K_FTWIN = K_FTWINz. Proof. reflexivity. Qed.

Section Fa.
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

Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
Hypothesis Cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> ZC_BASE + zc' < ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win zc) \/ w = zc_win zc') -> cw_holds Cw md ca LB ws' m.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Section RELEASED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis TS : twins_scan (s_facts st) (s_regs st) wnl wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Variables (kf sh : int).

Variables (rf rsh : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis Frs : IMap.find sh (s_regs st) = Some rsh.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, ActrB.K_FRAME).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, ActrB.K_FTWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis LO0s : rg_lo rsh = 0%uint63.
Hypothesis FULLs : hiZ E rsh = bv_unsigned (den E lent).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len) /\ 0 < hiZ E r0
        /\ rg_w r0 = true /\ (kd = ActrB.K_FRAME \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. intros a Ha; exact Ha.
  - exists b. split; [exact Hb| exact SUB].
Qed.

Lemma frame_entry : forall k len, In (k, len, ActrB.K_FRAME) wnl ->
  exists b, visf WW b /\ (bv_unsigned (ev E k), bv_unsigned (den E len)) = user_iv b /\ In (user_iv b) LB.
Proof.
  intros k len Hin. destruct (entry_window k len _ Hin) as (_ & INW & _). rewrite KF7 in INW.
  destruct TI as (_ & _ & _ & T4 & _). destruct (T4 _ INW eq_refl) as (b & Vb & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  exists b. split; [exact Vb|]. split; [exact EIV|].
  pose proof HWf as (_ & _ & _ & _ & _ & HLB & _). apply HLB. left. exists b. split; [exact (proj1 Vb)| reflexivity].
Qed.

Lemma owner_f : exists fb, visf WW fb /\ ab_addr fb = Af /\ ab_size fb - 8 = nf
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (ab_size fb)
  /\ In (user_iv fb) LB /\ In (fsh_iv fb) LB /\ user_iv fb = (Af, nf) /\ fsh_iv fb = (shad Af, shlen (ab_size fb)).
Proof.
  destruct (frame_entry kf lenf (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (fb & Vf & EIV & INU). fold Af nf in EIV.
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb (proj2 Vf)); reflexivity).
  rewrite UF in EIV. injection EIV as EA EN.
  destruct (entry_window sh lent _ (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite KFT8 in INW.
  destruct TI as (_ & _ & _ & _ & T5 & _). destruct (T5 _ INW eq_refl) as (fb' & Vf' & EIV'). unfold w_iv, fsh_iv in EIV'. cbn [w_lo w_len] in EIV'.
  injection EIV' as ES EL.
  destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB m mo fb HWf (proj1 Vf)) as (NP & B1 & B2 & HI). pose proof atop_range as ATR.
  assert (ESH : bv_unsigned (ev E sh) = shad Af).
  { rewrite (CallA.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. rewrite EA. clear - B2 HI NP ATR. pose proof (usz_le fb). Z.div_mod_to_equations. lia. }
  assert (EQB : fb' = fb).
  { pose proof HWf as (AH & _). apply (shadow_iv_inj AI AI_fake _ _ _ _ _ fb' fb AH (proj1 (proj1 Vf')) (proj1 (proj1 Vf))). rewrite <- ES, ESH, EA. reflexivity. }
  subst fb'. exists fb. split; [exact Vf|]. split; [symmetry; exact EA|]. split; [symmetry; exact EN|]. split; [exact ESH|]. split; [exact EL|].
  split; [exact INU|]. split.
  - pose proof HWf as (_ & _ & _ & _ & _ & HLB & _). apply HLB. right; right. exists fb. split; [exact Vf| reflexivity].
  - split; [rewrite UF, <- EA, <- EN; reflexivity| unfold fsh_iv; rewrite <- EA; reflexivity].
Qed.

Variable fb : ablock.
Hypothesis VF : visf WW fb.
Hypothesis EAf : ab_addr fb = Af.
Hypothesis ENf : ab_size fb - 8 = nf.
Hypothesis ESH : bv_unsigned (ev E sh) = shad Af.
Hypothesis ELT : bv_unsigned (den E lent) = shlen (ab_size fb).
Hypothesis INU : In (user_iv fb) LB.
Hypothesis INS : In (fsh_iv fb) LB.
Hypothesis UIV : user_iv fb = (Af, nf).
Hypothesis SIV : fsh_iv fb = (shad Af, shlen (ab_size fb)).

Lemma region_first_byte : forall k r0, rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = ActrB.K_FRAME \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> user_iv fb /\ b <> fsh_iv fb.
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _).
  destruct (entry_window kf lenf _ (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent _ (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 L0 P0) as RK.
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  split; intros ->.
  -
    rewrite UIV in INB. unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0, KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      destruct (frame_entry k len Hin) as (b2 & Vb2 & EIV2 & INU2).
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (user_iv b2) (user_iv fb) (bv_unsigned (ev E k)) AWHf INU2 INU).
      + rewrite <- EIV2, UIV. cbn [fst]. exact NA.
      + rewrite <- EIV2. exact A0IN.
      + rewrite UIV. unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    rewrite SIV in INB. unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INS' : bv_unsigned (ev E sh) + loZ rsh <= bv_unsigned (ev E k) < bv_unsigned (ev E sh) + hiZ E rsh).
    { unfold loZ. rewrite LO0s, KZ0, FULLs, ELT, ESH. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 sh rsh Fr0 Frs NKs ZK ZS (or_introl W0) _ (conj RK INS')).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> user_iv fb /\ b <> fsh_iv fb.
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT _]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd.
  assert (KT9 : w2Z K_TWIN = K_TWINz) by reflexivity. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  assert (EB : b = twin_iv b2).
  { apply (twin_container AI ACCT UNIV AI_fake WW aw LB m mo b2 b HWf Hb2T Hb). rewrite <- EIV. exact SUB. }
  destruct (iv_origin AI ACCT UNIV AI_fake WW aw LB m mo HWf) as (_ & O2 & _ & _ & O5 & _).
  subst b. split; intros X.
  - exact (O2 fb b2 (proj1 VF) Hb2T (eq_sym X)).
  - exact (O5 b2 fb Hb2T VF X).
Qed.

Let m' : amem := m.
Let mo' : Model := mo.
Definition LBk : blocks := remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB).
Definition Wf : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (fb :: w_FA WW) (w_ms WW) (w_zc WW - 1).

Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> user_iv fb /\ v <> fsh_iv fb).
Proof.
  intros v. unfold LBk. split.
  - intros H. apply in_remove in H as [H N2]. apply in_remove in H as [H N1]. auto.
  - intros (H & N1 & N2). apply in_in_remove; [exact N2|]. apply in_in_remove; [exact N1| exact H].
Qed.

Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPF : ATOP + 4096 <= sp.

Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.

Lemma SBf : forall a, 0 <= a < 2 ^ 64 -> CtrDelta.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof. intros; reflexivity. Qed.
Lemma SBVf : forall a, 0 <= a < 2 ^ 64 -> CtrDelta.stableA AI ms LBk a ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof. intros a Ha ST. apply (FrameV.frame_v_of_raw asegs). exact (SBf a Ha ST). Qed.

Lemma shad_band : forall a', 0 <= a' < 2 ^ 47 -> 0x7fff8000 <= shad a' < 0x10007fff8000.
Proof. intros a' H. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.

Lemma aci_47 : forall a, in_ranges (aci AI) a -> 0 <= a < 2 ^ 47.
Proof.
  intros a (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa. lia.
Qed.

Lemma WBMf : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb asegs m a = true -> wb asegs m' a = true.
Proof. intros a Ha CC H. exact H. Qed.

Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof. intros a Ha SC _. split; [reflexivity| exact (fun H => H)]. Qed.

Lemma SBSf : forall a, ATOP + 4096 <= a < bv_unsigned (AP.getr (ms_regs ms) 2%bv) ->
  rb asegs m' a = rb asegs m a /\ (wb asegs m a = true -> wb asegs m' a = true).
Proof. intros a Ha. split; [reflexivity| exact (fun H => H)]. Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd [NKf NKs] WL a Ha. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LBk_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV _ BT _ WL. split; intros ->.
  - rewrite WLf in WL. assert (X : ActrB.K_FRAME = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - rewrite WLt in WL. assert (X : ActrB.K_FTWIN = K_TWIN) by congruence. vm_compute in X. discriminate X.
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len _ _ WL _ _ _ _. split; intros ->.
  - rewrite WLf in WL. assert (X : ActrB.K_FRAME = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - rewrite WLt in WL. assert (X : ActrB.K_FTWIN = K_TWIN) by congruence. vm_compute in X. discriminate X.
Qed.

Lemma KEEP_delf : forall k0, ~ In k0 [kf; sh] -> KEEPf k0.
Proof. intros k0 H. split; intros ->; apply H; [left| right; left]; reflexivity. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.E' E st Fv Gv).

Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof. intros; reflexivity. Qed.

Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) ActrB.K_FRAME = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) ActrB.K_FTWIN = Some h2.
Variable h3 : list sv.
Hypothesis H3 : FaC.heap_pay (s_facts st) h2 1%uint63 = Some h3.

Definition WBf : window := Win Af nf K_FRAMEz.
Definition WTf : window := Win (shad Af) (shlen (ab_size fb)) K_FTWINz.

Lemma DEL3 : exists l1 l2 m1 m2 p1 p2 az,
  decode (map (den E') h3) = Some (w2Z md, den E A, p1 ++ Win (az - 1) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 /\ ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 /\ (forall w, In w (p1 ++ p2) -> not_cr w)
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.heap_del_window_k_facts E md A nw rest nn kf ActrB.K_FRAME h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.windows_anchored_nodup _ _ kf len1 ActrB.K_FRAME lenf ActrB.K_FRAME AN I1 (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (CtrFree.heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh ActrB.K_FTWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.windows_anchored_nodup _ _ sh len2 ActrB.K_FTWIN lent ActrB.K_FTWIN AN (S1 _ I2) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> _].

  assert (ND1 : List.NoDup (kf :: HeapCtrB.anchors wl1)) by (exact (Permutation_NoDup (CtrFree.anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.anchors wl2)) by (exact (Permutation_NoDup (CtrFree.anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  rewrite EH2 in H3.
  destruct (heap_pay_facts E (s_facts st) md A (wsub (wsub nw wone) wone) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) (pred (pred nn)) 1%uint63 h3 wl2 (so_facts _ _ _ _ _ _ HS) T2 N2 L2 NW2 H3)
    as (ws3 & p1 & ac & p2 & lsv & EH3 & P1 & P2 & RA & NZL & L3 & SK3 & NW3 & INL & S3').
  change (to_Z 1%uint63) with 1 in P2, RA.
  exists l1, l2, m1, m2, p1, p2, ac.
  split.
  { rewrite EH3. rewrite (decode_hargs E' md A _ _ (pred (pred nn)) T2 N2 L3).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB2 : forallb (sv_vars_below (s_next st)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) = true).
    { apply (CtrFree.forallb_sub _ rest); [| exact RB]. intros x Hx. apply S3. apply R3. exact Hx. }
    assert (RB3 : forallb (sv_vars_below (s_next st)) (ws3 ++ skipn (3 * pred (pred nn)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest))) = true).
    { apply forallb_forall. intros x Hx. destruct (S3' x Hx) as [X| ->]; [exact (proj1 (forallb_forall _ _) RB2 x X)|].
      apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact (proj1 (forallb_forall _ _) RB2 lsv INL)| reflexivity]. }
    rewrite (CtrDelta.den_E' E st Fv Gv A (CtrDelta.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrDelta.wins_of_E' E st Fv Gv _ _ RB3), P2, SK3, SK2, SK1.
    rewrite (CtrDelta.map_den_E' E st Fv Gv _ (CtrFree.forallb_skipn _ (3 * nn) rest RB)). reflexivity. }
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KF7. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KFT8. reflexivity. }
  split. { rewrite <- W2'. exact P1. }
  split; [exact RA|]. split; [exact NZL|].
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_FRAMEz, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent ActrB.K_FTWIN AN (S1 _ Ik) (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KFT8 in E3. unfold K_FRAMEz, K_FTWINz in E3. lia. }
    destruct (kept_block k len kd (user_iv fb) (S1 _ Ik) NKf NKs INU ltac:(rewrite UIV, <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_FTWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd (fsh_iv fb) (S1 _ (R1 _ Ik)) NKf NKs INS ltac:(rewrite SIV, <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma released_in_user : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> in_user LB a.
Proof.
  intros a Ha. unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (user_iv fb); split; [exact INU| exact Ha]| exists (fsh_iv fb); split; [exact INS| exact Ha]].
Qed.

Lemma released_off_image : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> find_segment asegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. pose proof atop_range as ATR. split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INU Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INS Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB m mo a HWf (released_in_user a Ha)) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma zc_ident : forall l1 l2 m1 m2 p1 p2 az,
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 ->
  Win az 0 K_STACK = zc_win (w_zc WW).
Proof.
  intros l1 l2 m1 m2 p1 p2 az W1 W2 W3 RA.
  assert (IN0 : In (Win az 0 K_STACK) (wins_of E nn rest)).
  { assert (X : In (Win az 0 K_STACK) (m1 ++ m2)) by (rewrite W3; apply in_or_app; right; left; reflexivity).
    assert (Y : In (Win az 0 K_STACK) (l1 ++ l2)) by (rewrite W2; apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]).
    rewrite W1. apply in_app_or in Y as [Y|Y]; apply in_or_app; [left; exact Y| right; right; exact Y]. }
  destruct TI as (_ & _ & _ & _ & _ & T6 & _).
  apply (T6 _ IN0); cbn [w_kind w_len w_lo]; [reflexivity| reflexivity| unfold ZC_BAND; lia].
Qed.

Lemma ZC1 : 1 <= w_zc WW.
Proof.
  destruct DEL3 as (l1 & l2 & m1 & m2 & p1 & p2 & a0 & _ & W1 & W2 & W3 & RA & _).
  pose proof (zc_ident l1 l2 m1 m2 p1 p2 a0 W1 W2 W3 RA) as EZC. unfold zc_win in EZC. injection EZC as X. unfold ZC_BASE, ZCB in *. lia.
Qed.

Lemma AR1 : aw_realW AI ACCT UNIV aw LBk m' mo' Wf.
Proof. exact (aw_real_abandon AI ACCT UNIV AI_fake aw LB m mo WW fb 1 AR VF (conj (Z.le_refl 1) ZC1)). Qed.

Lemma HOLDN3 : forall l1 l2 m1 m2 p1 p2 az,
  decode (map (den E') h3) = Some (w2Z md, den E A, p1 ++ Win (az - 1) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 ->
  m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 -> (forall w, In w (p1 ++ p2) -> not_cr w) ->
  ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h3) m' mo'.
Proof.
  intros l1 l2 m1 m2 p1 p2 az D W1 W2 W3 RA NZL NB NT. rewrite OPS_holds1.
  pose proof (zc_ident l1 l2 m1 m2 p1 p2 az W1 W2 W3 RA) as EZC.
  assert (EA : az = ZC_BASE + w_zc WW) by (unfold zc_win in EZC; injection EZC as X; exact X).
  assert (EZC' : Win (az - 1) 0 K_STACK = zc_win (w_zc WW - 1)) by (unfold zc_win; f_equal; lia).
  assert (ZCBND : ZC_BASE + (w_zc WW - 1) < ZC_BAND) by (unfold ZC_BAND; lia).
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (NZC : ~ In (zc_win (w_zc WW)) (p1 ++ p2)).
  { intros X. apply (NZL _ X). unfold zc_win. cbn [w_kind w_len w_lo]. split; [reflexivity|]. split; [reflexivity|]. unfold ZCB, ZC_BASE in *. lia. }
  assert (IN3 : forall w, In w (p1 ++ Win (az - 1) 0 K_STACK :: p2) <-> (In w (m1 ++ m2) /\ w <> zc_win (w_zc WW)) \/ w = zc_win (w_zc WW - 1)).
  { intros w. rewrite W3, EZC, EZC'. split.
    - intros H. apply in_app_or in H as [H|[H|H]].
      + left. split; [apply in_or_app; left; exact H| intros ->; apply NZC; apply in_or_app; left; exact H].
      + right. symmetry. exact H.
      + left. split; [apply in_or_app; right; right; exact H| intros ->; apply NZC; apply in_or_app; right; exact H].
    - intros [[H NE]| ->]; [| apply in_or_app; right; left; reflexivity].
      apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; right; exact H]. }
  exists (w2Z md), aw, (p1 ++ Win (az - 1) 0 K_STACK :: p2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact (proj1 AR1)|]. split; [| split].
  -
    apply Forall_forall. intros w Hw. apply IN3 in Hw as [[Hw NZ]| ->].
    2:{ pose proof atop_range as ATR. unfold zc_win, window_wf. cbn [w_lo w_len w_kind]. unfold ZC_BASE, ZCB, two64 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia]. }
    apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKf : k <> kf).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ kf len kd lenf ActrB.K_FRAME AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
      apply NWB. rewrite EW. unfold WBf. rewrite KF7. reflexivity. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.windows_anchored_nodup _ _ sh len kd lent ActrB.K_FTWIN AN Ik (HeapCtrB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KFT8. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LBk_In. split; [exact B|].
      apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a0 Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LBk_In. split; [exact Hb|].
      apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  -
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free_f K_FRAMEz _ _ _ _ m Af nf (l1 ++ l2) (or_introl eq_refl) HC INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free_f K_FTWINz _ _ _ _ m (shad Af) (shlen (ab_size fb)) (m1 ++ m2) (or_intror eq_refl) HC2 INT IN2) as HC3.
    pose proof (Cw_zc _ _ _ _ (p1 ++ Win (az - 1) 0 K_STACK :: p2) m (w_zc WW) (w_zc WW - 1) HC3 ZCBND IN3) as HC4.
    unfold LBk. rewrite UIV, SIV. exact HC4.
  -
    apply (ties_abandon AI ACCT UNIV AI_fake WW Wf aw LB m mo (wins_of E nn rest) (p1 ++ Win (az - 1) 0 K_STACK :: p2) fb 1 HWf TI eq_refl eq_refl ZC1 VF).
    + intros b. unfold visf, vis, Wf. cbn [w_LBa w_FA In]. split.
      * intros [[Hb NF] FK]. split; [split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact FK]| intros ->; apply NF; left; reflexivity].
      * intros [[[Hb NF] FK] NE]. split; [split; [exact Hb| intros [X|X]; [apply NE; symmetry; exact X| exact (NF X)]]| exact FK].
    + intros w. rewrite IN3, IN2, IN1. unfold WBf, WTf. rewrite EAf, ENf. tauto.
    +
      intros b _ [Hb NF]. unfold Wf in Hb, NF. cbn [w_LBa w_FA In] in Hb, NF. split; [exact Hb| intros X; apply NF; right; exact X].
    + exact ZCBND.
    + exact (fun P => P).
Qed.

Variable R' : bvmap 5 word.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition RgF : IMap.t region := CtrDelta.RgPg (s_regs st) [] [kf; sh].
Definition NEWSETf (_ : Z) : Prop := False.

Lemma RgF_eq : RgF = IMap.remove sh (IMap.remove kf (s_regs st)).
Proof. reflexivity. Qed.

Lemma released_band : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800bde00 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof HWf as (AH & _).
  destruct (blk_facts AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF))) as (NP & BK & HI & _).
  destruct (shadow_tight (ab_addr fb) (ab_size fb) BK HI NP) as [T1 T2].
  assert (SL : shlen (ab_size fb) <= shlen (ab_size fb + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
  pose proof (usz_le fb) as UL.
  unfold ablk, AIMG_HI, KLS in BK. unfold in_iv, user_iv, fsh_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma released_apart : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> ~ in_user LBk a.
Proof.
  intros a Ha U. apply in_ivs_In in U as (b' & Hb' & Hin). apply LBk_In in Hb' as (Hb' & N1 & N2).
  destruct Ha as [Ha|Ha].
  - destruct (Z.eq_dec (fst b') (fst (user_iv fb))) as [EQ|NE].
    + apply N1. destruct b' as [A' n']. rewrite UIV in *. cbn [fst] in EQ. subst A'. f_equal.
      exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo Af n' nf HWf Hb' INU).
    + exact (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo b' (user_iv fb) a AWHf Hb' INU NE Hin Ha).
  - destruct (Z.eq_dec (fst b') (fst (fsh_iv fb))) as [EQ|NE].
    + apply N2. destruct b' as [A' n']. rewrite SIV in *. cbn [fst] in EQ. subst A'. f_equal.
      exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo (shad Af) n' (shlen (ab_size fb)) HWf Hb' INS).
    + exact (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo b' (fsh_iv fb) a AWHf Hb' INS NE Hin Ha).
Qed.

Lemma released_unbased : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA). destruct (released_off_image a Ha) as [_ LOW].
  destruct (CtrDelta.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR
              (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl)
              hargs md A nw Hf Hc Eh Tnw Nn Ln [] [kf; sh]
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  - exact (released_apart a Ha X).
  - pose proof atop_range as ATR.
    assert (A47 : 0 <= ATOP < 2 ^ 47) by (clear - ATR; lia). pose proof (shad_band ATOP A47) as SHA.
    destruct (sh_cov_band a X) as [C|C]; destruct (released_band a Ha) as [B|B]; lia.
Qed.

Theorem fa_post_ok : forall (pc' : int) (rf' : FI.rf sv) (nx' : int),
  s_resv st = RNone ->
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  st_ok asegs OPS E' (SS pc' rf' (s_ff st) RNone (IMap.remove sh (IMap.remove kf (s_regs st))) (s_facts st) (set_op HEAP_ID h3 (s_ops st)) (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None m' (seg_rom asegs)) mo'.
Proof.
  intros pc' rf' nx' RVN X0Z REGS. rewrite <- RgF_eq.
  destruct DEL3 as (l1 & l2 & m1 & m2 & p1 & p2 & az & D & W1 & W2 & W3 & RA & NZL & NB & NT).
  pose proof (HOLDN3 l1 l2 m1 m2 p1 p2 az D W1 W2 W3 RA NZL NB NT) as HOLDN.
  set (ws3 := p1 ++ Win (az - 1) 0 K_STACK :: p2) in *.

  assert (WS3 : forall a0, in_ws ws3 a0 <-> in_ws (m1 ++ m2) a0).
  { intros a0. unfold in_ws, ws3. rewrite W3.
    split; intros X; apply in_ivs_In in X as (v & Hv & Hin); apply in_map_iff in Hv as (w & <- & Hw); apply in_ivs_In.
    - apply in_app_or in Hw as [Hw|[<-|Hw]].
      + exists (w_iv w). split; [apply in_map; apply in_or_app; left; exact Hw| exact Hin].
      + exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia.
      + exists (w_iv w). split; [apply in_map; apply in_or_app; right; right; exact Hw| exact Hin].
    - apply in_app_or in Hw as [Hw|[<-|Hw]].
      + exists (w_iv w). split; [apply in_map; apply in_or_app; left; exact Hw| exact Hin].
      + exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia.
      + exists (w_iv w). split; [apply in_map; apply in_or_app; right; right; exact Hw| exact Hin]. }
  assert (INWS : forall a0, in_ws (wins_of E nn rest) a0 -> in_ws ws3 a0 \/ in_iv (user_iv fb) a0 \/ in_iv (fsh_iv fb) a0).
  { intros a0 X. rewrite WS3. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite UIV, SIV.
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (RSNOK : region_ok asegs (s_priv st) E' m' ks rss).
  { apply (CtrDelta.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m' ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv R' m' mo' aw LB LBk AWHf MINV' SBVf SBOf WBMf SBTf SBSf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [kf; sh] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h3 (w2Z md) (den E A) ws3 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a0 X. destruct X.
  -   intros a0 Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a0) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a0 IW) as [X|FR]; [contradiction|]. split; [exact (proj1 (released_off_image a0 FR))| exact (released_unbased a0 FR)].
  -   intros a0 IB X. pose proof (CtrDelta.in_heap_ws _ _ X) as IW. destruct (INWS a0 IW) as [Y|FR]; [| exfalso; exact (released_unbased a0 FR IB)].
    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a0 -> False).
    { intros w0 [-> | ->] Hw0; unfold WBf, WTf, w_iv in Hw0; cbn [w_lo w_len] in Hw0;
        [rewrite <- UIV in Hw0; exact (released_unbased a0 (or_introl Hw0) IB)| rewrite <- SIV in Hw0; exact (released_unbased a0 (or_intror Hw0) IB)]. }
    assert (KEPT3 : In w (m1 ++ m2) -> In w ws3).
    { intros X. unfold ws3. rewrite W3 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; left; exact X| | apply in_or_app; right; right; exact X].
      exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia. }
    apply KEPT3.
    apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin)|].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
  - exact X0Z.
  - exact REGS.
  - reflexivity.
  - exact (so_facts _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact MINVo.
Qed.
End RELEASED.
End Fa.

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
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Import ActrB.TwinB FfShape.TwinB FaC.TwinB FaShape.TwinB.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Lemma KF7 : w2Z ActrB.TwinB.ActrB.K_FRAME = K_FRAMEz. Proof. reflexivity. Qed.
Lemma KFT8 : w2Z ActrB.TwinB.ActrB.K_FTWIN = K_FTWINz. Proof. reflexivity. Qed.

Section Fa.
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

Hypothesis Cw_ghost_free_f : forall kd md ca LB ws m b n ws', kd = K_FRAMEz \/ kd = K_FTWINz -> cw_holds Cw md ca LB ws m -> In (Win b n kd) ws ->
  (forall w, In w ws' <-> In w ws /\ w <> Win b n kd) -> cw_holds Cw md ca (remove iv_eq_dec (b, n) LB) ws' m.
Hypothesis Cw_zc : forall md ca LB ws ws' m zc zc', cw_holds Cw md ca LB ws m -> ZC_BASE + zc' < ZC_BAND ->
  (forall w, In w ws' <-> (In w ws /\ w <> zc_win zc) \/ w = zc_win zc') -> cw_holds Cw md ca LB ws' m.
Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.
Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Section RELEASED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis AN : CtrA.windows_anchored (s_regs st) wnl = true.
Hypothesis TS : twins_scan (s_facts st) (s_regs st) wnl wnl = true.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Variables (kf sh : int).

Variables (rf rsh : region) (lenf lent : sv).
Hypothesis Frf : IMap.find kf (s_regs st) = Some rf.
Hypothesis Frs : IMap.find sh (s_regs st) = Some rsh.
Hypothesis WLf : CtrA.win_lookup wnl kf = Some (lenf, ActrB.TwinB.ActrB.K_FRAME).
Hypothesis WLt : CtrA.win_lookup wnl sh = Some (lent, ActrB.TwinB.ActrB.K_FTWIN).
Hypothesis BTs : block_of_twin (s_facts st) sh = Some kf.
Hypothesis LO0 : rg_lo rf = 0%uint63.
Hypothesis POSf : 0 < hiZ E rf.
Hypothesis LEf : hiZ E rf <= bv_unsigned (den E lenf).
Hypothesis LO0s : rg_lo rsh = 0%uint63.
Hypothesis FULLs : hiZ E rsh = bv_unsigned (den E lent).
Hypothesis OTHERS : forall k len kd, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  (weqb kd K_TWIN = true /\ exists kb, block_of_twin (s_facts st) k = Some kb /\ kb <> kf)
  \/ (weqb kd K_TWIN = false /\ exists r0, IMap.find k (s_regs st) = Some r0 /\ rg_lo r0 = 0%uint63 /\ hiZ E r0 <= bv_unsigned (den E len) /\ 0 < hiZ E r0
        /\ rg_w r0 = true /\ (kd = ActrB.TwinB.ActrB.K_FRAME \/ hiZ E rf = bv_unsigned (den E lenf))).

Let Af : Z := bv_unsigned (ev E kf).
Let nf : Z := bv_unsigned (den E lenf).
Let m : amem := ms_mem ms.

Lemma AWHf : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWf : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma entry_window : forall k len kd, In (k, len, kd) wnl ->
  k <> 0%uint63 /\ In (Win (bv_unsigned (ev E k)) (bv_unsigned (den E len)) (w2Z kd)) (wins_of E nn rest)
  /\ exists b, In b LB /\ (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a).
Proof.
  intros k len kd Hin. destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k len kd NW Hin) as (K0 & _ & KD & INW).
  split; [exact K0|]. split; [exact INW|].
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - eexists. split; [exact B|]. intros a Ha; exact Ha.
  - exists b. split; [exact Hb| exact SUB].
Qed.

Lemma frame_entry : forall k len, In (k, len, ActrB.TwinB.ActrB.K_FRAME) wnl ->
  exists b, visf WW b /\ (bv_unsigned (ev E k), bv_unsigned (den E len)) = user_iv b /\ In (user_iv b) LB.
Proof.
  intros k len Hin. destruct (entry_window k len _ Hin) as (_ & INW & _). rewrite KF7 in INW.
  destruct TI as (_ & _ & _ & T4 & _). destruct (T4 _ INW eq_refl) as (b & Vb & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  exists b. split; [exact Vb|]. split; [exact EIV|].
  pose proof HWf as (_ & _ & _ & _ & _ & HLB & _). apply HLB. left. exists b. split; [exact (proj1 Vb)| reflexivity].
Qed.

Lemma owner_f : exists fb, visf WW fb /\ ab_addr fb = Af /\ ab_size fb - 8 = nf
  /\ bv_unsigned (ev E sh) = shad Af /\ bv_unsigned (den E lent) = shlen (ab_size fb)
  /\ In (user_iv fb) LB /\ In (fsh_iv fb) LB /\ user_iv fb = (Af, nf) /\ fsh_iv fb = (shad Af, shlen (ab_size fb)).
Proof.
  destruct (frame_entry kf lenf (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (fb & Vf & EIV & INU). fold Af nf in EIV.
  assert (UF : user_iv fb = (ab_addr fb, ab_size fb - 8)) by (unfold user_iv; rewrite (usz_fake fb (proj2 Vf)); reflexivity).
  rewrite UF in EIV. injection EIV as EA EN.
  destruct (entry_window sh lent _ (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (_ & INW & _). rewrite KFT8 in INW.
  destruct TI as (_ & _ & _ & _ & T5 & _). destruct (T5 _ INW eq_refl) as (fb' & Vf' & EIV'). unfold w_iv, fsh_iv in EIV'. cbn [w_lo w_len] in EIV'.
  injection EIV' as ES EL.
  destruct (LB_user_facts AI ACCT UNIV AI_fake WW aw LB m mo fb HWf (proj1 Vf)) as (NP & B1 & B2 & HI). pose proof atop_range as ATR.
  assert (ESH : bv_unsigned (ev E sh) = shad Af).
  { rewrite (CallA.TwinB.block_of_twin_sound E _ sh kf (so_facts _ _ _ _ _ _ HS) BTs). fold Af. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8.
    rewrite Z.mod_small; [lia|]. rewrite EA. clear - B2 HI NP ATR. pose proof (usz_le fb). Z.div_mod_to_equations. lia. }
  assert (EQB : fb' = fb).
  { pose proof HWf as (AH & _). apply (shadow_iv_inj AI AI_fake _ _ _ _ _ fb' fb AH (proj1 (proj1 Vf')) (proj1 (proj1 Vf))). rewrite <- ES, ESH, EA. reflexivity. }
  subst fb'. exists fb. split; [exact Vf|]. split; [symmetry; exact EA|]. split; [symmetry; exact EN|]. split; [exact ESH|]. split; [exact EL|].
  split; [exact INU|]. split.
  - pose proof HWf as (_ & _ & _ & _ & _ & HLB & _). apply HLB. right; right. exists fb. split; [exact Vf| reflexivity].
  - split; [rewrite UF, <- EA, <- EN; reflexivity| unfold fsh_iv; rewrite <- EA; reflexivity].
Qed.

Variable fb : ablock.
Hypothesis VF : visf WW fb.
Hypothesis EAf : ab_addr fb = Af.
Hypothesis ENf : ab_size fb - 8 = nf.
Hypothesis ESH : bv_unsigned (ev E sh) = shad Af.
Hypothesis ELT : bv_unsigned (den E lent) = shlen (ab_size fb).
Hypothesis INU : In (user_iv fb) LB.
Hypothesis INS : In (fsh_iv fb) LB.
Hypothesis UIV : user_iv fb = (Af, nf).
Hypothesis SIV : fsh_iv fb = (shad Af, shlen (ab_size fb)).

Lemma region_first_byte : forall k r0, rg_lo r0 = 0%uint63 -> 0 < hiZ E r0 ->
  bv_unsigned (ev E k) + loZ r0 <= bv_unsigned (ev E k) < bv_unsigned (ev E k) + hiZ E r0.
Proof. intros k r0 L0 P. unfold loZ. rewrite L0. assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity. rewrite KZ0. lia. Qed.

Lemma kept_block_w : forall k len kd r0 b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  IMap.find k (s_regs st) = Some r0 -> rg_lo r0 = 0%uint63 -> hiZ E r0 <= bv_unsigned (den E len) -> 0 < hiZ E r0 -> rg_w r0 = true ->
  (kd = ActrB.TwinB.ActrB.K_FRAME \/ hiZ E rf = nf) ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> user_iv fb /\ b <> fsh_iv fb.
Proof.
  intros k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB.
  destruct (entry_window k len kd Hin) as (K0 & _).
  destruct (entry_window kf lenf _ (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as (Kf0 & _).
  destruct (entry_window sh lent _ (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as (Ks0 & _).
  assert (ZK : PrimInt63.eqb k 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  assert (ZF : PrimInt63.eqb kf 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Kf0).
  assert (ZS : PrimInt63.eqb sh 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact Ks0).
  assert (A0IN : in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) (bv_unsigned (ev E k))) by (unfold in_iv; cbn [fst snd]; lia).
  pose proof (SUB _ A0IN) as INB. pose proof (region_first_byte k r0 L0 P0) as RK.
  assert (KZ0 : keyZ 0%uint63 = 0) by reflexivity.
  split; intros ->.
  -
    rewrite UIV in INB. unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INF : bv_unsigned (ev E kf) + loZ rf <= bv_unsigned (ev E k) < bv_unsigned (ev E kf) + hiZ E rf).
    { unfold loZ. rewrite LO0, KZ0. fold Af. destruct CASE as [->|FULL]; [| lia].

      destruct (frame_entry k len Hin) as (b2 & Vb2 & EIV2 & INU2).
      destruct (Z.eq_dec (bv_unsigned (ev E k)) Af) as [EA|NA]; [lia| exfalso].
      apply (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo (user_iv b2) (user_iv fb) (bv_unsigned (ev E k)) AWHf INU2 INU).
      + rewrite <- EIV2, UIV. cbn [fst]. exact NA.
      + rewrite <- EIV2. exact A0IN.
      + rewrite UIV. unfold in_iv. cbn [fst snd]. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 kf rf Fr0 Frf NKf ZK ZF (or_introl W0) _ (conj RK INF)).
  -
    rewrite SIV in INB. unfold in_iv in INB. cbn [fst snd] in INB.
    assert (INS' : bv_unsigned (ev E sh) + loZ rsh <= bv_unsigned (ev E k) < bv_unsigned (ev E sh) + hiZ E rsh).
    { unfold loZ. rewrite LO0s, KZ0, FULLs, ELT, ESH. lia. }
    exact (so_disj _ _ _ _ _ _ HS k r0 sh rsh Fr0 Frs NKs ZK ZS (or_introl W0) _ (conj RK INS')).
Qed.

Lemma kept_block : forall k len kd b, In (k, len, kd) wnl -> k <> kf -> k <> sh ->
  In b LB -> (forall a, in_iv (bv_unsigned (ev E k), bv_unsigned (den E len)) a -> in_iv b a) ->
  b <> user_iv fb /\ b <> fsh_iv fb.
Proof.
  intros k len kd b Hin NKf NKs Hb SUB.
  destruct (OTHERS k len kd Hin NKf NKs) as [[KT _]|(KT & r0 & Fr0 & L0 & LE0 & P0 & W0 & CASE)].
  2:{ exact (kept_block_w k len kd r0 b Hin NKf NKs Fr0 L0 LE0 P0 W0 CASE Hb SUB). }

  destruct (entry_window k len kd Hin) as (_ & INWk & _). apply weqb_eq in KT. subst kd.
  assert (KT9 : w2Z K_TWIN = K_TWINz) by reflexivity. rewrite KT9 in INWk.
  destruct TI as (_ & T2 & _). destruct (T2 _ INWk eq_refl) as (b2 & Hb2T & EIV). unfold w_iv in EIV. cbn [w_lo w_len] in EIV.
  assert (EB : b = twin_iv b2).
  { apply (twin_container AI ACCT UNIV AI_fake WW aw LB m mo b2 b HWf Hb2T Hb). rewrite <- EIV. exact SUB. }
  destruct (iv_origin AI ACCT UNIV AI_fake WW aw LB m mo HWf) as (_ & O2 & _ & _ & O5 & _).
  subst b. split; intros X.
  - exact (O2 fb b2 (proj1 VF) Hb2T (eq_sym X)).
  - exact (O5 b2 fb Hb2T VF X).
Qed.

Let m' : amem := m.
Let mo' : Model := mo.
Definition LBk : blocks := remove iv_eq_dec (fsh_iv fb) (remove iv_eq_dec (user_iv fb) LB).
Definition Wf : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (fb :: w_FA WW) (w_ms WW) (w_zc WW - 1).

Lemma LBk_In : forall v, In v LBk <-> (In v LB /\ v <> user_iv fb /\ v <> fsh_iv fb).
Proof.
  intros v. unfold LBk. split.
  - intros H. apply in_remove in H as [H N2]. apply in_remove in H as [H N1]. auto.
  - intros (H & N1 & N2). apply in_in_remove; [exact N2|]. apply in_in_remove; [exact N1| exact H].
Qed.

Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPF : ATOP + 4096 <= sp.

Lemma LBk_sub : forall v, In v LBk -> In v LB.
Proof. intros v H. exact (proj1 (proj1 (LBk_In v) H)). Qed.

Lemma SBf : forall a, 0 <= a < 2 ^ 64 -> CtrDelta.TwinB.stableA AI ms LBk a -> m' (ALib.Mem.wa a) = m (ALib.Mem.wa a).
Proof. intros; reflexivity. Qed.
Lemma SBVf : forall a, 0 <= a < 2 ^ 64 -> CtrDelta.TwinB.stableA AI ms LBk a ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof. intros a Ha ST. apply (FrameV.TwinB.frame_v_of_raw bsegs). exact (SBf a Ha ST). Qed.

Lemma shad_band : forall a', 0 <= a' < 2 ^ 47 -> 0x7fff8000 <= shad a' < 0x10007fff8000.
Proof. intros a' H. unfold shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. Z.div_mod_to_equations. lia. Qed.

Lemma aci_47 : forall a, in_ranges (aci AI) a -> 0 <= a < 2 ^ 47.
Proof.
  intros a (iv0 & Hi & RRa). pose proof (AI_aci_img AI iv0 Hi) as HIa. pose proof (AI_aci_lo AI iv0 Hi) as LOa. unfold AIMG_HI in HIa. lia.
Qed.

Lemma WBMf : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb bsegs m a = true -> wb bsegs m' a = true.
Proof. intros a Ha CC H. exact H. Qed.

Lemma SBTf : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof. intros a Ha SC _. split; [reflexivity| exact (fun H => H)]. Qed.

Lemma SBSf : forall a, ATOP + 4096 <= a < bv_unsigned (AP.getr (ms_regs ms) 2%bv) ->
  rb bsegs m' a = rb bsegs m a /\ (wb bsegs m a = true -> wb bsegs m' a = true).
Proof. intros a Ha. split; [reflexivity| exact (fun H => H)]. Qed.

Definition KEEPf (k0 : int) : Prop := k0 <> kf /\ k0 <> sh.

Lemma WINKf : forall k0 len kd, KEEPf k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Proof.
  intros k0 len kd [NKf NKs] WL a Ha. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (entry_window k0 len kd Hin) as (_ & _ & b & Hb & SUB).
  destruct (kept_block k0 len kd b Hin NKf NKs Hb SUB) as [N1 N2].
  apply in_ivs_In. exists b. split; [apply LBk_In; auto|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Lemma VKEEPf : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEPf k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEPf sh'.
Proof.
  intros k0 rg hs n sh' len Fk ZV _ BT _ WL. split; intros ->.
  - rewrite WLf in WL. assert (X : ActrB.TwinB.ActrB.K_FRAME = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - rewrite WLt in WL. assert (X : ActrB.TwinB.ActrB.K_FTWIN = K_TWIN) by congruence. vm_compute in X. discriminate X.
Qed.

Lemma TKEEPf : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEPf k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEPf sh'.
Proof.
  intros k0 rg sh' kb n len _ _ WL _ _ _ _. split; intros ->.
  - rewrite WLf in WL. assert (X : ActrB.TwinB.ActrB.K_FRAME = K_TWIN) by congruence. vm_compute in X. discriminate X.
  - rewrite WLt in WL. assert (X : ActrB.TwinB.ActrB.K_FTWIN = K_TWIN) by congruence. vm_compute in X. discriminate X.
Qed.

Lemma KEEP_delf : forall k0, ~ In k0 [kf; sh] -> KEEPf k0.
Proof. intros k0 H. split; intros ->; apply H; [left| right; left]; reflexivity. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.TwinB.E' E st Fv Gv).

Lemma SBOf : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Proof. intros; reflexivity. Qed.

Variables (h1 h2 : list sv).
Hypothesis H1 : heap_del_window_k hargs (VP kf wzero) ActrB.TwinB.ActrB.K_FRAME = Some h1.
Hypothesis H2 : heap_del_window_k h1 (VP sh wzero) ActrB.TwinB.ActrB.K_FTWIN = Some h2.
Variable h3 : list sv.
Hypothesis H3 : FaC.TwinB.FaC.heap_pay (s_facts st) h2 1%uint63 = Some h3.

Definition WBf : window := Win Af nf K_FRAMEz.
Definition WTf : window := Win (shad Af) (shlen (ab_size fb)) K_FTWINz.

Lemma DEL3 : exists l1 l2 m1 m2 p1 p2 az,
  decode (map (den E') h3) = Some (w2Z md, den E A, p1 ++ Win (az - 1) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = l1 ++ WBf :: l2 /\ l1 ++ l2 = m1 ++ WTf :: m2
  /\ m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 /\ ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 /\ (forall w, In w (p1 ++ p2) -> not_cr w)
  /\ ~ In WBf (l1 ++ l2) /\ ~ In WTf (m1 ++ m2).
Proof.
  pose proof (HeapCtrB.TwinB.windows_anchored_nodup_anchors _ _ AN) as NDA.
  rewrite Eh in H1.
  destruct (CtrFree.TwinB.heap_del_window_k_facts E md A nw rest nn kf ActrB.TwinB.ActrB.K_FRAME h1 wnl eq_refl Tnw Nn Ln NW H1)
    as (ws1 & l1 & len1 & l2 & wl1 & EH1 & I1 & W1 & W1' & T1 & N1 & L1 & SK1 & NW1 & S1 & S2 & S3 & M1 & PM1).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len1 ActrB.TwinB.ActrB.K_FRAME lenf ActrB.TwinB.ActrB.K_FRAME AN I1 (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> _].
  rewrite EH1 in H2.
  destruct (CtrFree.TwinB.heap_del_window_k_facts E md A (wsub nw wone) (ws1 ++ skipn (3 * nn) rest) (pred nn) sh ActrB.TwinB.ActrB.K_FTWIN h2 wl1 eq_refl T1 N1 L1 NW1 H2)
    as (ws2 & m1 & len2 & m2 & wl2 & EH2 & I2 & W2 & W2' & T2 & N2 & L2 & SK2 & NW2 & R1 & R2 & R3 & M2 & PM2).
  destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len2 ActrB.TwinB.ActrB.K_FTWIN lent ActrB.TwinB.ActrB.K_FTWIN AN (S1 _ I2) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> _].

  assert (ND1 : List.NoDup (kf :: HeapCtrB.TwinB.anchors wl1)) by (exact (Permutation_NoDup (CtrFree.TwinB.anchors_perm _ _ PM1) NDA)).
  apply List.NoDup_cons_iff in ND1 as [NKF1 ND1'].
  assert (ND2 : List.NoDup (sh :: HeapCtrB.TwinB.anchors wl2)) by (exact (Permutation_NoDup (CtrFree.TwinB.anchors_perm _ _ PM2) ND1')).
  apply List.NoDup_cons_iff in ND2 as [NSH2 _].
  assert (ANCH : forall (l : list (int * sv * w64)) k len kd, In (k, len, kd) l -> In k (HeapCtrB.TwinB.anchors l)).
  { intros l k len kd H. unfold HeapCtrB.TwinB.anchors. apply in_map_iff. exists (k, len, kd). auto. }
  rewrite EH2 in H3.
  destruct (heap_pay_facts E (s_facts st) md A (wsub (wsub nw wone) wone) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) (pred (pred nn)) 1%uint63 h3 wl2 (so_facts _ _ _ _ _ _ HS) T2 N2 L2 NW2 H3)
    as (ws3 & p1 & ac & p2 & lsv & EH3 & P1 & P2 & RA & NZL & L3 & SK3 & NW3 & INL & S3').
  change (to_Z 1%uint63) with 1 in P2, RA.
  exists l1, l2, m1, m2, p1, p2, ac.
  split.
  { rewrite EH3. rewrite (decode_hargs E' md A _ _ (pred (pred nn)) T2 N2 L3).
    assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.TwinB.rest_below st FOK rest hargs md A nw Hf Eh).
    assert (RB2 : forallb (sv_vars_below (s_next st)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest)) = true).
    { apply (CtrFree.TwinB.forallb_sub _ rest); [| exact RB]. intros x Hx. apply S3. apply R3. exact Hx. }
    assert (RB3 : forallb (sv_vars_below (s_next st)) (ws3 ++ skipn (3 * pred (pred nn)) (ws2 ++ skipn (3 * pred nn) (ws1 ++ skipn (3 * nn) rest))) = true).
    { apply forallb_forall. intros x Hx. destruct (S3' x Hx) as [X| ->]; [exact (proj1 (forallb_forall _ _) RB2 x X)|].
      apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact (proj1 (forallb_forall _ _) RB2 lsv INL)| reflexivity]. }
    rewrite (CtrDelta.TwinB.den_E' E st Fv Gv A (CtrDelta.TwinB.A_below st FOK rest hargs md A nw Hf Eh)).
    rewrite (CtrDelta.TwinB.wins_of_E' E st Fv Gv _ _ RB3), P2, SK3, SK2, SK1.
    rewrite (CtrDelta.TwinB.map_den_E' E st Fv Gv _ (CtrFree.TwinB.forallb_skipn _ (3 * nn) rest RB)). reflexivity. }
  split. { rewrite W1. unfold WBf. fold Af nf. rewrite KF7. reflexivity. }
  split. { rewrite <- W1', W2. unfold WTf. rewrite ESH, ELT, KFT8. reflexivity. }
  split. { rewrite <- W2'. exact P1. }
  split; [exact RA|]. split; [exact NZL|].
  split.
  - intros X. rewrite <- W1' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred nn) _ wl1 WBf NW1 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_FRAMEz, K_STACK in KS; lia|].
    unfold WBf in EW. injection EW as E1 E2 E3.
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ Ik))).
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent ActrB.TwinB.ActrB.K_FTWIN AN (S1 _ Ik) (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [_ ->]. rewrite KFT8 in E3. unfold K_FRAMEz, K_FTWINz in E3. lia. }
    destruct (kept_block k len kd (user_iv fb) (S1 _ Ik) NKf NKs INU ltac:(rewrite UIV, <- E1, <- E2; intros a Ha; exact Ha)) as [NE _]. exact (NE eq_refl).
  - intros X. rewrite <- W2' in X.
    destruct (HeapCtrB.TwinB.wins_cover E (pred (pred nn)) _ wl2 WTf NW2 X) as [KS|(k & len & kd & Ik & EW)]; [cbn in KS; unfold K_FTWINz, K_STACK in KS; lia|].
    unfold WTf in EW. injection EW as E1 E2 E3.
    assert (NKs : k <> sh) by (intros ->; exact (NSH2 (ANCH _ _ _ _ Ik))).
    assert (NKf : k <> kf) by (intros ->; exact (NKF1 (ANCH _ _ _ _ (R1 _ Ik)))).
    destruct (kept_block k len kd (fsh_iv fb) (S1 _ (R1 _ Ik)) NKf NKs INS ltac:(rewrite SIV, <- E1, <- E2; intros a Ha; exact Ha)) as [_ NE]. exact (NE eq_refl).
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.

Lemma released_in_user : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> in_user LB a.
Proof.
  intros a Ha. unfold in_user. apply in_ivs_In. destruct Ha as [Ha|Ha]; [exists (user_iv fb); split; [exact INU| exact Ha]| exists (fsh_iv fb); split; [exact INS| exact Ha]].
Qed.

Lemma released_off_image : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> find_segment bsegs a 1 = None /\ a < ATOP.
Proof.
  intros a Ha. pose proof atop_range as ATR. split.
  - destruct Ha as [Ha|Ha]; [exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INU Ha))
                            | exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB m mo _ a AWHf INS Ha))].
  - destruct (LB_band AI ACCT UNIV AI_fake WW aw LB m mo a HWf (released_in_user a Ha)) as [B|[B|B]]; unfold AIMG_HI, KLS in *; lia.
Qed.

Lemma zc_ident : forall l1 l2 m1 m2 p1 p2 az,
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 -> m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 ->
  Win az 0 K_STACK = zc_win (w_zc WW).
Proof.
  intros l1 l2 m1 m2 p1 p2 az W1 W2 W3 RA.
  assert (IN0 : In (Win az 0 K_STACK) (wins_of E nn rest)).
  { assert (X : In (Win az 0 K_STACK) (m1 ++ m2)) by (rewrite W3; apply in_or_app; right; left; reflexivity).
    assert (Y : In (Win az 0 K_STACK) (l1 ++ l2)) by (rewrite W2; apply in_app_or in X as [X|X]; apply in_or_app; [left; exact X| right; right; exact X]).
    rewrite W1. apply in_app_or in Y as [Y|Y]; apply in_or_app; [left; exact Y| right; right; exact Y]. }
  destruct TI as (_ & _ & _ & _ & _ & T6 & _).
  apply (T6 _ IN0); cbn [w_kind w_len w_lo]; [reflexivity| reflexivity| unfold ZC_BAND; lia].
Qed.

Lemma ZC1 : 1 <= w_zc WW.
Proof.
  destruct DEL3 as (l1 & l2 & m1 & m2 & p1 & p2 & a0 & _ & W1 & W2 & W3 & RA & _).
  pose proof (zc_ident l1 l2 m1 m2 p1 p2 a0 W1 W2 W3 RA) as EZC. unfold zc_win in EZC. injection EZC as X. unfold ZC_BASE, ZCB in *. lia.
Qed.

Lemma AR1 : aw_realW AI ACCT UNIV aw LBk m' mo' Wf.
Proof. exact (aw_real_abandon AI ACCT UNIV AI_fake aw LB m mo WW fb 1 AR VF (conj (Z.le_refl 1) ZC1)). Qed.

Lemma HOLDN3 : forall l1 l2 m1 m2 p1 p2 az,
  decode (map (den E') h3) = Some (w2Z md, den E A, p1 ++ Win (az - 1) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = l1 ++ WBf :: l2 -> l1 ++ l2 = m1 ++ WTf :: m2 ->
  m1 ++ m2 = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + 1 <= az < 2 ^ 47 + 2 ^ 46 -> (forall w, In w (p1 ++ p2) -> not_cr w) ->
  ~ In WBf (l1 ++ l2) -> ~ In WTf (m1 ++ m2) ->
  op_holds OPS HEAP_ID (map (den E') h3) m' mo'.
Proof.
  intros l1 l2 m1 m2 p1 p2 az D W1 W2 W3 RA NZL NB NT. rewrite OPS_holds1.
  pose proof (zc_ident l1 l2 m1 m2 p1 p2 az W1 W2 W3 RA) as EZC.
  assert (EA : az = ZC_BASE + w_zc WW) by (unfold zc_win in EZC; injection EZC as X; exact X).
  assert (EZC' : Win (az - 1) 0 K_STACK = zc_win (w_zc WW - 1)) by (unfold zc_win; f_equal; lia).
  assert (ZCBND : ZC_BASE + (w_zc WW - 1) < ZC_BAND) by (unfold ZC_BAND; lia).
  assert (IN1 : forall w, In w (l1 ++ l2) <-> In w (wins_of E nn rest) /\ w <> WBf).
  { intros w. rewrite W1. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NB H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (IN2 : forall w, In w (m1 ++ m2) <-> In w (l1 ++ l2) /\ w <> WTf).
  { intros w. rewrite W2. split.
    - intros H. split; [apply in_app_or in H as [H|H]; apply in_or_app; [left; exact H| right; right; exact H]| intros ->; exact (NT H)].
    - intros [H NE]. apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; exact H]. }
  assert (NZC : ~ In (zc_win (w_zc WW)) (p1 ++ p2)).
  { intros X. apply (NZL _ X). unfold zc_win. cbn [w_kind w_len w_lo]. split; [reflexivity|]. split; [reflexivity|]. unfold ZCB, ZC_BASE in *. lia. }
  assert (IN3 : forall w, In w (p1 ++ Win (az - 1) 0 K_STACK :: p2) <-> (In w (m1 ++ m2) /\ w <> zc_win (w_zc WW)) \/ w = zc_win (w_zc WW - 1)).
  { intros w. rewrite W3, EZC, EZC'. split.
    - intros H. apply in_app_or in H as [H|[H|H]].
      + left. split; [apply in_or_app; left; exact H| intros ->; apply NZC; apply in_or_app; left; exact H].
      + right. symmetry. exact H.
      + left. split; [apply in_or_app; right; right; exact H| intros ->; apply NZC; apply in_or_app; right; exact H].
    - intros [[H NE]| ->]; [| apply in_or_app; right; left; reflexivity].
      apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; right; exact H]. }
  exists (w2Z md), aw, (p1 ++ Win (az - 1) 0 K_STACK :: p2), (map (den E) (skipn (3 * nn) rest)), LBk, Wf.
  split; [rewrite AWden; exact D|]. split; [exact (proj1 AR1)|]. split; [| split].
  -
    apply Forall_forall. intros w Hw. apply IN3 in Hw as [[Hw NZ]| ->].
    2:{ pose proof atop_range as ATR. unfold zc_win, window_wf. cbn [w_lo w_len w_kind]. unfold ZC_BASE, ZCB, two64 in *.
        split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia]. }
    apply IN2 in Hw as [Hw NWT]. apply IN1 in Hw as [Hw NWB].
    pose proof (proj1 (Forall_forall _ _) WF w Hw) as (X1 & X2 & X3 & KD). split; [exact X1|]. split; [exact X2|]. split; [exact X3|].
    destruct (HeapCtrB.TwinB.wins_cover E nn rest wnl w NW Hw) as [KS|(k & len & kd & Ik & EW)].
    { left. destruct KD as [[_ C]|[[K _]|[K _]]]; [split; [exact KS| exact C]| rewrite KS in K; unfold K_BLOCK, K_STACK in K; lia| rewrite KS in K; unfold K_SUB, K_STACK in K; lia]. }
    assert (NKf : k <> kf).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ kf len kd lenf ActrB.TwinB.ActrB.K_FRAME AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLf)) as [-> ->].
      apply NWB. rewrite EW. unfold WBf. rewrite KF7. reflexivity. }
    assert (NKs : k <> sh).
    { intros ->. destruct (HeapCtrB.TwinB.windows_anchored_nodup _ _ sh len kd lent ActrB.TwinB.ActrB.K_FTWIN AN Ik (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WLt)) as [-> ->].
      apply NWT. rewrite EW. unfold WTf. rewrite ESH, ELT, KFT8. reflexivity. }
    destruct KD as [[K C]|[[K B]|[K (b & Hb & SUB)]]].
    + left. auto.
    + right; left. split; [exact K|]. apply LBk_In. split; [exact B|].
      apply (kept_block k len kd (w_iv w) Ik NKf NKs B). rewrite EW. unfold w_iv. cbn [w_lo w_len]. intros a0 Ha. exact Ha.
    + right; right. split; [exact K|]. exists b. split; [| exact SUB]. apply LBk_In. split; [exact Hb|].
      apply (kept_block k len kd b Ik NKf NKs Hb). rewrite EW in SUB. unfold w_iv in SUB. cbn [w_lo w_len] in SUB. exact SUB.
  -
    assert (INB : In WBf (wins_of E nn rest)) by (rewrite W1; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free_f K_FRAMEz _ _ _ _ m Af nf (l1 ++ l2) (or_introl eq_refl) HC INB IN1) as HC2.
    assert (INT : In WTf (l1 ++ l2)) by (rewrite W2; apply in_or_app; right; left; reflexivity).
    pose proof (Cw_ghost_free_f K_FTWINz _ _ _ _ m (shad Af) (shlen (ab_size fb)) (m1 ++ m2) (or_intror eq_refl) HC2 INT IN2) as HC3.
    pose proof (Cw_zc _ _ _ _ (p1 ++ Win (az - 1) 0 K_STACK :: p2) m (w_zc WW) (w_zc WW - 1) HC3 ZCBND IN3) as HC4.
    unfold LBk. rewrite UIV, SIV. exact HC4.
  -
    apply (ties_abandon AI ACCT UNIV AI_fake WW Wf aw LB m mo (wins_of E nn rest) (p1 ++ Win (az - 1) 0 K_STACK :: p2) fb 1 HWf TI eq_refl eq_refl ZC1 VF).
    + intros b. unfold visf, vis, Wf. cbn [w_LBa w_FA In]. split.
      * intros [[Hb NF] FK]. split; [split; [split; [exact Hb| intros X; apply NF; right; exact X]| exact FK]| intros ->; apply NF; left; reflexivity].
      * intros [[[Hb NF] FK] NE]. split; [split; [exact Hb| intros [X|X]; [apply NE; symmetry; exact X| exact (NF X)]]| exact FK].
    + intros w. rewrite IN3, IN2, IN1. unfold WBf, WTf. rewrite EAf, ENf. tauto.
    +
      intros b _ [Hb NF]. unfold Wf in Hb, NF. cbn [w_LBa w_FA In] in Hb, NF. split; [exact Hb| intros X; apply NF; right; exact X].
    + exact ZCBND.
    + exact (fun P => P).
Qed.

Variable R' : bvmap 5 word.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo'.
Hypothesis MINVo : op_minv OPS mo'.

Definition RgF : IMap.t region := CtrDelta.TwinB.RgPg (s_regs st) [] [kf; sh].
Definition NEWSETf (_ : Z) : Prop := False.

Lemma RgF_eq : RgF = IMap.remove sh (IMap.remove kf (s_regs st)).
Proof. reflexivity. Qed.

Lemma released_band : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a ->
  (a < 0x7fff7000 \/ 0x10007fff8000 <= a) \/ (0x800be200 <= a < shad ATOP).
Proof.
  intros a Ha. pose proof HWf as (AH & _).
  destruct (blk_facts AI AI_fake _ _ _ _ _ fb AH (proj1 (proj1 VF))) as (NP & BK & HI & _).
  destruct (shadow_tight (ab_addr fb) (ab_size fb) BK HI NP) as [T1 T2].
  assert (SL : shlen (ab_size fb) <= shlen (ab_size fb + 7)) by (unfold shlen; rewrite !Z.shiftr_div_pow2 by lia; apply Z.div_le_mono; lia).
  pose proof (usz_le fb) as UL.
  unfold ablk, AIMG_HI, KLS in BK. unfold in_iv, user_iv, fsh_iv in Ha. cbn [fst snd] in Ha.
  destruct Ha as [Ha|Ha]; [left| right]; lia.
Qed.

Lemma released_apart : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> ~ in_user LBk a.
Proof.
  intros a Ha U. apply in_ivs_In in U as (b' & Hb' & Hin). apply LBk_In in Hb' as (Hb' & N1 & N2).
  destruct Ha as [Ha|Ha].
  - destruct (Z.eq_dec (fst b') (fst (user_iv fb))) as [EQ|NE].
    + apply N1. destruct b' as [A' n']. rewrite UIV in *. cbn [fst] in EQ. subst A'. f_equal.
      exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo Af n' nf HWf Hb' INU).
    + exact (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo b' (user_iv fb) a AWHf Hb' INU NE Hin Ha).
  - destruct (Z.eq_dec (fst b') (fst (fsh_iv fb))) as [EQ|NE].
    + apply N2. destruct b' as [A' n']. rewrite SIV in *. cbn [fst] in EQ. subst A'. f_equal.
      exact (LB_same_addr AI ACCT UNIV AI_fake WW aw LB m mo (shad Af) n' (shlen (ab_size fb)) HWf Hb' INS).
    + exact (aw_blocks_disj_asan AI ACCT UNIV AI_fake aw LB m mo b' (fsh_iv fb) a AWHf Hb' INS NE Hin Ha).
Qed.

Lemma released_unbased : forall a, in_iv (user_iv fb) a \/ in_iv (fsh_iv fb) a -> ~ in_based E' RgF a.
Proof.
  intros a Ha (k0 & rg & Fk & KZ & RA). destruct (released_off_image a Ha) as [_ LOW].
  destruct (CtrDelta.TwinB.RgPg_range OPS E st ms mo HS FOK Fv Gv LB LBk ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf LOSP FLOOR
              (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl)
              hargs md A nw Hf Hc Eh Tnw Nn Ln [] [kf; sh]
              (NoDup_nil _) KEEP_delf NEWSETf ltac:(intros k1 r1 a1 X; destruct X) k0 rg a Fk KZ RA) as [[X _]|[_ [[_ X]|[_ [X|[X|X]]]]]].
  - destruct X.
  - lia.
  - fold sp in X. lia.
  - exact (released_apart a Ha X).
  - pose proof atop_range as ATR.
    assert (A47 : 0 <= ATOP < 2 ^ 47) by (clear - ATR; lia). pose proof (shad_band ATOP A47) as SHA.
    destruct (sh_cov_band a X) as [C|C]; destruct (released_band a Ha) as [B|B]; lia.
Qed.

Theorem fa_post_ok : forall (pc' : int) (rf' : FI.rf sv) (nx' : int),
  s_resv st = RNone ->
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  st_ok bsegs OPS E' (SS pc' rf' (s_ff st) RNone (IMap.remove sh (IMap.remove kf (s_regs st))) (s_facts st) (set_op HEAP_ID h3 (s_ops st)) (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None m' (seg_rom bsegs)) mo'.
Proof.
  intros pc' rf' nx' RVN X0Z REGS. rewrite <- RgF_eq.
  destruct DEL3 as (l1 & l2 & m1 & m2 & p1 & p2 & az & D & W1 & W2 & W3 & RA & NZL & NB & NT).
  pose proof (HOLDN3 l1 l2 m1 m2 p1 p2 az D W1 W2 W3 RA NZL NB NT) as HOLDN.
  set (ws3 := p1 ++ Win (az - 1) 0 K_STACK :: p2) in *.

  assert (WS3 : forall a0, in_ws ws3 a0 <-> in_ws (m1 ++ m2) a0).
  { intros a0. unfold in_ws, ws3. rewrite W3.
    split; intros X; apply in_ivs_In in X as (v & Hv & Hin); apply in_map_iff in Hv as (w & <- & Hw); apply in_ivs_In.
    - apply in_app_or in Hw as [Hw|[<-|Hw]].
      + exists (w_iv w). split; [apply in_map; apply in_or_app; left; exact Hw| exact Hin].
      + exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia.
      + exists (w_iv w). split; [apply in_map; apply in_or_app; right; right; exact Hw| exact Hin].
    - apply in_app_or in Hw as [Hw|[<-|Hw]].
      + exists (w_iv w). split; [apply in_map; apply in_or_app; left; exact Hw| exact Hin].
      + exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia.
      + exists (w_iv w). split; [apply in_map; apply in_or_app; right; right; exact Hw| exact Hin]. }
  assert (INWS : forall a0, in_ws (wins_of E nn rest) a0 -> in_ws ws3 a0 \/ in_iv (user_iv fb) a0 \/ in_iv (fsh_iv fb) a0).
  { intros a0 X. rewrite WS3. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    rewrite UIV, SIV.
    rewrite W1 in Hw. apply in_app_or in Hw as [Hw|[<-|Hw]]; [| right; left; exact Hin|].
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]).
    - assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [| right; right; exact Hin|];
        left; unfold in_ws; apply in_ivs_In; exists (w_iv w); (split; [apply in_map; apply in_or_app; auto| exact Hin]). }
  assert (RSNOK : region_ok bsegs (s_priv st) E' m' ks rss).
  { apply (CtrDelta.TwinB.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m' ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  apply (CtrDelta.TwinB.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv R' m' mo' aw LB LBk AWHf MINV' SBVf SBOf WBMf SBTf SBSf ks offs rss ksp SPR SPE wnl nn rest AJ WF KEEPf WINKf VKEEPf TKEEPf
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [kf; sh] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) KEEP_delf NEWSETf ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h3 (w2Z md) (den E A) ws3 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a0 X. destruct X.
  -   intros a0 Ha NIX NWS. destruct (GLib.UG.in_ws_dec (wins_of E nn rest) a0) as [IW|NIW]; [| left; exact NIW].
    right. destruct (INWS a0 IW) as [X|FR]; [contradiction|]. split; [exact (proj1 (released_off_image a0 FR))| exact (released_unbased a0 FR)].
  -   intros a0 IB X. pose proof (CtrDelta.TwinB.in_heap_ws _ _ X) as IW. destruct (INWS a0 IW) as [Y|FR]; [| exfalso; exact (released_unbased a0 FR IB)].
    unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [| exact KW].
    rewrite W1 in Hw. assert (NFR : forall w0, w0 = WBf \/ w0 = WTf -> in_iv (w_iv w0) a0 -> False).
    { intros w0 [-> | ->] Hw0; unfold WBf, WTf, w_iv in Hw0; cbn [w_lo w_len] in Hw0;
        [rewrite <- UIV in Hw0; exact (released_unbased a0 (or_introl Hw0) IB)| rewrite <- SIV in Hw0; exact (released_unbased a0 (or_intror Hw0) IB)]. }
    assert (KEPT3 : In w (m1 ++ m2) -> In w ws3).
    { intros X. unfold ws3. rewrite W3 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; left; exact X| | apply in_or_app; right; right; exact X].
      exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia. }
    apply KEPT3.
    apply in_app_or in Hw as [Hw|[<-|Hw]]; [| exfalso; exact (NFR WBf (or_introl eq_refl) Hin)|].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; left; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
    + assert (X : In w (l1 ++ l2)) by (apply in_or_app; right; exact Hw). rewrite W2 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; auto| exfalso; exact (NFR WTf (or_intror eq_refl) Hin)| apply in_or_app; auto].
  - exact X0Z.
  - exact REGS.
  - reflexivity.
  - exact (so_facts _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact MINVo.
Qed.
End RELEASED.
End Fa.
End TwinB.
