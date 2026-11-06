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

Section Burn.
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

Section BURNED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Let m : amem := ms_mem ms.

Lemma AWHb : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWb : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma WINKb : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a.
Proof.
  intros k0 len kd _ WL a Ha. pose proof (HeapCtrB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (HeapCtrB.nonstack_windows_In E nn rest wnl k0 len kd NW Hin) as (K0 & _ & KD & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
  - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.E' E st Fv Gv).
Variables (c : int) (h' : list sv).
Hypothesis HP : FaC.heap_pay (s_facts st) hargs c = Some h'.

Lemma DELB : exists p1 p2 az,
  decode (map (den E') h') = Some (w2Z md, den E A, p1 ++ Win (az - to_Z c) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = p1 ++ Win az 0 K_STACK :: p2 /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46 /\ (forall w, In w (p1 ++ p2) -> not_cr w).
Proof.
  rewrite Eh in HP.
  destruct (heap_pay_facts E (s_facts st) md A nw rest nn c h' wnl (so_facts _ _ _ _ _ _ HS) Tnw Nn Ln NW HP) as (ws3 & p1 & ac & p2 & lsv & EH3 & P1 & P2 & RA & NZL & L3 & SK3 & NW3 & INL & S3').
  exists p1, p2, ac. split; [| split; [exact P1| split; [exact RA| exact NZL]]].
  rewrite EH3. rewrite (decode_hargs E' md A _ _ nn Tnw Nn L3).
  assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.rest_below st FOK rest hargs md A nw Hf Eh).
  assert (RB3 : forallb (sv_vars_below (s_next st)) (ws3 ++ skipn (3 * nn) rest) = true).
  { apply forallb_forall. intros x Hx. destruct (S3' x Hx) as [X| ->]; [exact (proj1 (forallb_forall _ _) RB x X)|].
    apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact (proj1 (forallb_forall _ _) RB lsv INL)| reflexivity]. }
  rewrite (CtrDelta.den_E' E st Fv Gv A (CtrDelta.A_below st FOK rest hargs md A nw Hf Eh)).
  rewrite (CtrDelta.wins_of_E' E st Fv Gv _ _ RB3), P2, SK3.
  rewrite (CtrDelta.map_den_E' E st Fv Gv _ (CtrFree.forallb_skipn _ (3 * nn) rest RB)). reflexivity.
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.
Definition Wb : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (w_FA WW) (w_ms WW) (w_zc WW - to_Z c).

Lemma HOLDNB : forall p1 p2 az,
  decode (map (den E') h') = Some (w2Z md, den E A, p1 ++ Win (az - to_Z c) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46 -> (forall w, In w (p1 ++ p2) -> not_cr w) ->
  op_holds OPS HEAP_ID (map (den E') h') m mo.
Proof.
  intros p1 p2 az D W3 RA NZL. rewrite OPS_holds1.
  pose proof (to_Z_bounded c) as CB.
  assert (EZC : Win az 0 K_STACK = zc_win (w_zc WW)).
  { destruct TI as (_ & _ & _ & _ & _ & T6 & _).
    apply (T6 (Win az 0 K_STACK)); cbn [w_kind w_len w_lo]; [rewrite W3; apply in_or_app; right; left; reflexivity| reflexivity| reflexivity| unfold ZC_BAND; lia]. }
  assert (EA : az = ZC_BASE + w_zc WW) by (unfold zc_win in EZC; injection EZC as X; exact X).
  assert (EZC' : Win (az - to_Z c) 0 K_STACK = zc_win (w_zc WW - to_Z c)) by (unfold zc_win; f_equal; lia).
  assert (CZ : 0 <= to_Z c <= w_zc WW) by (unfold ZC_BASE, ZCB in *; lia).
  assert (ZCBND : ZC_BASE + (w_zc WW - to_Z c) < ZC_BAND) by (unfold ZC_BAND; lia).
  assert (NZC : ~ In (zc_win (w_zc WW)) (p1 ++ p2)).
  { intros X. apply (NZL _ X). unfold zc_win. cbn [w_kind w_len w_lo]. split; [reflexivity|]. split; [reflexivity|]. unfold ZCB, ZC_BASE in *. lia. }
  assert (IN3 : forall w, In w (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) <-> (In w (wins_of E nn rest) /\ w <> zc_win (w_zc WW)) \/ w = zc_win (w_zc WW - to_Z c)).
  { intros w. rewrite W3, EZC, EZC'. split.
    - intros H. apply in_app_or in H as [H|[H|H]].
      + left. split; [apply in_or_app; left; exact H| intros ->; apply NZC; apply in_or_app; left; exact H].
      + right. symmetry. exact H.
      + left. split; [apply in_or_app; right; right; exact H| intros ->; apply NZC; apply in_or_app; right; exact H].
    - intros [[H NE]| ->]; [| apply in_or_app; right; left; reflexivity].
      apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; right; exact H]. }
  exists (w2Z md), aw, (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2), (map (den E) (skipn (3 * nn) rest)), LB, Wb.
  split; [rewrite AWden; exact D|].
  split; [exact (proj1 (aw_real_burn AI ACCT UNIV aw LB m mo WW (to_Z c) AR CZ))|]. split; [| split].
  - apply Forall_forall. intros w Hw. apply IN3 in Hw as [[Hw NZ]| ->]; [exact (proj1 (Forall_forall _ _) WF w Hw)|].
    pose proof atop_range as ATR. unfold zc_win, window_wf. cbn [w_lo w_len w_kind]. unfold ZC_BASE, ZCB, two64 in *.
    split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia].
  - exact (Cw_zc _ _ _ _ (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) m (w_zc WW) (w_zc WW - to_Z c) HC ZCBND IN3).
  - apply (ties_burn WW Wb (wins_of E nn rest) (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) (to_Z c) TI eq_refl); [| reflexivity| lia| exact IN3| | exact ZCBND| exact (fun P => P)].
    + intros b. unfold visf, vis, Wb. cbn [w_LBa w_FA]. tauto.
    + intros b _ V. unfold vis, Wb in *. cbn [w_LBa w_FA] in *. exact V.
Qed.

Variable R' : bvmap 5 word.
Hypothesis MINV' : ALib.Mem.mem_inv asegs m.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo.
Hypothesis MINVo : op_minv OPS mo.

Theorem fa_burn_ok : forall (pc' : int) (rf' : FI.rf sv) (nx' : int),
  s_resv st = RNone ->
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  st_ok asegs OPS E' (SS pc' rf' (s_ff st) RNone (s_regs st) (s_facts st) (set_op HEAP_ID h' (s_ops st)) (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None m (seg_rom asegs)) mo.
Proof.
  intros pc' rf' nx' RVN X0Z REGS.
  destruct DELB as (p1 & p2 & az & D & W3 & RA & NZL).
  pose proof (HOLDNB p1 p2 az D W3 RA NZL) as HOLDN.
  set (ws3 := p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) in *.
  assert (KEPT3 : forall w a0, In w (wins_of E nn rest) -> in_iv (w_iv w) a0 -> In w ws3).
  { intros w a0 X Hin. unfold ws3. rewrite W3 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; left; exact X| | apply in_or_app; right; right; exact X].
    exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia. }
  assert (RSNOK : region_ok asegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  change (s_regs st) with (CtrDelta.RgPg (s_regs st) [] []) at 1.
  apply (CtrDelta.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv R' m mo aw LB LB AWHb MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINKb ltac:(intros; exact I) ltac:(intros; exact I)
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros; exact I) (fun _ : Z => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h' (w2Z md) (den E A) ws3 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a0 X. destruct X.
  -   intros a0 Ha NIX NWS. left. intros X. apply NWS. unfold in_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    apply in_ivs_In. exists (w_iv w). split; [apply in_map; exact (KEPT3 w a0 Hw Hin)| exact Hin].
  -   intros a0 IB X. unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact (KEPT3 w a0 Hw Hin)| exact KW].
  - exact X0Z.
  - exact REGS.
  - reflexivity.
  - exact (so_facts _ _ _ _ _ _ (CtrDelta.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact MINVo.
Qed.
End BURNED.
End Burn.

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

Section Burn.
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

Section BURNED.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Variables (wnl : list (int * sv * w64)) (nn : nat) (rest : list sv) (LB : blocks) (aw : word).
Hypothesis NW : CtrA.nonstack_windows nn rest = Some wnl.
Hypothesis WF : windows_wf (wins_of E nn rest) LB (ATOP + 4096).
Variable WW : wit.
Hypothesis AR : aw_realW AI ACCT UNIV aw LB (ms_mem ms) mo WW.
Hypothesis TI : ties WW (wins_of E nn rest).
Let m : amem := ms_mem ms.

Lemma AWHb : aw_holds_asan AI ACCT UNIV aw LB m mo.
Proof. exact (aw_real_holds AI ACCT UNIV _ _ _ _ _ AR). Qed.
Lemma HWb : aw_holds_w AI ACCT UNIV WW aw LB m mo.
Proof. exact (proj1 AR). Qed.

Lemma WINKb : forall k0 len kd, True -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LB a.
Proof.
  intros k0 len kd _ WL a Ha. pose proof (HeapCtrB.TwinB.win_lookup_In _ _ _ _ WL) as Hin.
  destruct (HeapCtrB.TwinB.nonstack_windows_In E nn rest wnl k0 len kd NW Hin) as (K0 & _ & KD & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (W1 & W2 & W3 & [[KS0 _]|[[KB B]|[KS2 (b & Hb & SUB)]]]); unfold w_iv in *; cbn [w_kind w_lo w_len] in *.
  - exfalso. exact (KD KS0).
  - apply in_ivs_In. eexists. split; [exact B|]. unfold in_iv. cbn [fst snd]. lia.
  - apply in_ivs_In. exists b. split; [exact Hb|]. apply SUB. unfold in_iv. cbn [fst snd]. lia.
Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : nn = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * nn <= length rest)%nat.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Notation E' := (CtrDelta.TwinB.E' E st Fv Gv).
Variables (c : int) (h' : list sv).
Hypothesis HP : FaC.TwinB.FaC.heap_pay (s_facts st) hargs c = Some h'.

Lemma DELB : exists p1 p2 az,
  decode (map (den E') h') = Some (w2Z md, den E A, p1 ++ Win (az - to_Z c) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest))
  /\ wins_of E nn rest = p1 ++ Win az 0 K_STACK :: p2 /\ ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46 /\ (forall w, In w (p1 ++ p2) -> not_cr w).
Proof.
  rewrite Eh in HP.
  destruct (heap_pay_facts E (s_facts st) md A nw rest nn c h' wnl (so_facts _ _ _ _ _ _ HS) Tnw Nn Ln NW HP) as (ws3 & p1 & ac & p2 & lsv & EH3 & P1 & P2 & RA & NZL & L3 & SK3 & NW3 & INL & S3').
  exists p1, p2, ac. split; [| split; [exact P1| split; [exact RA| exact NZL]]].
  rewrite EH3. rewrite (decode_hargs E' md A _ _ nn Tnw Nn L3).
  assert (RB : forallb (sv_vars_below (s_next st)) rest = true) by exact (CtrDelta.TwinB.rest_below st FOK rest hargs md A nw Hf Eh).
  assert (RB3 : forallb (sv_vars_below (s_next st)) (ws3 ++ skipn (3 * nn) rest) = true).
  { apply forallb_forall. intros x Hx. destruct (S3' x Hx) as [X| ->]; [exact (proj1 (forallb_forall _ _) RB x X)|].
    apply MemFX.MemFX.sv_vars_below_alu; [right; reflexivity| exact (proj1 (forallb_forall _ _) RB lsv INL)| reflexivity]. }
  rewrite (CtrDelta.TwinB.den_E' E st Fv Gv A (CtrDelta.TwinB.A_below st FOK rest hargs md A nw Hf Eh)).
  rewrite (CtrDelta.TwinB.wins_of_E' E st Fv Gv _ _ RB3), P2, SK3.
  rewrite (CtrDelta.TwinB.map_den_E' E st Fv Gv _ (CtrFree.TwinB.forallb_skipn _ (3 * nn) rest RB)). reflexivity.
Qed.

Hypothesis AWden : aw = den E A.
Hypothesis HC : cw_holds Cw (w2Z md) (map (den E) (skipn (3 * nn) rest)) LB (wins_of E nn rest) m.
Definition Wb : wit := mkWit (w_L WW) (w_RNG WW) (w_st WW) (w_LBa WW) (w_T WW) (w_FA WW) (w_ms WW) (w_zc WW - to_Z c).

Lemma HOLDNB : forall p1 p2 az,
  decode (map (den E') h') = Some (w2Z md, den E A, p1 ++ Win (az - to_Z c) 0 K_STACK :: p2, map (den E) (skipn (3 * nn) rest)) ->
  wins_of E nn rest = p1 ++ Win az 0 K_STACK :: p2 -> ZCB + to_Z c <= az < 2 ^ 47 + 2 ^ 46 -> (forall w, In w (p1 ++ p2) -> not_cr w) ->
  op_holds OPS HEAP_ID (map (den E') h') m mo.
Proof.
  intros p1 p2 az D W3 RA NZL. rewrite OPS_holds1.
  pose proof (to_Z_bounded c) as CB.
  assert (EZC : Win az 0 K_STACK = zc_win (w_zc WW)).
  { destruct TI as (_ & _ & _ & _ & _ & T6 & _).
    apply (T6 (Win az 0 K_STACK)); cbn [w_kind w_len w_lo]; [rewrite W3; apply in_or_app; right; left; reflexivity| reflexivity| reflexivity| unfold ZC_BAND; lia]. }
  assert (EA : az = ZC_BASE + w_zc WW) by (unfold zc_win in EZC; injection EZC as X; exact X).
  assert (EZC' : Win (az - to_Z c) 0 K_STACK = zc_win (w_zc WW - to_Z c)) by (unfold zc_win; f_equal; lia).
  assert (CZ : 0 <= to_Z c <= w_zc WW) by (unfold ZC_BASE, ZCB in *; lia).
  assert (ZCBND : ZC_BASE + (w_zc WW - to_Z c) < ZC_BAND) by (unfold ZC_BAND; lia).
  assert (NZC : ~ In (zc_win (w_zc WW)) (p1 ++ p2)).
  { intros X. apply (NZL _ X). unfold zc_win. cbn [w_kind w_len w_lo]. split; [reflexivity|]. split; [reflexivity|]. unfold ZCB, ZC_BASE in *. lia. }
  assert (IN3 : forall w, In w (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) <-> (In w (wins_of E nn rest) /\ w <> zc_win (w_zc WW)) \/ w = zc_win (w_zc WW - to_Z c)).
  { intros w. rewrite W3, EZC, EZC'. split.
    - intros H. apply in_app_or in H as [H|[H|H]].
      + left. split; [apply in_or_app; left; exact H| intros ->; apply NZC; apply in_or_app; left; exact H].
      + right. symmetry. exact H.
      + left. split; [apply in_or_app; right; right; exact H| intros ->; apply NZC; apply in_or_app; right; exact H].
    - intros [[H NE]| ->]; [| apply in_or_app; right; left; reflexivity].
      apply in_app_or in H as [H|[H|H]]; apply in_or_app; [left; exact H| congruence| right; right; exact H]. }
  exists (w2Z md), aw, (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2), (map (den E) (skipn (3 * nn) rest)), LB, Wb.
  split; [rewrite AWden; exact D|].
  split; [exact (proj1 (aw_real_burn AI ACCT UNIV aw LB m mo WW (to_Z c) AR CZ))|]. split; [| split].
  - apply Forall_forall. intros w Hw. apply IN3 in Hw as [[Hw NZ]| ->]; [exact (proj1 (Forall_forall _ _) WF w Hw)|].
    pose proof atop_range as ATR. unfold zc_win, window_wf. cbn [w_lo w_len w_kind]. unfold ZC_BASE, ZCB, two64 in *.
    split; [lia|]. split; [lia|]. split; [lia|]. left. split; [reflexivity| lia].
  - exact (Cw_zc _ _ _ _ (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) m (w_zc WW) (w_zc WW - to_Z c) HC ZCBND IN3).
  - apply (ties_burn WW Wb (wins_of E nn rest) (p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) (to_Z c) TI eq_refl); [| reflexivity| lia| exact IN3| | exact ZCBND| exact (fun P => P)].
    + intros b. unfold visf, vis, Wb. cbn [w_LBa w_FA]. tauto.
    + intros b _ V. unfold vis, Wb in *. cbn [w_LBa w_FA] in *. exact V.
Qed.

Variable R' : bvmap 5 word.
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m.
Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis OTH : OTHER mo mo.
Hypothesis MINVo : op_minv OPS mo.

Theorem fa_burn_ok : forall (pc' : int) (rf' : FI.rf sv) (nx' : int),
  s_resv st = RNone ->
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None) (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  st_ok bsegs OPS E' (SS pc' rf' (s_ff st) RNone (s_regs st) (s_facts st) (set_op HEAP_ID h' (s_ops st)) (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) None m (seg_rom bsegs)) mo.
Proof.
  intros pc' rf' nx' RVN X0Z REGS.
  destruct DELB as (p1 & p2 & az & D & W3 & RA & NZL).
  pose proof (HOLDNB p1 p2 az D W3 RA NZL) as HOLDN.
  set (ws3 := p1 ++ Win (az - to_Z c) 0 K_STACK :: p2) in *.
  assert (KEPT3 : forall w a0, In w (wins_of E nn rest) -> in_iv (w_iv w) a0 -> In w ws3).
  { intros w a0 X Hin. unfold ws3. rewrite W3 in X. apply in_app_or in X as [X|[<-|X]]; [apply in_or_app; left; exact X| | apply in_or_app; right; right; exact X].
    exfalso. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. lia. }
  assert (RSNOK : region_ok bsegs (s_priv st) E' m ks rss).
  { apply (CtrDelta.TwinB.sp_region_same_ok OPS E st ms mo HS FOK Fv Gv m ks offs rss SPR). intros a0 Ha RA0. split; [reflexivity| exact (fun H => H)]. }
  change (s_regs st) with (CtrDelta.TwinB.RgPg (s_regs st) [] []) at 1.
  apply (CtrDelta.TwinB.delta_st_ok AI IMGX IMGX_aci ACCT UNIV OPS AI_fake OPS_fp1 OPS_cov1 OPS_frame_other OPS_fp_other OTHER OPS_mo_other OPS_cov0_img
           E st ms mo HS FOK Fv Gv R' m mo aw LB LB AWHb MINV'
           ltac:(intros a0 Ha S; split; [reflexivity| exact (fun H => H)]) ltac:(intros; reflexivity) ltac:(intros a0 Ha CC H; exact H)
           ltac:(intros a0 Ha SC IB; split; [reflexivity| exact (fun H => H)])
           ltac:(intros a0 Ha; split; [reflexivity| exact (fun H => H)])
           ks offs rss ksp SPR SPE wnl nn rest AJ WF (fun _ => True) WINKb ltac:(intros; exact I) ltac:(intros; exact I)
           LOSP FLOOR (s_regs st) rss (so_bst _ _ _ _ _ _ HS) (CtrDelta.TwinB.inline_RB_find st ks offs rss SPR) eq_refl (fun _ => eq_refl) eq_refl RSNOK
           hargs md A nw Hf Hc Eh Tnw Nn Ln OTH [] [] (NoDup_nil _)
           ltac:(intros k1 r1 X; destruct X) ltac:(intros; exact I) (fun _ : Z => False) ltac:(intros k1 r1 X; destruct X) ltac:(intros k1 r1 a1 X; destruct X)
           ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros a1 X; destruct X) ltac:(intros k1 r1 k2 r2 a1 X; destruct X)
           h' (w2Z md) (den E A) ws3 (map (den E) (skipn (3 * nn) rest)) D HOLDN).
  - intros a0 X. destruct X.
  -   intros a0 Ha NIX NWS. left. intros X. apply NWS. unfold in_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
    apply in_ivs_In. exists (w_iv w). split; [apply in_map; exact (KEPT3 w a0 Hw Hin)| exact Hin].
  -   intros a0 IB X. unfold in_ws, heap_ws in X |- *. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw). apply filter_In in Hw as [Hw KW].
    apply in_ivs_In. exists (w_iv w). split; [| exact Hin]. apply in_map. apply filter_In. split; [exact (KEPT3 w a0 Hw Hin)| exact KW].
  - exact X0Z.
  - exact REGS.
  - reflexivity.
  - exact (so_facts _ _ _ _ _ _ (CtrDelta.TwinB.HS' OPS E st ms mo HS FOK Fv Gv)).
  - exact MINVo.
Qed.
End BURNED.
End Burn.
End TwinB.
