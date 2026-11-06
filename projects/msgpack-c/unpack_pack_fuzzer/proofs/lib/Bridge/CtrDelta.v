(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require Import PropExec MState Cells Frame ITree Nodes.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib Require ALib.Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require Import AcctCore ExecF ITreeA NodesA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require Import STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require Import AImg AProto AMalloc_iface AMalloc_iface2.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import RunDraw ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Instr State Step Plan PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Ledger Op Adeq.
Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64Proofs ValProofs MemProofs StepSoundBase.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require HeapCtr HeapCtrB.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require CallA CallV CtrPre GlueA FrameV.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require GLib.
Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Delta.
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
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->

  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb asegs m a = true -> wb asegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.

Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment asegs a 1 = Some seg) -> op_cov0 OPS a.

Hypothesis OPS_cov0_stk : forall a, ATOP <= a < 2 ^ 47 -> op_cov0 OPS a.

Hypothesis IMGX_img : forall a, in_ivs IMGX a -> exists seg, find_segment asegs a 1 = Some seg.

Section DELTA.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok asegs OPS E st ms mo.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply HeapCtr.fresh_ok_inv. exact FOK. Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : st_ok asegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval asegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).

Variables (aw : word) (LB LBk : blocks).
Hypothesis AWH : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Hypothesis LBk_sub : forall v, In v LBk -> In v LB.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis MINV' : ALib.Mem.mem_inv asegs m'.
Definition stableA (a : Z) : Prop := (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a.

Hypothesis SBV : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Hypothesis SBO : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Hypothesis WBM : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb asegs (ms_mem ms) a = true -> wb asegs m' a = true.

Hypothesis SBT : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).

Hypothesis SBS : forall a, ATOP + 4096 <= a < sp ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).

Lemma stable_byte : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true).
Proof. exact SBV. Qed.

Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Variables (wnl : list (int * sv * w64)) (n : nat) (rest : list sv).
Hypothesis NW : CtrA.nonstack_windows n rest = Some wnl.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis WF : windows_wf (wins_of E n rest) LB (ATOP + 4096).

Variable KEEP : int -> Prop.

Hypothesis WINKW : forall k0 len kd, KEEP k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Hypothesis VKEEP : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEP k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEP sh'.

Hypothesis TKEEP : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEP k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEP sh'.

Lemma SP_den : bv_unsigned (den E (getr st X2)) = sp.
Proof. unfold sp. rewrite <- HeapCtr.reg_of_X2, (GlueA.getr_RA asegs OPS E st ms mo HS X2). reflexivity. Qed.

Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.

Lemma sp_region_same_ok :
  (forall a, 0 <= a < two64 -> bv_unsigned (ev E ks) + loZ rss <= a < bv_unsigned (ev E ks) + hiZ E rss ->
     rb asegs m' a = rb asegs (ms_mem ms) a /\ (wb asegs (ms_mem ms) a = true -> wb asegs m' a = true)) ->
  region_ok asegs (s_priv st) E' m' ks rss.
Proof.
  intros SAME. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & KZ & _).
  pose proof (so_reg _ _ _ _ _ _ HS' ks rss Hrs) as RO. destruct (reg_E' ks rss Hrs) as (Ek & Eh0 & _).
  apply (FrameV.region_ok_frame_v asegs (s_priv st) E' (ms_mem ms) m' ks rss (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh0 in R. exact (SAME a Ha (R KZ)).
Qed.

Variables (RB : IMap.t region) (rs_new : region).
Hypothesis RB_bst : IMap.bst RB.
Hypothesis RB_find : forall k0 rg, IMap.find k0 RB = Some rg -> (k0 = ks /\ rg = rs_new) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Hypothesis RSN_lo : loZ rs_new = loZ rss.
Hypothesis RSN_hi : forall E0, hiZ E0 rs_new = hiZ E0 rss.
Hypothesis RSN_w : rg_w rs_new = rg_w rss.
Hypothesis RSN_ok : region_ok asegs (s_priv st) E' m' ks rs_new.

Lemma rs_top : bv_unsigned (ev E ks) + hiZ E rss <= 2 ^ 47.
Proof.
  destruct (CallA.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  assert (K0 : ks <> 0%uint63) by (apply Uint63.eqb_false_spec; exact KZ).
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss ks rss HS SPR AJ Hrs K0) as [[_ TOP]|[NE _]]; [exact TOP| contradiction].
Qed.

Lemma sp_floor : ATOP + 4096 <= sp.
Proof. rewrite SPE. lia. Qed.
Lemma ks_nz : ks <> 0%uint63.
Proof. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & _ & KZ & _). apply Uint63.eqb_false_spec. exact KZ. Qed.
Lemma old_key_lt : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> to_Z k0 < to_Z (s_next st).
Proof. intros k0 rg H. destruct (reg_E' k0 rg H) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. exact LT. Qed.

Lemma fresh_Z : forall i, (i <= 200)%nat -> to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i.
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma fresh_nz : forall i, (i <= 200)%nat -> PrimInt63.eqb (addn (s_next st) i) 0%uint63 = false.
Proof.
  intros i Hi. apply Uint63.eqb_false_spec. intros X. pose proof (fresh_Z i Hi) as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ.
  destruct NX as (_ & P & _). lia.
Qed.
Lemma fresh_not_old : forall i k0 rg, (i <= 200)%nat -> IMap.find k0 (s_regs st) = Some rg -> addn (s_next st) i <> k0.
Proof. intros i k0 rg Hi F X. pose proof (fresh_Z i Hi). pose proof (old_key_lt k0 rg F). rewrite X in *. lia. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : n = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * n <= length rest)%nat.

Lemma DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite Eh. exact (decode_hargs E md A nw rest n Tnw Nn Ln). Qed.

Lemma wlo_floor : forall wlo, stack_wlo st = Some wlo -> ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros wlo H. unfold stack_wlo in H. rewrite Hf in H.
  assert (HN : heap_nwin hargs = Some n).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw. rewrite <- Nn. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. rewrite Eh in H. destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate]. injection H as <-.
  destruct (CallA.stack_window_key_In E n rest w SK) as (len & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[_ C]|[[K _]|[K _]]]); cbn [w_kind w_lo] in *; [exact C| |]; unfold K_STACK, K_BLOCK, K_SUB in K; lia.
Qed.

Lemma shz_shad : forall a', 0 <= a' -> CallV.shz a' = shad a'.
Proof. intros a' H. unfold CallV.shz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Notation is_sliver k0 rg := (sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg).
Lemma old_stable : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> KEEP k0 -> is_sliver k0 rg = false ->
  forall a, bv_unsigned (ev E k0) + loZ rg <= a < bv_unsigned (ev E k0) + hiZ E rg -> (sp <= a < 2 ^ 47) \/ in_user LBk a \/ sh_cov a.
Proof.
  intros k0 rg Hk K0 KS KP NSL a Ha. pose proof atop_range as ATR.
  destruct (CallA.aregion_just_sound asegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR AJ Hk K0) as [[EQK _]|(_ & [(len & kd & WL & LZ & HZ)|[(ABOVE & TOP)|[VJ|SL]]])];
    [| | | | congruence].
  - contradiction.
  - right. left. rewrite LZ in Ha. apply (WINKW k0 len kd KP WL). lia.
  - left. rewrite SP_den in ABOVE. lia.
  - destruct (CallV.view_just_sound asegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR Hk K0 VJ) as [(_ & blo & bhi & SHA & TOP & FLR)|[(hs0 & n0 & sh' & len & ZV & BT & VPAR & WL & LO & HI)|[(_ & v & Hv & LO & HI)|(sh' & kbt & nt & len & WL & BTt & WLk & STt & TNt & _ & LO & HI)]]].
    + right. right. left. destruct (SHA a Ha) as (a' & Ha' & ->). exists a'.
      assert (FL : ATOP + 4096 <= blo).
      { destruct FLR as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
        - exact (wlo_floor wlo SW).
        - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. exact FLOOR.
        - rewrite SP_den in GE. pose proof sp_floor. lia. }
      split; [lia| apply shz_shad; lia].
    + right. left. apply (WINKW sh' len K_TWIN (VKEEP k0 rg hs0 n0 sh' len Hk ZV KP BT VPAR WL) WL). lia.
    + right. right. right. exists v. split; [exact (IMGSH_SHLIT v Hv)| lia].
    + right. left. apply (WINKW sh' len K_TWIN (TKEEP k0 rg sh' kbt nt len Hk KP WL BTt WLk STt TNt) WL). lia.
Qed.

Lemma old_region_ok : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> KEEP k0 ->
  region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg Hk K0 KS KP. pose proof (so_reg _ _ _ _ _ _ HS' k0 rg Hk) as RO. destruct (reg_E' k0 rg Hk) as (Ek & Eh0 & _).
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  apply (FrameV.region_ok_frame_v asegs (s_priv st) E' (ms_mem ms) m' k0 rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh0 in R.
  destruct (is_sliver k0 rg) eqn:SL.
  {
    destruct (CtrPre.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR Hk K0 KS SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
    pose proof (wlo_floor wlo SW) as CE. specialize (R KZ). rewrite L0 in R. apply SBS. rewrite SPE. lia. }
  destruct (old_stable k0 rg Hk K0 KS KP SL a (R KZ)) as [X|[X|X]].
  - exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(left; exact X)).
  - exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact X)).
  - apply (SBT a ltac:(unfold two64 in Ha; lia) X). exists k0, rg. split; [exact Hk|]. split; [exact KZ| exact (R KZ)].
Qed.

Lemma win_off_image : forall a, in_ws (wins_of E n rest) a -> find_segment asegs a 1 = None.
Proof.
  intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
  - apply ref_find_segment_none; [lia|]. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWH B Hin)).
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo b a AWH Hb (SUBb a Hin))).
Qed.

Lemma pub_image_client : forall a seg, 0 <= a < two64 -> find_segment asegs a 1 = Some seg -> ~ in_priv (s_priv st) a -> in_ranges (aci AI) a.
Proof.
  intros a seg Ha SEG NP.
  destruct (in_ivs_b IMGX a) eqn:IX.
  - apply in_ivs_b_spec in IX. apply in_ivs_In in IX as (v & Hv & Hin). unfold in_iv in Hin.
    destruct (IMGX_aci v Hv) as (N0 & [(rg & Hr & R1 & R2)|[(rg & Hr & R1 & R2)|(S1 & S2)]]).
    + exists rg. split; [exact Hr|]. lia.
    +   exfalso. pose proof (AI_aci_lo AI rg Hr) as LO.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
    + exfalso. pose proof atop_range as ATR0.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
  - exfalso. assert (NIX : ~ in_ivs IMGX a) by (rewrite <- in_ivs_b_spec; congruence).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; rewrite (win_off_image a X) in SEG; discriminate).
    destruct (ops_apart_find asegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf) as [_ IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC)). auto. }
    apply NP. apply IP. exists seg. exact SEG.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> region_ok asegs (s_priv st) E' m' 0%uint63 r0.
Proof.
  intros r0 H0. pose proof (so_reg _ _ _ _ _ _ HS' _ _ H0) as RO.
  apply (FrameV.region_ok_frame_v asegs (s_priv st) E' (ms_mem ms) m' _ r0 (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha _ R. destruct (R eq_refl) as [[seg SEG] NP].
  exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact (pub_image_client a seg Ha SEG NP))).
Qed.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. exact X.
Qed.
Lemma A_below : sv_vars_below (s_next st) A = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X.
Qed.
Lemma hargs_below : forallb (sv_vars_below (s_next st)) hargs = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). exact (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)).
Qed.
Lemma reg_below : forall x, sv_vars_below (s_next st) (getr st x) = true.
Proof. intros x. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x). Qed.

Lemma wins_of_E' : forall m0 l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m0 l = wins_of E m0 l.
Proof.
  induction m0 as [|m0 IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.
Lemma map_den_E' : forall l, forallb (sv_vars_below (s_next st)) l = true -> map (den E') l = map (den E) l.
Proof.
  induction l as [|x l IH]; intros AV; [reflexivity|]. cbn [forallb] in AV. apply andb_prop in AV as [A1 AV].
  cbn [map]. rewrite (den_E' x A1), (IH AV). reflexivity.
Qed.
Lemma DEC' : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite (map_den_E' hargs hargs_below). exact DEC. Qed.

Hypothesis OTH : OTHER mo mo'.
Lemma other_ops_ok : forall o, In o (s_ops st) -> not_id HEAP_ID o ->
  op_holds OPS (op_id o) (map (den E') (op_args o)) (ms_mem ms) mo -> op_holds OPS (op_id o) (map (den E') (op_args o)) m' mo'.
Proof.
  intros o Ho NI H. pose proof NI as NI0. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H).
  - intros a Ha FP. symmetry. exact (SBO o a Ho NI0 Ha FP).
  - exact WBM.
Qed.
Lemma aci_low : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & R). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma minv' : forall a b, m' a = Some b -> forall seg, find_segment asegs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b H seg Hs. pose proof (MINV' a b H) as X. unfold ALib.Mem.ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Variables (newR : list (int * region)) (delK : list int).
Hypothesis NEW_nodup : List.NoDup (map fst newR).

Hypothesis NEW_nz : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false.
Hypothesis DEL_ks : ~ In ks delK.
Hypothesis DEL_0 : ~ In 0%uint63 delK.
Hypothesis KEEP_del : forall k0, ~ In k0 delK -> KEEP k0.
Variable NEWSET : Z -> Prop.
Hypothesis NEW_ok : forall k rg, In (k, rg) newR -> region_ok asegs (s_priv st) E' m' k rg.
Hypothesis NEW_range : forall k rg a, In (k, rg) newR ->
  bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSET a.
Hypothesis NEW_low : forall a, NEWSET a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Hypothesis NEW_nosh : forall a, NEWSET a -> ~ (0x7fff8000 <= a < 0x800bde00).
Hypothesis NEW_nostk : forall a, NEWSET a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Lemma NEW_nocov : forall a, NEWSET a -> ~ sh_cov a.
Proof.
  intros a Ha [X|(v & Hv & R)]; [exact (NEW_nostk a Ha X)|]. apply (NEW_nosh a Ha).
  destruct (SHLIT_cases v Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in R|]; lia.
Qed.
Hypothesis NEW_disj : forall k1 r1 k2 r2 a, In (k1, r1) newR -> In (k2, r2) newR -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\
     bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).

Definition RgPg : IMap.t region := GLib.UG.add_regions newR (GLib.UG.remove_keys delK RB).

Lemma RgPg_bst : IMap.bst RgPg.
Proof. unfold RgPg. apply GLib.UG.add_regions_bst. apply GLib.UG.remove_keys_bst. exact RB_bst. Qed.

Lemma RgPg_find : forall k0 rg, IMap.find k0 RgPg = Some rg ->
  In (k0, rg) newR
  \/ (~ In k0 (map fst newR) /\ ~ In k0 delK /\ ((k0 = ks /\ rg = rs_new) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg))).
Proof.
  intros k0 rg H. unfold RgPg in H.
  apply (GLib.UG.find_add_regions newR _ k0 rg (GLib.UG.remove_keys_bst _ _ RB_bst) NEW_nodup) in H as [H|[NN H]]; [left; exact H|].
  apply (GLib.UG.find_remove_keys delK _ k0 rg RB_bst) in H as [ND H]. right. split; [exact NN|]. split; [exact ND|]. exact (RB_find k0 rg H).
Qed.

Lemma new_nz : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false.
Proof. exact NEW_nz. Qed.

Lemma RgPg_range : forall k0 rg a, IMap.find k0 RgPg = Some rg -> PrimInt63.eqb k0 0%uint63 = false ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg ->
  (In (k0, rg) newR /\ NEWSET a)
  \/ (~ In k0 (map fst newR) /\ ((k0 = ks /\ ATOP + 4096 <= a < 2 ^ 47) \/ (k0 <> ks /\ ((ATOP + 4096 <= a < 2 ^ 47) \/ in_user LBk a \/ sh_cov a)))).

Proof.
  intros k0 rg a H KZ Ha. destruct (RgPg_find k0 rg H) as [IN|(NN & ND & [[-> ->]|[NK F]])].
  - left. split; [exact IN| exact (NEW_range k0 rg a IN Ha)].
  - right. split; [exact NN|]. left. split; [reflexivity|]. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct (reg_E' ks rss Hrs) as (Ek & Ehh & _). rewrite RSN_lo, (RSN_hi E') in Ha.
    rewrite Ek, Ehh in Ha. pose proof rs_top. lia.
  - right. split; [exact NN|]. right. split; [exact NK|]. destruct (reg_E' k0 rg F) as (Ek & Ehh & _). rewrite Ek, Ehh in Ha.
    assert (K0' : k0 <> 0%uint63) by (intros ->; discriminate KZ).
    destruct (is_sliver k0 rg) eqn:SL.
    + left. destruct (CtrPre.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR F K0' NK SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
      pose proof (wlo_floor wlo SW) as CE. pose proof rs_top as RT. pose proof (CallA.sliver_neg st ks offs rss k0 rg SPR SL) as NEG.
      pose proof (bv_unsigned_in_range 64 (den E (rg_hi rss))) as RH. fold (hiZ E rss) in RH. rewrite L0 in Ha. lia.
    + destruct (old_stable k0 rg F K0' NK (KEEP_del k0 ND) SL a Ha) as [X|[X|X]]; [left; pose proof sp_floor; lia| right; left; exact X| right; right; exact X].
Qed.

Lemma RgPg_old : forall k0 rg, IMap.find k0 RgPg = Some rg -> ~ In k0 (map fst newR) ->
  exists rg0, IMap.find k0 (s_regs st) = Some rg0 /\ loZ rg = loZ rg0 /\ (forall E0, hiZ E0 rg = hiZ E0 rg0) /\ rg_w rg = rg_w rg0.
Proof.
  intros k0 rg H NN. destruct (RgPg_find k0 rg H) as [IN|(_ & _ & [[-> ->]|[_ F]])].
  - exfalso. apply NN. apply in_map_iff. exists (k0, rg). auto.
  - destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). exists rss. split; [exact Hrs|]. split; [exact RSN_lo|]. split; [exact RSN_hi| exact RSN_w].
  - exists rg. auto.
Qed.

Lemma RgPg_disjoint : regions_disjoint E' RgPg.
Proof.
  intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2]. pose proof sp_floor as SPF.
  pose proof (RgPg_range k1 rg1 a H1 Z1 A1) as C1. pose proof (RgPg_range k2 rg2 a H2 Z2 A2) as C2.
  destruct C1 as [[I1 S1]|[NN1 C1]]; destruct C2 as [[I2 S2]|[NN2 C2]].
  - exact (NEW_disj k1 rg1 k2 rg2 a I1 I2 NE WR (conj A1 A2)).
  - destruct (NEW_low a S1) as [LOWa NU]. destruct C2 as [[_ X]|(_ & [X|[X|X]])]; [lia| lia| exact (NU X)| exact (NEW_nocov a S1 X)].
  - destruct (NEW_low a S2) as [LOWa NU]. destruct C1 as [[_ X]|(_ & [X|[X|X]])]; [lia| lia| exact (NU X)| exact (NEW_nocov a S2 X)].
  - destruct (RgPg_old k1 rg1 H1 NN1) as (q1 & F1 & L1 & HH1 & W1). destruct (RgPg_old k2 rg2 H2 NN2) as (q2 & F2 & L2 & HH2 & W2).
    rewrite L1, (HH1 E') in A1. rewrite L2, (HH2 E') in A2. rewrite W1, W2 in WR.
    exact (so_disj _ _ _ _ _ _ HS' k1 q1 k2 q2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
Qed.

Lemma RgPg_in_based : forall a, in_based E' RgPg a -> NEWSET a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R). destruct (RgPg_find k0 rg H) as [IN|(NN & _)]; [left; exact (NEW_range k0 rg a IN R)|].
  destruct (RgPg_old k0 rg H NN) as (q & F & L1 & HH1 & _). right. exists k0, q. rewrite <- L1, <- (HH1 E'). auto.
Qed.

Lemma RgPg_regions_ok : forall k0 rg, IMap.find k0 RgPg = Some rg -> region_ok asegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg H. destruct (RgPg_find k0 rg H) as [IN|(NN & ND & [[-> ->]|[NK F]])].
  - exact (NEW_ok k0 rg IN).
  - exact RSN_ok.
  - destruct (Uint63.eqb k0 0%uint63) eqn:Q0.
    + apply Uint63.eqb_correct in Q0. subst k0. exact (r0_ok rg F).
    + apply Uint63.eqb_false_spec in Q0. exact (old_region_ok k0 rg F Q0 NK (KEEP_del k0 ND)).
Qed.

Lemma RgPg_pub : abs_cells_public (s_priv st) RgPg.
Proof.
  intros r0 g gr c H0 Hg Hcc i Hi.
  destruct (RgPg_find _ _ H0) as [IN|(_ & _ & [[X _]|[_ F]])].
  - exfalso. pose proof (new_nz _ _ IN) as X. discriminate X.
  - exfalso. exact (ks_nz (eq_sym X)).
  - exact (so_pub _ _ _ _ _ _ HS r0 g gr c F Hg Hcc i Hi).
Qed.

Variables (h' : list sv) (md' : Z) (aw' : word) (ws' : list window) (ca' : list word).
Hypothesis DECN : decode (map (den E') h') = Some (md', aw', ws', ca').
Hypothesis HOLDN : op_holds OPS HEAP_ID (map (den E') h') m' mo'.
Hypothesis W1 : forall a, NEWSET a -> in_ws (heap_ws ws') a.
Hypothesis W3 : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws' a ->
  ~ in_ws (wins_of E n rest) a \/ (find_segment asegs a 1 = None /\ ~ in_based E' RgPg a).
Hypothesis W4 : forall a, in_based E' RgPg a -> in_ws (heap_ws (wins_of E n rest)) a -> in_ws (heap_ws ws') a.

Definition opsg : list opinst := set_op HEAP_ID h' (s_ops st).

Lemma OPS_HOLD_g : ops_hold OPS E' opsg m' mo'.
Proof.
  apply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs h' (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ HS')); [| exact HOLDN].
  exact other_ops_ok.
Qed.

Lemma in_heap_ws : forall ws a, in_ws (heap_ws ws) a -> in_ws ws a.
Proof.
  intros ws a X. unfold in_ws, heap_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
  apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply filter_In in Hw as [Hw _]. exact Hw.
Qed.

Lemma APART_g : ops_apart asegs OPS E' opsg RgPg (s_priv st).
Proof.
  apply (ops_apart_set_op asegs OPS E' E' (s_ops st) HEAP_ID hargs h' (s_regs st) RgPg (s_priv st) Hf Hc (so_apart _ _ _ _ _ _ HS')).
  - intros o a Ho NI OLD FP. destruct (OLD FP) as [NB IP]. split; [| exact IP].
    intros IB. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (RgPg_in_based a IB) as [I|I]; [| exact (NB I)].
    destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
    + pose proof (aci_low a R) as LOW. destruct (NEW_low a I) as [X _]. lia.
    + apply (NEW_nosh _ I). apply CtrPre.shad_img_band. split; [destruct R as (iv0 & Hi & R); pose proof (AI_aci_lo AI iv0 Hi); lia| exact (aci_low a' R)].
    + exact (NEW_nostk _ I (ex_intro _ a' (conj R eq_refl))).
  - intros a FP. rewrite OPS_fp1 in FP. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DECN)) in FP as (Ha & NIX & NWS).
    destruct (W3 a Ha NIX NWS) as [NW0|[SEG NB]].
    + destruct (ops_apart_find asegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS') Hf) as [NB IP].
      { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC')). auto. }
      split; [| exact IP]. intros IB. destruct (RgPg_in_based a IB) as [I|I]; [| exact (NB I)].
      apply NWS. apply in_heap_ws. exact (W1 a I).
    + split; [exact NB|]. intros [seg X]. rewrite SEG in X. discriminate X.
Qed.

Lemma opsg_cases : In (OpI HEAP_ID h') opsg /\ forall o, In o (s_ops st) -> o = OpI HEAP_ID hargs \/ In o opsg.
Proof.
  destruct (find_op_unique HEAP_ID (s_ops st) hargs Hf Hc) as (l1 & l2 & E0 & F1 & F2). unfold opsg. rewrite E0, (set_op_split HEAP_ID h' l1 l2 hargs F1).
  split; [apply in_app_iff; right; left; reflexivity|].
  intros o Ho. apply in_app_iff in Ho as [Ho|[Ho|Ho]]; [right; apply in_app_iff; left; exact Ho| left; symmetry; exact Ho| right; apply in_app_iff; right; right; exact Ho].
Qed.

Lemma COVER_g : forall a, fx_acc asegs E' RgPg a -> op_cov OPS (insts E' opsg) a.
Proof.
  intros a [IB|IMG]; [| left; exact (OPS_cov0_img a IMG)].
  destruct opsg_cases as [INH OTHERS].
  assert (NEWCOV : in_ws (heap_ws ws') a \/ sh_cov a -> op_cov OPS (insts E' opsg) a).
  { intros X. right. apply Exists_exists. exists (HEAP_ID, map (den E') h'). split.
    - unfold insts. apply in_map_iff. exists (OpI HEAP_ID h'). split; [reflexivity| exact INH].
    - cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _. split; [exact DECN| exact X]. }
  destruct (RgPg_in_based a IB) as [I|I]; [exact (NEWCOV (or_introl (W1 a I)))|].
  destruct (so_cover _ _ _ _ _ _ HS' a (or_introl I)) as [C0|C1]; [left; exact C0|].
  apply Exists_exists in C1 as (oi & Hoi & CV). unfold insts in Hoi. apply in_map_iff in Hoi as (o & <- & Ho). cbn [fst snd] in CV.
  destruct (OTHERS o Ho) as [->|INo].
  - cbn [op_id op_args] in CV. apply OPS_cov1 in CV as (_ & md0 & aw0 & ws0 & ca0 & D0 & X). rewrite DEC' in D0. injection D0 as <- <- <- <-.
    destruct X as [X|X]; [exact (NEWCOV (or_introl (W4 a IB X)))| exact (NEWCOV (or_intror X))].
  - right. apply Exists_exists. exists (op_id o, map (den E') (op_args o)). split; [| exact CV].
    unfold insts. apply in_map_iff. exists o. split; [reflexivity| exact INo].
Qed.

Theorem delta_st_ok : forall (pc' : int) (rf' : rf sv) (resv' : sresv) (rv' : option word) (facts' : list fact) (nx' : int),
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) rv') (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  resv_ok E' resv' rv' ->
  facts_hold E' facts' -> op_minv OPS mo' ->
  st_ok asegs OPS E' (SS pc' rf' (s_ff st) resv' RgPg facts' opsg (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) rv' m' (seg_rom asegs)) mo'.
Proof.
  intros pc' rf' resv' rv' facts' nx' X0Z REGS RESV HFACTS MINVo.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending MS].
  - reflexivity.
  - exact X0Z.
  - exact REGS.
  - exact (so_fregs _ _ _ _ _ _ HS').
  - reflexivity.
  - exact RESV.
  - exact (so_fcsr _ _ _ _ _ _ HS).
  - reflexivity.
  - exact (so_zero _ _ _ _ _ _ HS').
  - exact RgPg_bst.
  - exact RgPg_regions_ok.
  - exact RgPg_disjoint.
  - exact RgPg_pub.
  - exact HFACTS.
  - exact OPS_HOLD_g.
  - exact APART_g.
  - exact MINVo.
  - exact COVER_g.
  - exact minv'.
Qed.

End DELTA.
End Delta.

Lemma inline_RB_find : forall st ks offs rss, sp_region st = Some (ks, offs, rss) ->
  forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> (k0 = ks /\ rg = rss) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Proof.
  intros st ks offs rss SPR k0 rg H. destruct (CallA.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
  destruct (Uint63.eqb k0 ks) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k0. left. split; [reflexivity|]. congruence.
  - apply Uint63.eqb_false_spec in Q. right. split; [exact Q| exact H].
Qed.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require Import BImg.
Module TwinB.
Import stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.AcctCore OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ExecF OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.ITreeA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.NodesA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import AProto.TwinB AMalloc_iface.TwinB AMalloc_iface2.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import Ledger.TwinB Op.TwinB Adeq.TwinB.

Import ListNotations.
Import W64 Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem.Mem FI St Step Plan PlanS CtrLib HeapOp.
Open Scope Z_scope.
Unset Lia Cache.

Import Actr.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX.

Unset Nia Cache. Unset Nra Cache.
Import ValP MemP CtrFX.
Import ActrA.
Module AP := OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec.

Section Delta.
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
Hypothesis Cw_ghost_grow : forall md ca LB ws m b0 n0 n, cw_holds Cw md ca LB ws m ->
  In (Win b0 n0 K_BLOCK) ws -> 0 < n0 -> b0 mod 8 = 0 ->
  (forall a, in_iv (shad b0, n) a -> ~ in_user LB a) -> cw_holds Cw md ca ((shad b0, n) :: LB) (ws ++ [Win (shad b0) n K_TWINz]) m.

Hypothesis OPS_frame_other : forall id args m m' mo, id <> HEAP_ID -> op_holds OPS id args m mo ->
  (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->

  (forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) -> wb bsegs m a = true -> wb bsegs m' a = true) ->
  op_holds OPS id args m' mo.
Hypothesis OPS_fp_other : forall id args a, id <> HEAP_ID -> Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS id args) ->
  in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Variable OTHER : Model -> Model -> Prop.
Hypothesis OPS_mo_other : forall id args m mo mo', id <> HEAP_ID -> OTHER mo mo' -> op_holds OPS id args m mo -> op_holds OPS id args m mo'.

Hypothesis OPS_cov0_img : forall a, (exists seg, find_segment bsegs a 1 = Some seg) -> op_cov0 OPS a.

Hypothesis OPS_cov0_stk : forall a, ATOP <= a < 2 ^ 47 -> op_cov0 OPS a.

Hypothesis IMGX_img : forall a, in_ivs IMGX a -> exists seg, find_segment bsegs a 1 = Some seg.

Section DELTA.
Variables (E : env) (st : sstate) (ms : machine_state) (mo : Model).
Hypothesis HS : st_ok bsegs OPS E st ms mo.
Hypothesis FOK : fresh_ok st = true.
Variables (Fv : Z -> word) (Gv : Z -> Z -> byte).
Definition E' : env := env_above E (s_next st) Fv Gv.

Lemma EXT : env_ext (s_next st) E E'.
Proof. apply env_above_ext. Qed.

Lemma NX : st_vars_below (s_next st) st = true /\ 0 < to_Z (s_next st) /\ to_Z (s_next st) + 256 <= 2 ^ 62.
Proof. apply HeapCtr.TwinB.fresh_ok_inv. exact FOK. Qed.

Lemma SVB_parts :
  rf_allb (sv_vars_below (s_next st)) (s_rf st) = true /\ rf_allb (sv_vars_below (s_next st)) (s_ff st) = true
  /\ resv_vars_below (s_next st) (s_resv st) = true
  /\ IMap.forallb (fun k r => PrimInt63.ltb k (s_next st) && region_vars_below (s_next st) r) (s_regs st) = true
  /\ forallb (fact_vars_below (s_next st)) (s_facts st) = true
  /\ forallb (fun o => forallb (sv_vars_below (s_next st)) (op_args o)) (s_ops st) = true.
Proof.
  destruct NX as (SVB & _). unfold st_vars_below in SVB.
  apply andb_prop in SVB as [SVB H6]. apply andb_prop in SVB as [SVB H5]. apply andb_prop in SVB as [SVB H4'].
  apply andb_prop in SVB as [SVB H3]. apply andb_prop in SVB as [H1 H2]. repeat split; assumption.
Qed.

Lemma HS' : st_ok bsegs OPS E' st ms mo.
Proof. destruct NX as (SVB & POS & _). exact (st_ok_reval bsegs OPS (s_next st) E E' EXT st ms mo POS SVB HS). Qed.

Lemma den_E' : forall v, sv_vars_below (s_next st) v = true -> den E' v = den E v.
Proof. intros v Hv. exact (den_reval (s_next st) E E' EXT v Hv). Qed.

Lemma ev_E'_below : forall k, to_Z k < to_Z (s_next st) -> ev E' k = ev E k.
Proof. intros k Hk. unfold E'. apply ev_below. exact Hk. Qed.

Lemma ev_E'_fresh : forall i, (i <= 200)%nat -> ev E' (addn (s_next st) i) = Fv (Z.of_nat i).
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  assert (EA : to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i) by (apply addn_Z; rewrite wB_two63, two63_eq; lia).
  unfold E'. rewrite ev_above by (rewrite EA; lia). rewrite EA. f_equal. lia.
Qed.

Lemma reg_E' : forall k rg, IMap.find k (s_regs st) = Some rg ->
  ev E' k = ev E k /\ hiZ E' rg = hiZ E rg /\ PrimInt63.ltb k (s_next st) = true /\ region_vars_below (s_next st) rg = true.
Proof.
  intros k rg Hk. destruct SVB_parts as (_ & _ & _ & HR & _). exact (regs_reval_find (s_next st) E E' EXT _ k rg (so_bst _ _ _ _ _ _ HS) HR Hk).
Qed.

Variables (R' : bvmap 5 word) (m' : amem) (mo' : Model).

Variables (aw : word) (LB LBk : blocks).
Hypothesis AWH : aw_holds_asan AI ACCT UNIV aw LB (ms_mem ms) mo.
Hypothesis LBk_sub : forall v, In v LBk -> In v LB.
Let sp : Z := bv_unsigned (AP.getr (ms_regs ms) 2%bv).
Hypothesis MINV' : ALib.Mem.mem_inv bsegs m'.
Definition stableA (a : Z) : Prop := (sp <= a < 2 ^ 47) \/ in_ranges (aci AI) a \/ in_user LBk a.

Hypothesis SBV : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Hypothesis SBO : forall o a, In o (s_ops st) -> not_id HEAP_ID o -> 0 <= a < two64 ->
  Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E') (op_args o))) -> m' (Z_to_bv 64 a) = ms_mem ms (Z_to_bv 64 a).
Hypothesis WBM : forall a, 0 <= a < two64 -> (in_ranges (aci AI) a \/ (exists a', in_ranges (aci AI) a' /\ a = shad a') \/ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a')) ->
  wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true.

Hypothesis SBT : forall a, 0 <= a < 2 ^ 64 -> sh_cov a -> in_based E (s_regs st) a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).

Hypothesis SBS : forall a, ATOP + 4096 <= a < sp ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).

Lemma stable_byte : forall a, 0 <= a < 2 ^ 64 -> stableA a ->
  rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true).
Proof. exact SBV. Qed.

Variables (ks : int) (offs : w64) (rss : region) (ksp : int).
Hypothesis SPR : sp_region st = Some (ks, offs, rss).
Hypothesis Hksp : okey offs = Some ksp.
Hypothesis SPE : sp = bv_unsigned (ev E ks) + keyZ ksp.
Variables (wnl : list (int * sv * w64)) (n : nat) (rest : list sv).
Hypothesis NW : CtrA.nonstack_windows n rest = Some wnl.
Hypothesis AJ : aregions_justified st wnl = true.
Hypothesis WF : windows_wf (wins_of E n rest) LB (ATOP + 4096).

Variable KEEP : int -> Prop.

Hypothesis WINKW : forall k0 len kd, KEEP k0 -> CtrA.win_lookup wnl k0 = Some (len, kd) ->
  forall a, bv_unsigned (ev E k0) <= a < bv_unsigned (ev E k0) + bv_unsigned (den E len) -> in_user LBk a.
Hypothesis VKEEP : forall k0 rg hs n sh' len, IMap.find k0 (s_regs st) = Some rg -> zero_view rg = Some hs -> KEEP k0 ->
  block_of_twin (s_facts st) k0 = Some n -> CallV.TwinB.view_parent (s_facts st) (s_regs st) n sh' ->
  CtrA.win_lookup wnl sh' = Some (len, K_TWIN) -> KEEP sh'.

Hypothesis TKEEP : forall k0 rg sh' kb n len, IMap.find k0 (s_regs st) = Some rg -> KEEP k0 -> CtrA.win_lookup wnl sh' = Some (len, K_TWIN) ->
  block_of_twin (s_facts st) sh' = Some kb -> CtrA.win_lookup wnl kb = Some (n, CtrLib.K_BLOCK) ->
  size_tail_ok (s_facts st) n = true -> tail_named (tail_rhs sh' n) k0 (s_facts st) = true -> KEEP sh'.

Lemma SP_den : bv_unsigned (den E (getr st X2)) = sp.
Proof. unfold sp. rewrite <- HeapCtr.TwinB.reg_of_X2, (GlueA.TwinB.getr_RA bsegs OPS E st ms mo HS X2). reflexivity. Qed.

Hypothesis K16 : keyZ ksp mod 16 = 0.
Hypothesis LOSP : loZ rss <= keyZ ksp.
Hypothesis FLOOR : ATOP + 4096 <= bv_unsigned (ev E ks) + loZ rss.

Lemma sp_region_same_ok :
  (forall a, 0 <= a < two64 -> bv_unsigned (ev E ks) + loZ rss <= a < bv_unsigned (ev E ks) + hiZ E rss ->
     rb bsegs m' a = rb bsegs (ms_mem ms) a /\ (wb bsegs (ms_mem ms) a = true -> wb bsegs m' a = true)) ->
  region_ok bsegs (s_priv st) E' m' ks rss.
Proof.
  intros SAME. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & KZ & _).
  pose proof (so_reg _ _ _ _ _ _ HS' ks rss Hrs) as RO. destruct (reg_E' ks rss Hrs) as (Ek & Eh0 & _).
  apply (FrameV.TwinB.region_ok_frame_v bsegs (s_priv st) E' (ms_mem ms) m' ks rss (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh0 in R. exact (SAME a Ha (R KZ)).
Qed.

Variables (RB : IMap.t region) (rs_new : region).
Hypothesis RB_bst : IMap.bst RB.
Hypothesis RB_find : forall k0 rg, IMap.find k0 RB = Some rg -> (k0 = ks /\ rg = rs_new) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Hypothesis RSN_lo : loZ rs_new = loZ rss.
Hypothesis RSN_hi : forall E0, hiZ E0 rs_new = hiZ E0 rss.
Hypothesis RSN_w : rg_w rs_new = rg_w rss.
Hypothesis RSN_ok : region_ok bsegs (s_priv st) E' m' ks rs_new.

Lemma rs_top : bv_unsigned (ev E ks) + hiZ E rss <= 2 ^ 47.
Proof.
  destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (HX2 & Hrs & KZ & HW & HBG).
  assert (K0 : ks <> 0%uint63) by (apply Uint63.eqb_false_spec; exact KZ).
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss ks rss HS SPR AJ Hrs K0) as [[_ TOP]|[NE _]]; [exact TOP| contradiction].
Qed.

Lemma sp_floor : ATOP + 4096 <= sp.
Proof. rewrite SPE. lia. Qed.
Lemma ks_nz : ks <> 0%uint63.
Proof. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & _ & KZ & _). apply Uint63.eqb_false_spec. exact KZ. Qed.
Lemma old_key_lt : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> to_Z k0 < to_Z (s_next st).
Proof. intros k0 rg H. destruct (reg_E' k0 rg H) as (_ & _ & LT & _). apply Uint63.ltb_spec in LT. exact LT. Qed.

Lemma fresh_Z : forall i, (i <= 200)%nat -> to_Z (addn (s_next st) i) = to_Z (s_next st) + Z.of_nat i.
Proof.
  intros i Hi. destruct NX as (_ & _ & B). pose proof (int_range (s_next st)) as R. rewrite two63_eq in R.
  rewrite addn_Z; [lia| rewrite wB_two63, two63_eq; lia].
Qed.
Lemma fresh_nz : forall i, (i <= 200)%nat -> PrimInt63.eqb (addn (s_next st) i) 0%uint63 = false.
Proof.
  intros i Hi. apply Uint63.eqb_false_spec. intros X. pose proof (fresh_Z i Hi) as KZ. rewrite X in KZ. change (to_Z 0%uint63) with 0 in KZ.
  destruct NX as (_ & P & _). lia.
Qed.
Lemma fresh_not_old : forall i k0 rg, (i <= 200)%nat -> IMap.find k0 (s_regs st) = Some rg -> addn (s_next st) i <> k0.
Proof. intros i k0 rg Hi F X. pose proof (fresh_Z i Hi). pose proof (old_key_lt k0 rg F). rewrite X in *. lia. Qed.

Variables (hargs : list sv) (md : w64) (A : sv) (nw : w64).
Hypothesis Hf : find_op HEAP_ID (s_ops st) = Some hargs.
Hypothesis Hc : CtrA.count_op HEAP_ID (s_ops st) = 1%nat.
Hypothesis Eh : hargs = VL md :: A :: VL nw :: rest.
Hypothesis Tnw : wt nw = false.
Hypothesis Nn : n = Z.to_nat (to_Z (wl nw)).
Hypothesis Ln : (3 * n <= length rest)%nat.

Lemma DEC : decode (map (den E) hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite Eh. exact (decode_hargs E md A nw rest n Tnw Nn Ln). Qed.

Lemma wlo_floor : forall wlo, stack_wlo st = Some wlo -> ATOP + 4096 <= bv_unsigned (den E (VP STACK_ID wlo)).
Proof.
  intros wlo H. unfold stack_wlo in H. rewrite Hf in H.
  assert (HN : heap_nwin hargs = Some n).
  { rewrite Eh. unfold heap_nwin. rewrite Tnw. rewrite <- Nn. destruct (Nat.leb_spec (3 * n) (length rest)); [reflexivity| lia]. }
  rewrite HN in H. rewrite Eh in H. destruct (stack_window_key n rest) as [w|] eqn:SK; [|discriminate].
  destruct (nowrap_kb (s_facts st) STACK_ID w); [|discriminate]. injection H as <-.
  destruct (CallA.TwinB.stack_window_key_In E n rest w SK) as (len & INW).
  pose proof (proj1 (Forall_forall _ _) WF _ INW) as (_ & _ & _ & [[_ C]|[[K _]|[K _]]]); cbn [w_kind w_lo] in *; [exact C| |]; unfold K_STACK, K_BLOCK, K_SUB in K; lia.
Qed.

Lemma shz_shad : forall a', 0 <= a' -> CallV.TwinB.shz a' = shad a'.
Proof. intros a' H. unfold CallV.TwinB.shz, shad, ASHOFF. rewrite Z.shiftr_div_pow2 by lia. change (2 ^ 3) with 8. lia. Qed.

Notation is_sliver k0 rg := (sliver_just (s_facts st) (s_regs st) ks (stack_wlo st) (sliver_floor st) k0 rg).
Lemma old_stable : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> KEEP k0 -> is_sliver k0 rg = false ->
  forall a, bv_unsigned (ev E k0) + loZ rg <= a < bv_unsigned (ev E k0) + hiZ E rg -> (sp <= a < 2 ^ 47) \/ in_user LBk a \/ sh_cov a.
Proof.
  intros k0 rg Hk K0 KS KP NSL a Ha. pose proof atop_range as ATR.
  destruct (CallA.TwinB.aregion_just_sound bsegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR AJ Hk K0) as [[EQK _]|(_ & [(len & kd & WL & LZ & HZ)|[(ABOVE & TOP)|[VJ|SL]]])];
    [| | | | congruence].
  - contradiction.
  - right. left. rewrite LZ in Ha. apply (WINKW k0 len kd KP WL). lia.
  - left. rewrite SP_den in ABOVE. lia.
  - destruct (CallV.TwinB.view_just_sound bsegs OPS E st ms mo wnl ks offs rss k0 rg HS SPR Hk K0 VJ) as [(_ & blo & bhi & SHA & TOP & FLR)|[(hs0 & n0 & sh' & len & ZV & BT & VPAR & WL & LO & HI)|[(_ & v & Hv & LO & HI)|(sh' & kbt & nt & len & WL & BTt & WLk & STt & TNt & _ & LO & HI)]]].
    + right. right. left. destruct (SHA a Ha) as (a' & Ha' & ->). exists a'.
      assert (FL : ATOP + 4096 <= blo).
      { destruct FLR as [(wlo & SW & ->)|[(rs0 & Frs & ->)|GE]].
        - exact (wlo_floor wlo SW).
        - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). rewrite Hrs in Frs. injection Frs as <-. exact FLOOR.
        - rewrite SP_den in GE. pose proof sp_floor. lia. }
      split; [lia| apply shz_shad; lia].
    + right. left. apply (WINKW sh' len K_TWIN (VKEEP k0 rg hs0 n0 sh' len Hk ZV KP BT VPAR WL) WL). lia.
    + right. right. right. exists v. split; [exact (IMGSH_SHLIT v Hv)| lia].
    + right. left. apply (WINKW sh' len K_TWIN (TKEEP k0 rg sh' kbt nt len Hk KP WL BTt WLk STt TNt) WL). lia.
Qed.

Lemma old_region_ok : forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> k0 <> 0%uint63 -> k0 <> ks -> KEEP k0 ->
  region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg Hk K0 KS KP. pose proof (so_reg _ _ _ _ _ _ HS' k0 rg Hk) as RO. destruct (reg_E' k0 rg Hk) as (Ek & Eh0 & _).
  assert (KZ : PrimInt63.eqb k0 0%uint63 = false) by (apply Uint63.eqb_false_spec; exact K0).
  apply (FrameV.TwinB.region_ok_frame_v bsegs (s_priv st) E' (ms_mem ms) m' k0 rg (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha R _. rewrite Ek, Eh0 in R.
  destruct (is_sliver k0 rg) eqn:SL.
  {
    destruct (CtrPre.TwinB.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR Hk K0 KS SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
    pose proof (wlo_floor wlo SW) as CE. specialize (R KZ). rewrite L0 in R. apply SBS. rewrite SPE. lia. }
  destruct (old_stable k0 rg Hk K0 KS KP SL a (R KZ)) as [X|[X|X]].
  - exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(left; exact X)).
  - exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; right; exact X)).
  - apply (SBT a ltac:(unfold two64 in Ha; lia) X). exists k0, rg. split; [exact Hk|]. split; [exact KZ| exact (R KZ)].
Qed.

Lemma win_off_image : forall a, in_ws (wins_of E n rest) a -> find_segment bsegs a 1 = None.
Proof.
  intros a X. unfold in_ws in X. apply in_ivs_In in X as (v & Hv & Hin). apply in_map_iff in Hv as (w & <- & Hw).
  pose proof atop_range as ATR.
  pose proof (proj1 (Forall_forall _ _) WF w Hw) as (W1 & W2 & W3 & [[K S]|[[K B]|[K (b & Hb & SUBb)]]]).
  - apply ref_find_segment_none; [lia|]. unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. lia.
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo _ a AWH B Hin)).
  - exact (proj2 (aw_user_ok_asan AI ACCT UNIV AI_fake aw LB (ms_mem ms) mo b a AWH Hb (SUBb a Hin))).
Qed.

Lemma pub_image_client : forall a seg, 0 <= a < two64 -> find_segment bsegs a 1 = Some seg -> ~ in_priv (s_priv st) a -> in_ranges (aci AI) a.
Proof.
  intros a seg Ha SEG NP.
  destruct (in_ivs_b IMGX a) eqn:IX.
  - apply in_ivs_b_spec in IX. apply in_ivs_In in IX as (v & Hv & Hin). unfold in_iv in Hin.
    destruct (IMGX_aci v Hv) as (N0 & [(rg & Hr & R1 & R2)|[(rg & Hr & R1 & R2)|(S1 & S2)]]).
    + exists rg. split; [exact Hr|]. lia.
    +   exfalso. pose proof (AI_aci_lo AI rg Hr) as LO.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
    + exfalso. pose proof atop_range as ATR0.
      rewrite (ref_find_segment_none a 1 ltac:(lia) ltac:(right; unfold ASHOFF in *; lia)) in SEG. discriminate.
  - exfalso. assert (NIX : ~ in_ivs IMGX a) by (rewrite <- in_ivs_b_spec; congruence).
    assert (NW0 : ~ in_ws (wins_of E n rest) a) by (intros X; rewrite (win_off_image a X) in SEG; discriminate).
    destruct (ops_apart_find bsegs OPS E (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS) Hf) as [_ IP].
    { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC)). auto. }
    apply NP. apply IP. exists seg. exact SEG.
Qed.

Lemma r0_ok : forall r0, IMap.find 0%uint63 (s_regs st) = Some r0 -> region_ok bsegs (s_priv st) E' m' 0%uint63 r0.
Proof.
  intros r0 H0. pose proof (so_reg _ _ _ _ _ _ HS' _ _ H0) as RO.
  apply (FrameV.TwinB.region_ok_frame_v bsegs (s_priv st) E' (ms_mem ms) m' _ r0 (so_zero _ _ _ _ _ _ HS') RO).
  intros a Ha _ R. destruct (R eq_refl) as [[seg SEG] NP].
  exact (stable_byte a ltac:(unfold two64 in Ha; lia) ltac:(right; left; exact (pub_image_client a seg Ha SEG NP))).
Qed.

Lemma rest_below : forallb (sv_vars_below (s_next st)) rest = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. apply andb_prop in X as [_ X]. exact X.
Qed.
Lemma A_below : sv_vars_below (s_next st) A = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). pose proof (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)) as X.
  cbn [op_args] in X. rewrite Eh in X. cbn [forallb] in X. apply andb_prop in X as [_ X]. apply andb_prop in X as [X _]. exact X.
Qed.
Lemma hargs_below : forallb (sv_vars_below (s_next st)) hargs = true.
Proof.
  destruct SVB_parts as (_ & _ & _ & _ & _ & SO). exact (proj1 (forallb_forall _ _) SO _ (find_op_In _ _ _ Hf)).
Qed.
Lemma reg_below : forall x, sv_vars_below (s_next st) (getr st x) = true.
Proof. intros x. destruct SVB_parts as (SVB & _). exact (rf_allb_get _ _ _ SVB x). Qed.

Lemma wins_of_E' : forall m0 l, forallb (sv_vars_below (s_next st)) l = true -> wins_of E' m0 l = wins_of E m0 l.
Proof.
  induction m0 as [|m0 IH]; intros l AV; [reflexivity|]. destruct l as [|x [|y [|z l']]]; try reflexivity. cbn [forallb] in AV.
  apply andb_prop in AV as [A1 AV]. apply andb_prop in AV as [A2 AV]. apply andb_prop in AV as [A3 AV].
  rewrite !wins_of_cons, (IH l' AV), !den_E' by assumption. reflexivity.
Qed.
Lemma map_den_E' : forall l, forallb (sv_vars_below (s_next st)) l = true -> map (den E') l = map (den E) l.
Proof.
  induction l as [|x l IH]; intros AV; [reflexivity|]. cbn [forallb] in AV. apply andb_prop in AV as [A1 AV].
  cbn [map]. rewrite (den_E' x A1), (IH AV). reflexivity.
Qed.
Lemma DEC' : decode (map (den E') hargs) = Some (w2Z md, den E A, wins_of E n rest, map (den E) (skipn (3 * n) rest)).
Proof. rewrite (map_den_E' hargs hargs_below). exact DEC. Qed.

Hypothesis OTH : OTHER mo mo'.
Lemma other_ops_ok : forall o, In o (s_ops st) -> not_id HEAP_ID o ->
  op_holds OPS (op_id o) (map (den E') (op_args o)) (ms_mem ms) mo -> op_holds OPS (op_id o) (map (den E') (op_args o)) m' mo'.
Proof.
  intros o Ho NI H. pose proof NI as NI0. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
  apply (OPS_mo_other _ _ _ mo mo' NI OTH). apply (OPS_frame_other _ _ (ms_mem ms) m' mo NI H).
  - intros a Ha FP. symmetry. exact (SBO o a Ho NI0 Ha FP).
  - exact WBM.
Qed.
Lemma aci_low : forall a, in_ranges (aci AI) a -> a < AIMG_HI.
Proof. intros a (iv0 & Hi & R). pose proof (AI_aci_img AI iv0 Hi). lia. Qed.

Lemma minv' : forall a b, m' a = Some b -> forall seg, find_segment bsegs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true.
Proof.
  intros a b H seg Hs. pose proof (MINV' a b H) as X. unfold ALib.Mem.ro_addr in X. rewrite Hs in X.
  destruct (seg_writable seg); [reflexivity| discriminate X].
Qed.

Variables (newR : list (int * region)) (delK : list int).
Hypothesis NEW_nodup : List.NoDup (map fst newR).

Hypothesis NEW_nz : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false.
Hypothesis DEL_ks : ~ In ks delK.
Hypothesis DEL_0 : ~ In 0%uint63 delK.
Hypothesis KEEP_del : forall k0, ~ In k0 delK -> KEEP k0.
Variable NEWSET : Z -> Prop.
Hypothesis NEW_ok : forall k rg, In (k, rg) newR -> region_ok bsegs (s_priv st) E' m' k rg.
Hypothesis NEW_range : forall k rg a, In (k, rg) newR ->
  bv_unsigned (ev E' k) + loZ rg <= a < bv_unsigned (ev E' k) + hiZ E' rg -> NEWSET a.
Hypothesis NEW_low : forall a, NEWSET a -> AIMG_HI <= a < ATOP + 4096 /\ ~ in_user LBk a.
Hypothesis NEW_nosh : forall a, NEWSET a -> ~ (0x7fff8000 <= a < 0x800be200).
Hypothesis NEW_nostk : forall a, NEWSET a -> ~ (exists a', ATOP <= a' < 2 ^ 47 /\ a = shad a').
Lemma NEW_nocov : forall a, NEWSET a -> ~ sh_cov a.
Proof.
  intros a Ha [X|(v & Hv & R)]; [exact (NEW_nostk a Ha X)|]. apply (NEW_nosh a Ha).
  destruct (SHLIT_cases v Hv) as [->|(_ & P1 & P2 & P3)]; [cbn [fst snd] in R|]; lia.
Qed.
Hypothesis NEW_disj : forall k1 r1 k2 r2 a, In (k1, r1) newR -> In (k2, r2) newR -> k1 <> k2 -> (rg_w r1 = true \/ rg_w r2 = true) ->
  ~ (bv_unsigned (ev E' k1) + loZ r1 <= a < bv_unsigned (ev E' k1) + hiZ E' r1 /\
     bv_unsigned (ev E' k2) + loZ r2 <= a < bv_unsigned (ev E' k2) + hiZ E' r2).

Definition RgPg : IMap.t region := GLib.UG.add_regions newR (GLib.UG.remove_keys delK RB).

Lemma RgPg_bst : IMap.bst RgPg.
Proof. unfold RgPg. apply GLib.UG.add_regions_bst. apply GLib.UG.remove_keys_bst. exact RB_bst. Qed.

Lemma RgPg_find : forall k0 rg, IMap.find k0 RgPg = Some rg ->
  In (k0, rg) newR
  \/ (~ In k0 (map fst newR) /\ ~ In k0 delK /\ ((k0 = ks /\ rg = rs_new) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg))).
Proof.
  intros k0 rg H. unfold RgPg in H.
  apply (GLib.UG.find_add_regions newR _ k0 rg (GLib.UG.remove_keys_bst _ _ RB_bst) NEW_nodup) in H as [H|[NN H]]; [left; exact H|].
  apply (GLib.UG.find_remove_keys delK _ k0 rg RB_bst) in H as [ND H]. right. split; [exact NN|]. split; [exact ND|]. exact (RB_find k0 rg H).
Qed.

Lemma new_nz : forall k rg, In (k, rg) newR -> PrimInt63.eqb k 0%uint63 = false.
Proof. exact NEW_nz. Qed.

Lemma RgPg_range : forall k0 rg a, IMap.find k0 RgPg = Some rg -> PrimInt63.eqb k0 0%uint63 = false ->
  bv_unsigned (ev E' k0) + loZ rg <= a < bv_unsigned (ev E' k0) + hiZ E' rg ->
  (In (k0, rg) newR /\ NEWSET a)
  \/ (~ In k0 (map fst newR) /\ ((k0 = ks /\ ATOP + 4096 <= a < 2 ^ 47) \/ (k0 <> ks /\ ((ATOP + 4096 <= a < 2 ^ 47) \/ in_user LBk a \/ sh_cov a)))).

Proof.
  intros k0 rg a H KZ Ha. destruct (RgPg_find k0 rg H) as [IN|(NN & ND & [[-> ->]|[NK F]])].
  - left. split; [exact IN| exact (NEW_range k0 rg a IN Ha)].
  - right. split; [exact NN|]. left. split; [reflexivity|]. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
    destruct (reg_E' ks rss Hrs) as (Ek & Ehh & _). rewrite RSN_lo, (RSN_hi E') in Ha.
    rewrite Ek, Ehh in Ha. pose proof rs_top. lia.
  - right. split; [exact NN|]. right. split; [exact NK|]. destruct (reg_E' k0 rg F) as (Ek & Ehh & _). rewrite Ek, Ehh in Ha.
    assert (K0' : k0 <> 0%uint63) by (intros ->; discriminate KZ).
    destruct (is_sliver k0 rg) eqn:SL.
    + left. destruct (CtrPre.TwinB.sp_lo_of_sliver OPS E st ms mo ks offs rss k0 rg HS SPR F K0' NK SL) as (_ & L0 & EH & _ & _ & wlo & SW & EKW).
      pose proof (wlo_floor wlo SW) as CE. pose proof rs_top as RT. pose proof (CallA.TwinB.sliver_neg st ks offs rss k0 rg SPR SL) as NEG.
      pose proof (bv_unsigned_in_range 64 (den E (rg_hi rss))) as RH. fold (hiZ E rss) in RH. rewrite L0 in Ha. lia.
    + destruct (old_stable k0 rg F K0' NK (KEEP_del k0 ND) SL a Ha) as [X|[X|X]]; [left; pose proof sp_floor; lia| right; left; exact X| right; right; exact X].
Qed.

Lemma RgPg_old : forall k0 rg, IMap.find k0 RgPg = Some rg -> ~ In k0 (map fst newR) ->
  exists rg0, IMap.find k0 (s_regs st) = Some rg0 /\ loZ rg = loZ rg0 /\ (forall E0, hiZ E0 rg = hiZ E0 rg0) /\ rg_w rg = rg_w rg0.
Proof.
  intros k0 rg H NN. destruct (RgPg_find k0 rg H) as [IN|(_ & _ & [[-> ->]|[_ F]])].
  - exfalso. apply NN. apply in_map_iff. exists (k0, rg). auto.
  - destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _). exists rss. split; [exact Hrs|]. split; [exact RSN_lo|]. split; [exact RSN_hi| exact RSN_w].
  - exists rg. auto.
Qed.

Lemma RgPg_disjoint : regions_disjoint E' RgPg.
Proof.
  intros k1 rg1 k2 rg2 H1 H2 NE Z1 Z2 WR a [A1 A2]. pose proof sp_floor as SPF.
  pose proof (RgPg_range k1 rg1 a H1 Z1 A1) as C1. pose proof (RgPg_range k2 rg2 a H2 Z2 A2) as C2.
  destruct C1 as [[I1 S1]|[NN1 C1]]; destruct C2 as [[I2 S2]|[NN2 C2]].
  - exact (NEW_disj k1 rg1 k2 rg2 a I1 I2 NE WR (conj A1 A2)).
  - destruct (NEW_low a S1) as [LOWa NU]. destruct C2 as [[_ X]|(_ & [X|[X|X]])]; [lia| lia| exact (NU X)| exact (NEW_nocov a S1 X)].
  - destruct (NEW_low a S2) as [LOWa NU]. destruct C1 as [[_ X]|(_ & [X|[X|X]])]; [lia| lia| exact (NU X)| exact (NEW_nocov a S2 X)].
  - destruct (RgPg_old k1 rg1 H1 NN1) as (q1 & F1 & L1 & HH1 & W1). destruct (RgPg_old k2 rg2 H2 NN2) as (q2 & F2 & L2 & HH2 & W2).
    rewrite L1, (HH1 E') in A1. rewrite L2, (HH2 E') in A2. rewrite W1, W2 in WR.
    exact (so_disj _ _ _ _ _ _ HS' k1 q1 k2 q2 F1 F2 NE Z1 Z2 WR a (conj A1 A2)).
Qed.

Lemma RgPg_in_based : forall a, in_based E' RgPg a -> NEWSET a \/ in_based E' (s_regs st) a.
Proof.
  intros a (k0 & rg & H & KZ & R). destruct (RgPg_find k0 rg H) as [IN|(NN & _)]; [left; exact (NEW_range k0 rg a IN R)|].
  destruct (RgPg_old k0 rg H NN) as (q & F & L1 & HH1 & _). right. exists k0, q. rewrite <- L1, <- (HH1 E'). auto.
Qed.

Lemma RgPg_regions_ok : forall k0 rg, IMap.find k0 RgPg = Some rg -> region_ok bsegs (s_priv st) E' m' k0 rg.
Proof.
  intros k0 rg H. destruct (RgPg_find k0 rg H) as [IN|(NN & ND & [[-> ->]|[NK F]])].
  - exact (NEW_ok k0 rg IN).
  - exact RSN_ok.
  - destruct (Uint63.eqb k0 0%uint63) eqn:Q0.
    + apply Uint63.eqb_correct in Q0. subst k0. exact (r0_ok rg F).
    + apply Uint63.eqb_false_spec in Q0. exact (old_region_ok k0 rg F Q0 NK (KEEP_del k0 ND)).
Qed.

Lemma RgPg_pub : abs_cells_public (s_priv st) RgPg.
Proof.
  intros r0 g gr c H0 Hg Hcc i Hi.
  destruct (RgPg_find _ _ H0) as [IN|(_ & _ & [[X _]|[_ F]])].
  - exfalso. pose proof (new_nz _ _ IN) as X. discriminate X.
  - exfalso. exact (ks_nz (eq_sym X)).
  - exact (so_pub _ _ _ _ _ _ HS r0 g gr c F Hg Hcc i Hi).
Qed.

Variables (h' : list sv) (md' : Z) (aw' : word) (ws' : list window) (ca' : list word).
Hypothesis DECN : decode (map (den E') h') = Some (md', aw', ws', ca').
Hypothesis HOLDN : op_holds OPS HEAP_ID (map (den E') h') m' mo'.
Hypothesis W1 : forall a, NEWSET a -> in_ws (heap_ws ws') a.
Hypothesis W3 : forall a, 0 <= a < two64 -> ~ in_ivs IMGX a -> ~ in_ws ws' a ->
  ~ in_ws (wins_of E n rest) a \/ (find_segment bsegs a 1 = None /\ ~ in_based E' RgPg a).
Hypothesis W4 : forall a, in_based E' RgPg a -> in_ws (heap_ws (wins_of E n rest)) a -> in_ws (heap_ws ws') a.

Definition opsg : list opinst := set_op HEAP_ID h' (s_ops st).

Lemma OPS_HOLD_g : ops_hold OPS E' opsg m' mo'.
Proof.
  apply (ops_hold_set_op OPS E' E' (s_ops st) HEAP_ID hargs h' (ms_mem ms) m' mo mo' Hf Hc (so_ops _ _ _ _ _ _ HS')); [| exact HOLDN].
  exact other_ops_ok.
Qed.

Lemma in_heap_ws : forall ws a, in_ws (heap_ws ws) a -> in_ws ws a.
Proof.
  intros ws a X. unfold in_ws, heap_ws in *. apply in_ivs_In in X as (v & Hv & Hin). apply in_ivs_In. exists v. split; [| exact Hin].
  apply in_map_iff in Hv as (w & <- & Hw). apply in_map. apply filter_In in Hw as [Hw _]. exact Hw.
Qed.

Lemma APART_g : ops_apart bsegs OPS E' opsg RgPg (s_priv st).
Proof.
  apply (ops_apart_set_op bsegs OPS E' E' (s_ops st) HEAP_ID hargs h' (s_regs st) RgPg (s_priv st) Hf Hc (so_apart _ _ _ _ _ _ HS')).
  - intros o a Ho NI OLD FP. destruct (OLD FP) as [NB IP]. split; [| exact IP].
    intros IB. unfold not_id in NI. apply Uint63.eqb_false_spec in NI.
    destruct (RgPg_in_based a IB) as [I|I]; [| exact (NB I)].
    destruct (OPS_fp_other _ _ a NI FP) as [R|[(a' & R & ->)|(a' & R & ->)]].
    + pose proof (aci_low a R) as LOW. destruct (NEW_low a I) as [X _]. lia.
    + apply (NEW_nosh _ I). apply CtrPre.TwinB.shad_img_band. split; [destruct R as (iv0 & Hi & R); pose proof (AI_aci_lo AI iv0 Hi); lia| exact (aci_low a' R)].
    + exact (NEW_nostk _ I (ex_intro _ a' (conj R eq_refl))).
  - intros a FP. rewrite OPS_fp1 in FP. apply (proj1 (fp_spec IMGX _ _ _ _ _ a DECN)) in FP as (Ha & NIX & NWS).
    destruct (W3 a Ha NIX NWS) as [NW0|[SEG NB]].
    + destruct (ops_apart_find bsegs OPS E' (s_ops st) (s_regs st) (s_priv st) HEAP_ID hargs a (so_apart _ _ _ _ _ _ HS') Hf) as [NB IP].
      { rewrite OPS_fp1. apply (proj2 (fp_spec IMGX _ _ _ _ _ a DEC')). auto. }
      split; [| exact IP]. intros IB. destruct (RgPg_in_based a IB) as [I|I]; [| exact (NB I)].
      apply NWS. apply in_heap_ws. exact (W1 a I).
    + split; [exact NB|]. intros [seg X]. rewrite SEG in X. discriminate X.
Qed.

Lemma opsg_cases : In (OpI HEAP_ID h') opsg /\ forall o, In o (s_ops st) -> o = OpI HEAP_ID hargs \/ In o opsg.
Proof.
  destruct (find_op_unique HEAP_ID (s_ops st) hargs Hf Hc) as (l1 & l2 & E0 & F1 & F2). unfold opsg. rewrite E0, (set_op_split HEAP_ID h' l1 l2 hargs F1).
  split; [apply in_app_iff; right; left; reflexivity|].
  intros o Ho. apply in_app_iff in Ho as [Ho|[Ho|Ho]]; [right; apply in_app_iff; left; exact Ho| left; symmetry; exact Ho| right; apply in_app_iff; right; right; exact Ho].
Qed.

Lemma COVER_g : forall a, fx_acc bsegs E' RgPg a -> op_cov OPS (insts E' opsg) a.
Proof.
  intros a [IB|IMG]; [| left; exact (OPS_cov0_img a IMG)].
  destruct opsg_cases as [INH OTHERS].
  assert (NEWCOV : in_ws (heap_ws ws') a \/ sh_cov a -> op_cov OPS (insts E' opsg) a).
  { intros X. right. apply Exists_exists. exists (HEAP_ID, map (den E') h'). split.
    - unfold insts. apply in_map_iff. exists (OpI HEAP_ID h'). split; [reflexivity| exact INH].
    - cbn [fst snd]. apply OPS_cov1. split; [reflexivity|]. eexists _, _, _, _. split; [exact DECN| exact X]. }
  destruct (RgPg_in_based a IB) as [I|I]; [exact (NEWCOV (or_introl (W1 a I)))|].
  destruct (so_cover _ _ _ _ _ _ HS' a (or_introl I)) as [C0|C1]; [left; exact C0|].
  apply Exists_exists in C1 as (oi & Hoi & CV). unfold insts in Hoi. apply in_map_iff in Hoi as (o & <- & Ho). cbn [fst snd] in CV.
  destruct (OTHERS o Ho) as [->|INo].
  - cbn [op_id op_args] in CV. apply OPS_cov1 in CV as (_ & md0 & aw0 & ws0 & ca0 & D0 & X). rewrite DEC' in D0. injection D0 as <- <- <- <-.
    destruct X as [X|X]; [exact (NEWCOV (or_introl (W4 a IB X)))| exact (NEWCOV (or_intror X))].
  - right. apply Exists_exists. exists (op_id o, map (den E') (op_args o)). split; [| exact CV].
    unfold insts. apply in_map_iff. exists o. split; [reflexivity| exact INo].
Qed.

Theorem delta_st_ok : forall (pc' : int) (rf' : rf sv) (resv' : sresv) (rv' : option word) (facts' : list fact) (nx' : int),
  rf_get rf' X0 = VL wzero ->
  (forall x, rget (Core R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) rv') (reg_of_r5 x) = den E' (rf_get rf' x)) ->
  resv_ok E' resv' rv' ->
  facts_hold E' facts' -> op_minv OPS mo' ->
  st_ok bsegs OPS E' (SS pc' rf' (s_ff st) resv' RgPg facts' opsg (s_priv st) nx')
        (MS R' (ms_fregs ms) (Z_to_bv 64 (to_Z pc')) (ms_fcsr ms) rv' m' (seg_rom bsegs)) mo'.
Proof.
  intros pc' rf' resv' rv' facts' nx' X0Z REGS RESV HFACTS MINVo.
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next ms_pc_val ms_regs ms_fregs ms_fcsr ms_resv ms_mem ms_rom ms_svc_pending MS].
  - reflexivity.
  - exact X0Z.
  - exact REGS.
  - exact (so_fregs _ _ _ _ _ _ HS').
  - reflexivity.
  - exact RESV.
  - exact (so_fcsr _ _ _ _ _ _ HS).
  - reflexivity.
  - exact (so_zero _ _ _ _ _ _ HS').
  - exact RgPg_bst.
  - exact RgPg_regions_ok.
  - exact RgPg_disjoint.
  - exact RgPg_pub.
  - exact HFACTS.
  - exact OPS_HOLD_g.
  - exact APART_g.
  - exact MINVo.
  - exact COVER_g.
  - exact minv'.
Qed.

End DELTA.
End Delta.

Lemma inline_RB_find : forall st ks offs rss, sp_region st = Some (ks, offs, rss) ->
  forall k0 rg, IMap.find k0 (s_regs st) = Some rg -> (k0 = ks /\ rg = rss) \/ (k0 <> ks /\ IMap.find k0 (s_regs st) = Some rg).
Proof.
  intros st ks offs rss SPR k0 rg H. destruct (CallA.TwinB.sp_region_inv st ks offs rss SPR) as (_ & Hrs & _).
  destruct (Uint63.eqb k0 ks) eqn:Q.
  - apply Uint63.eqb_correct in Q. subst k0. left. split; [reflexivity|]. congruence.
  - apply Uint63.eqb_false_spec in Q. right. split; [exact Q| exact H].
Qed.
End TwinB.
