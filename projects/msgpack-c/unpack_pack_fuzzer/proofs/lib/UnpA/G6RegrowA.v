(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Import PropExec MState Cells Step Frame Omono.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib Require Mem.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan ValProofs MemProofs PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require Import CtrFX MemFX.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops GLib GUnp G3 GWin G4 G1 G6A.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import OpsKeep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.UnpA Require Import G6RegrowAC.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Import G6A G6RegrowAC.

Module G6RegrowA.
Ltac is_arith T :=
  lazymatch T with
  | (@eq Z _ _) => idtac | (not (@eq Z _ _)) => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | (_ /\ _) => idtac | (_ \/ _) => idtac
  | _ => fail
  end.
Ltac revert_arith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then revert H else fail
         end.
Ltac alia := revert_arith; let K := fresh "aliaK" in pose proof I as K; clear - K; intros; unfold two64, two63, two62Z in *; lia.
Ltac inlist := cbn [In]; repeat first [left; reflexivity | right].

Lemma acall_pre_inv : forall room unw st r hargs wnl st1,
  ActrA.acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  call_pre st = Some r /\ exists R', st1 = setregs st R'.
Proof.
  intros room unw st r hargs wnl st1 H. unfold ActrA.acall_pre in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (ActrA.aheap_windows st) as [[ha wl0]|]; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  destruct (ActrA.forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as <- <- <- <-.
  split; [reflexivity|].
  unfold ActrA.forget_stack_below_sp_g in FS. destruct (ActrA.sp_region st) as [[[k off] rr]|]; [|discriminate].
  destruct (okey off) as [ksp|]; [|discriminate]. injection FS as <-. eexists. reflexivity.
Qed.

Lemma sink_fields : forall st R' r,
  let stS := sink st (setregs st R') r in
  s_facts stS = s_facts st /\ s_ops stS = s_ops st /\ s_priv stS = s_priv st /\ s_next stS = PrimInt63.add (s_next st) 15 /\
  getr stS X10 = getr st X10 /\ s_pc stS = r.
Proof.
  intros st R' r stS. subst stS. unfold sink.
  pose proof (setpc_fields (setr (clobber (setregs st R')) X10 (getr st X10)) r) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof (setr_fields (clobber (setregs st R')) X10 (getr st X10)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
  pose proof (clobber_fields (setregs st R')) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof (setregs_fields st R') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  rewrite P5, Y5, C5, Z6, P6, Y6, C6, Z7, P7, Y7, C7, Z8, P8, Y8, C8, Z9, P9.
  repeat split.
Qed.

Lemma cells_from_sound : forall r L, 0 <= L -> L mod 8 = 0 -> IMap.bst (rg_cells r) -> cells_from r L = true ->
  forall g gr c i, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> 0 <= to_Z (c_idx c) -> 0 <= i -> L <= 8 * keyZ g + to_Z (c_idx c) + i.
Proof.
  intros r L L0 L8 B H g gr c i Hf Hc Hidx Hi. unfold cells_from in H.
  pose proof (proj1 (IMap.forallb_inb _ _) H g gr (proj1 (IMap.find_inb g gr _ B) Hf)) as X. cbn beta in X. apply Z.leb_le in X.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DM. rewrite L8 in DM. unfold St.keyZ in *. lia.
Qed.

Lemma regrow_geom : forall (isV : bool) E (fs : list fact) g wsZ kB kT oc,
  let V := if isV then u_vstk g else u_cstk g in
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> pure_ok g -> wins_ok 1 g wsZ ->
  v_begin V = bv_unsigned (den E (VP kB wzero)) -> v_end V = bv_unsigned (den E (VP kT (wlit 8%uint63))) -> v_capend V = bv_unsigned (den E (VP kB oc)) ->
  implied fs (FULe (VP kT (wlit 8%uint63)) (VP kB oc)) = true -> implied fs (FULe (VP kB oc) (VP kT (wlit 8%uint63))) = true ->
  wt oc = false -> 16 <= w2Z oc -> w2Z oc < 1099511627776 ->
  In (Win (bv_unsigned (ev E kT)) 8 (if isV then K_VTOP else K_CTOP)) wsZ ->
  vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\
  v_begin V = bv_unsigned (ev E kB) /\ v_end V = bv_unsigned (ev E kT) + 8 /\ v_capend V = bv_unsigned (ev E kB) + w2Z oc /\
  bv_unsigned (den E (VP kT (wlit 8%uint63))) = bv_unsigned (ev E kT) + 8 /\ bv_unsigned (den E (VP kB oc)) = bv_unsigned (ev E kB) + w2Z oc /\
  w2Z oc = 8 * v_cap V /\ v_size V = v_cap V /\ bv_unsigned (ev E kT) + 8 = bv_unsigned (ev E kB) + w2Z oc /\ 32 <= v_cap V /\
  In (v_begin V, v_bytes V) (owned g) /\ v_size V = (if isV then u_D g + 1 else u_D g).
Proof.
  intros isV E fs g wsZ kB kT oc V Pz0 Pfacts0 P Wk LVB LVE LVC IMP1 IMP2 OCT L16 L40 RT.
  pose proof (pf g P) as (VC & EC & SC & VV & EV8 & SV' & LV & LA & ZV).
  pose proof P as (_ & _ & _ & CC & _ & _ & _ & CV & _ & DLIM & _ & _).
  assert (VFACTS : vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\ In (v_begin V, v_bytes V) (owned g) /\ v_size V = (if isV then u_D g + 1 else u_D g)).
  { subst V. destruct isV.
    - split; [exact VV|]. split; [exact EV8|]. split; [exact CV|]. split; [exact (owned_vstk g)| exact SV'].
    - split; [exact VC|]. split; [exact EC|]. split; [exact CC|]. split; [exact (owned_cstk g)| exact SC]. }
  destruct VFACTS as (VVAL & VELT & VCAP & VOWN & VSZ).
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (L := w2Z oc) in *.
  pose proof (cap32_pos _ VCAP) as CAP32. unfold EMBED_STACK in CAP32.

  assert (RT' : Tz + 8 < two64).
  { pose proof (proj1 (Forall_forall _ _) Wk _ RT) as X. cbn [w_kind] in X.
    pose proof (bv_unsigned_in_range 64 (den E (VP kB oc))) as RC. rewrite bv_modulus_64 in RC.
    destruct (X ltac:(destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_STACK; lia)) as [[[KD|KD] _]|[_ SO]].
    - exfalso. destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_BLOCK in KD; lia.
    - exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_GHOST in KD; lia.
    - unfold sub_ok in SO. cbv zeta in SO. cbn [w_kind w_lo w_len] in SO. subst V.
      destruct SO as [(KK & _ & _ & E5)|[(KK & _ & _ & E5)|[(KK & _)|(KK & _)]]].
      + destruct isV; [exfalso; unfold K_VTOP, K_CTOP in KK; lia|]. rewrite LVC in E5. clear - E5 RC. unfold two64 in *. lia.
      + destruct isV; [| exfalso; unfold K_VTOP, K_CTOP in KK; lia]. rewrite LVC in E5. clear - E5 RC. unfold two64 in *. lia.
      + exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_SLOT in KK; lia.
      + exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_ZONE in KK; lia. }
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in LVB. fold Bz in LVB.
  assert (DVE : bv_unsigned (den E (VP kT (wlit 8%uint63))) = Tz + 8).
  { apply G1.den_VP_nowrap. rewrite wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. exact RT'. }
  rewrite DVE in LVE.
  pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as IM1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as IM2.
  cbn [fact_holds] in IM1, IM2. rewrite DVE in IM1, IM2.
  assert (VCE : v_capend V = Bz + 8 * v_cap V) by (unfold v_capend; rewrite VELT, LVB; reflexivity).
  assert (VEN : v_end V = Bz + 8 * v_size V) by (unfold v_end; rewrite VELT, LVB; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.
  pose proof (w2Z_range oc) as ROC. fold L in ROC.
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { assert (DM : bv_unsigned (den E (VP kB oc)) = (Bz + L) mod two64) by (cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wrap64; reflexivity).
    destruct (Z_lt_le_dec (Bz + L) two64) as [LT2|GE2].
    - rewrite Z.mod_small in DM by (clear - LT2 RB ROC; lia). exact DM.
    - exfalso. rewrite <- (Z.mod_unique (Bz + L) two64 1 (Bz + L - two64)) in DM by (clear - GE2 RB ROC L40; unfold two64 in *; lia).
      rewrite VCE, DM in LVC. clear - LVC CAP32 L40 RB. unfold two64 in *. lia. }
  rewrite DVC in LVC, IM1, IM2.
  split; [exact VVAL|]. split; [exact VELT|]. split; [exact VCAP|]. split; [exact LVB|]. split; [exact LVE|]. split; [exact LVC|]. split; [exact DVE|]. split; [exact DVC|].
  split; [clear - VCE LVC; lia|]. split; [clear - VEN LVE VCE LVC IM1 IM2; lia|]. split; [clear - IM1 IM2; lia|]. split; [exact CAP32|]. split; [exact VOWN| exact VSZ].
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable isV : bool.
Variable MEMCPY_PC : int.

Definition KD : int := G6RegrowAC.KD isV.

Hypothesis AVECCOPY : forall st (K : TSet) E ms mo r hargs wnl st1 ka ra wlena kb nsv nZ md aw ws ca,
  st_ok segs OPS E st ms mo -> MP mo -> s_pc st = MEMCPY_PC ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) ->
  bv_unsigned (den E (getr st X10)) = bv_unsigned (ev E ka) -> IMap.find ka (s_regs st) = Some ra ->
  rg_bg ra = BGNone -> rg_lo ra = 0%uint63 -> rg_w ra = true ->
  CtrA.win_lookup wnl ka = Some (wlena, wlit 1%uint63) -> ActrA.twin_pat_ok st wnl ka = true ->
  0 < nZ -> nZ <= hiZ E ra -> hiZ E ra <= bv_unsigned (den E wlena) ->
  (forall g gr c i, IMap.find g (rg_cells ra) = Some gr -> In c (g_cells gr) -> 0 <= i < to_Z (c_w c) -> nZ <= 8 * keyZ g + to_Z (c_idx c) + i) ->
  bv_unsigned (den E (getr st X11)) = bv_unsigned (ev E kb) -> bv_unsigned (den E (getr st X12)) = nZ ->
  (bv_unsigned (ev E kb) + nZ <= bv_unsigned (ev E ka) \/ bv_unsigned (ev E ka) + nZ <= bv_unsigned (ev E kb)) ->
  SRCPAT st wnl kb nsv = true -> nZ <= bv_unsigned (den E nsv) ->
  the_op st = Some (md, aw, ws, ca) ->
  (forall LB, cw_holds (unp_cw segs XW) (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' ->
     (forall i, 0 <= i < nZ -> exists b, rb segs (ms_mem ms') (bv_unsigned (ev E ka) + i) = Some b /\ rb segs (ms_mem ms') (bv_unsigned (ev E kb) + i) = Some b /\
                                         rb segs (ms_mem ms) (bv_unsigned (ev E kb) + i) = Some b) ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Lemma regrow_sound : forall st r hargs wnl st1 aw ws ca sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (1%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  regrow SRCPAT isV st (sink st st1 r) wnl aw ws ca = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca sts K E ms model Hpc TO AP FRS HAP HS0 HMP HPB Hk.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  unfold regrow in HAP.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in HAP. rewrite SF in HAP.
  remember (if isV then vb else cb) as b eqn:EB in HAP. remember (if isV then ve else ce) as e eqn:EE in HAP.
  remember (if isV then vcap else ccap) as cap eqn:ECAP in HAP.
  destruct b as [|kB ob| | | | | | | | |]; try discriminate.
  destruct e as [|kT oe| | | | | | | | |]; try discriminate.
  destruct cap as [|kB' oc| | | | | | | | |]; try discriminate.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs stS)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  destruct (elem_cells isV rT 0) as [topc|] eqn:ETOP; [|discriminate].
  destruct (elem_cells isV rN (Uint63.of_Z (L / 8))) as [newc|] eqn:ENEW; [|discriminate].
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SRCP]. apply andb_prop in COND as [COND VCP].
  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL]. apply andb_prop in COND as [COND NOB].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB]. apply andb_prop in COND as [COND NTB].
  apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [COND L16].
  apply andb_prop in COND as [COND OCT]. apply andb_prop in COND as [COND OE8]. apply andb_prop in COND as [KBB OB0].
  apply Uint63.eqb_correct in KBB. subst kB'.
  apply (proj1 (weqb_ok _ _)) in OB0. subst ob. apply (proj1 (weqb_ok _ _)) in OE8. subst oe. apply negb_true_iff in OCT.
  apply Z.leb_le in L16. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0.
  apply G1.neqb_neq in NNT. apply G1.neqb_neq in NNB. apply G1.neqb_neq in NTB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply G1.existsb_win_In in EXN. apply G1.existsb_win_In in EXT.
  apply andb_prop in COND2 as [COND2 WT]. apply andb_prop in COND2 as [COND2 HIT]. apply andb_prop in COND2 as [COND2 LOT].
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN. apply Uint63.eqb_correct in LOT. apply sv_eqb_eq in HIT.

  destruct (IMap.find kN (s_regs st)) as [ra|] eqn:FNst; [|discriminate VCP].
  destruct (CtrA.win_lookup wnl kN) as [[wlena kda]|] eqn:WLK; [|discriminate VCP].
  apply andb_prop in VCP as [VCP PATa]. apply andb_prop in VCP as [VCP KDa]. apply andb_prop in VCP as [VCP WLa]. apply andb_prop in VCP as [VCP CFa]. apply andb_prop in VCP as [VCP HIa].
  apply andb_prop in VCP as [VCP Wa]. apply andb_prop in VCP as [BGa LOa].
  apply Uint63.eqb_correct in LOa. apply sv_eqb_eq in HIa. apply sv_eqb_eq in WLa. apply (proj1 (weqb_ok _ _)) in KDa. subst wlena kda.
  assert (BGa' : rg_bg ra = BGNone) by (destruct (rg_bg ra); try discriminate BGa; reflexivity).
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & rav & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.
  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pcov0 Pminv0].
  set (m := ms_mem ms).

  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  change (G6RegrowAC.KD isV) with KD in *.
  set (wT := top_win kT 8 KD) in *.
  assert (KDv : to_Z KD = (if isV then K_VTOP else K_CTOP)) by (unfold KD, G6RegrowAC.KD; destruct isV; reflexivity).
  assert (WTd : forall E0, wden E0 wT = Win (bv_unsigned (ev E0 kT)) 8 (if isV then K_VTOP else K_CTOP)) by (intros E0; subst wT; rewrite top_win_den, KDv; reflexivity).
  assert (L40' : w2Z oc < 1099511627776) by exact L40.

  assert (GEOM : forall E0 u0 g0, ev E0 0%uint63 = Z_to_bv 64 0 -> facts_hold E0 fs ->
            decode_uc (map (den E0) [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]) = Some u0 ->
            link u0 g0 -> pure_ok g0 -> wins_ok 1 g0 (map (wden E0) ws) ->
            let V := if isV then u_vstk g0 else u_cstk g0 in
            vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\
            v_begin V = bv_unsigned (ev E0 kB) /\ v_end V = bv_unsigned (ev E0 kT) + 8 /\ v_capend V = bv_unsigned (ev E0 kB) + w2Z oc /\
            bv_unsigned (den E0 (VP kT (wlit 8%uint63))) = bv_unsigned (ev E0 kT) + 8 /\ bv_unsigned (den E0 (VP kB oc)) = bv_unsigned (ev E0 kB) + w2Z oc /\
            w2Z oc = 8 * v_cap V /\ v_size V = v_cap V /\ bv_unsigned (ev E0 kT) + 8 = bv_unsigned (ev E0 kB) + w2Z oc /\ 32 <= v_cap V /\
            In (v_begin V, v_bytes V) (owned g0) /\ v_size V = (if isV then u_D g0 + 1 else u_D g0)).
  { intros E0 u0 g0 Pz Pf DU LK0 P0 Wk0. cbn [map decode_uc] in DU. injection DU as <-.
    pose proof LK0 as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
    cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
    apply (regrow_geom isV E0 fs g0 (map (wden E0) ws) kB kT oc Pz Pf P0 Wk0); try assumption.
    - destruct isV; [rewrite EB; exact Lvb| rewrite EB; exact Lcb].
    - destruct isV; [rewrite EE; exact Lve| rewrite EE; exact Lce].
    - destruct isV; [rewrite ECAP; exact Lvcap| rewrite ECAP; exact Lccap].
    - rewrite <- (WTd E0). apply in_map. exact EXT. }

  pose proof HC as HCm.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & LK & P & O & Wk & M & CS0). clear CS0.
  destruct (GEOM E _ g Pz0 Pfacts0 eq_refl LK P Wk) as (VVAL & VELT & VCAP & LVB & LVE & LVC & DVE & DVC & LCAP & SZC & TZ8 & CAP32 & VOWN & VSZ).
  set (V := if isV then u_vstk g else u_cstk g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.
  fold L in LVC, DVC, LCAP, TZ8.
  pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  assert (VBY : v_bytes V = 8 * v_cap V) by (unfold v_bytes; rewrite VELT; reflexivity).

  pose proof (Preg0 kN ra FNst) as ROKa.
  assert (LOa' : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity).
  pose proof (w2Z_range oc) as ROC. fold L in ROC. unfold two40Z in L40.
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. alia. }
  assert (HIa' : hiZ E ra = 2 * L) by (unfold hiZ; rewrite HIa; cbn [den]; rewrite wbv_unsigned; exact L2w).
  pose proof (ro_range _ _ _ _ _ _ ROKa KN0) as RNr. rewrite LOa', HIa' in RNr. fold Nz in RNr.
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RBz. rewrite bv_modulus_64 in RBz. fold Bz in RBz.

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (G1.den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + L - L) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz (2 * L) HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) (v_bytes V) L); [| alia| alia| rewrite VBY; alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. rewrite LVB. exact Hb. }

  apply (AVECCOPY st K E ms model (wl rav) hargs wnl (setregs st R') kN ra (VL (wlit (Uint63.of_Z (2 * L)))) kB (VL oc) L 1%uint63 aw ws
           [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] HS0 HMP Hpc AP).
  - fold dx. rewrite DXV. reflexivity.
  - exact FNst.
  - exact BGa'.
  - exact LOa.
  - exact Wa.
  - exact WLK.
  - exact PATa.
  - alia.
  - rewrite HIa'. alia.
  - rewrite HIa'. cbn [den]. rewrite wbv_unsigned, L2w. apply Z.le_refl.
  - intros g0 gr cc i Hf Hc Hi. apply (cells_from_sound ra L ltac:(alia) L8 (ro_bst _ _ _ _ _ _ ROKa) CFa g0 gr cc i Hf Hc); [| lia].
    pose proof (Uint63.to_Z_bounded (c_idx cc)). lia.
  - rewrite X11B. exact (den_VP0 E kB wzero (weqb_refl _)).
  - fold n12. exact N12V.
  - fold Bz Nz. clear - SEP. lia.
  - exact SRCP.
  - cbn [den]. rewrite wbv_unsigned. fold L. apply Z.le_refl.
  - exact TO.
  -
    intros LB' HC'. change (to_Z 1%uint63) with 1 in HC'.
    cbn [cw_holds unp_cw] in HC'. unfold cw_unp_holds in HC'. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC'. cbn [map decode_uc] in HC'.
    destruct HC' as (g' & LK' & P' & O' & Wk' & _).
    destruct (GEOM E _ g' Pz0 Pfacts0 eq_refl LK' P' Wk') as (_ & VELT' & _ & LVB' & _ & _ & _ & _ & LCAP' & _ & _ & _ & VOWN' & _).
    cbn [den]. rewrite wbv_unsigned. fold L Bz. fold L in LCAP'. fold Bz in LVB'.
    pose proof VOWN' as OW'. rewrite LVB' in OW'. unfold v_bytes in OW'. rewrite VELT' in OW'. rewrite <- LCAP' in OW'.
    split; [exact (proj1 O' _ OW')|].

    intros w0 Hw0 KD0 a Ha0 Hb0.
    destruct (proj1 (Forall_forall _ _) Wk' w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[NB SOK]].
    + exact (DJ _ OW' a Ha0 Hb0).
    + exfalso. destruct KD0 as [KB1|KG]; [exact (NB KB1)|]. unfold sub_ok in SOK. cbv zeta in SOK.
      destruct SOK as [(KK & _)|[(KK & _)|[(KK & _)|(KK & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_GHOST in *; lia.
  -
    intros E' ms' mo' HX' HMP' HSS COPYB.
    {
    clear DEC.
    clear g LK P O Wk M VVAL VELT VCAP LVB LVE LVC DVE DVC LCAP SZC TZ8 CAP32 VOWN VSZ VV1 VV2 VV3 VV4 VBY DISJN SEP HA WF HCm V LB.
    set (nT := s_next stS) in *.
    destruct (fresh_ok_inv stS FRS) as (VBS & NPOSS & N62S). fold nT in VBS, NPOSS, N62S.
    set (M' := ms_mem ms') in *.
    assert (TZ15 : to_Z nT = to_Z n0 + 15).
    { subst nT. rewrite SN. fold n0. rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia). reflexivity. }
    assert (TZ16 : to_Z (PrimInt63.add nT 1) = to_Z n0 + 16).
    { rewrite add_Z by (change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; alia). rewrite TZ15. change (to_Z 1%uint63) with 1. lia. }
    set (NT := Nz + L - 8).
    set (Fv := fun _ : Z => Z_to_bv 64 NT). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
    set (E1 := env_above E' nT Fv Gv).
    assert (HX1 : env_ext nT E' E1) by (subst E1; apply env_above_ext).
    assert (HX : env_ext n0 E E1) by (apply (env_ext_trans n0 nT E E' E1); [lia| exact HX'| exact HX1]).
    assert (ENT : ev E1 nT = Z_to_bv 64 NT) by (subst E1; rewrite ev_above by lia; reflexivity).

    assert (INCA : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] -> In v (op_args o)).
    { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
    assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
    { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
      repeat split; right; right; right; apply in_app_iff; left; assumption. }
    assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
    { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    assert (INb : In (VP kB wzero) (op_args o)) by (rewrite EB; destruct isV; apply INCA; inlist).
    assert (INe : In (VP kT (wlit 8)) (op_args o)) by (rewrite EE; destruct isV; apply INCA; inlist).
    assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero INb).
    assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 8) INe).
    assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
    assert (EVN1 : ev E1 kN = ev E kN) by exact (proj1 (proj2 HX kN KN_LT)).
    assert (EVB1 : ev E1 kB = ev E kB) by exact (proj1 (proj2 HX kB KB_LT)).
    assert (EVT1 : ev E1 kT = ev E kT) by exact (proj1 (proj2 HX kT KT_LT)).
    assert (NTV : bv_unsigned (ev E1 nT) = NT).
    { rewrite ENT, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. subst NT. alia. }
    pose proof (st_ok_reval segs OPS nT E' E1 HX1 stS ms' mo' NPOSS VBS HSS) as HSE1.
    pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 Pbst1 Preg1 Pdisj1 _ Pfacts1 Pops1 _ _ _ _].
    rewrite SF in Pfacts1. fold fs in Pfacts1.

    assert (DDX1 : den E1 dx = den E1 (VP kN wzero)).
    { rewrite (den_reval n0 E E1 HX dx VBdx), DXV. rewrite <- EVN1. apply bv_eq. symmetry. exact (den_VP0 E1 kN wzero (weqb_refl _)). }
    pose proof (setreg_sound segs OPS E1 stS _ mo' X10 (VP kN wzero) HSE1 ltac:(discriminate) ltac:(rewrite SX10; exact DDX1)) as HS3.
    pose proof (repl_regs_sound segs OPS kept_r5 dx (VP kN wzero) E1 _ _ mo' HS3 ltac:(cbn; intuition discriminate) DDX1) as HS5.
    apply (Hk st' (or_introl eq_refl) E1 ms' mo' HX HMP').
    set (st5 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero))) in *.
    pose proof (repl_regs_fields kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    pose proof (setr_fields stS X10 (VP kN wzero)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    assert (F5ops : s_ops st5 = opre ++ o :: opost) by (subst st5; rewrite Q6, Y6, SO; exact OPSEQ).
    assert (F5regs : s_regs st5 = s_regs stS) by (subst st5; rewrite Q4, Y4; reflexivity).
    assert (F5pv : s_priv st5 = s_priv st) by (subst st5; rewrite Q7, Y7; exact SPV).
    assert (F5fs : s_facts st5 = fs) by (subst st5; rewrite Q5, Y5; exact SF).
    subst st'.

    pose proof (ops_hold_in OPS _ _ _ _ o Pops1 ltac:(rewrite SO; exact (op_in_In st o OPS1))) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA' & WF & HC). change (ms_mem ms') with M' in HA', HC.
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
    cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
    destruct HC as (g2 & LK2 & P2 & O2 & Wk2 & M2 & _ & AX2).
    destruct (GEOM E1 _ g2 Pz1 Pfacts1 eq_refl LK2 P2 Wk2) as (V2VAL & V2ELT & V2CAP & V2B & V2E & V2C & DVE & DVC & LCAP2 & V2SC & TZ8 & CAP32 & V2OWN & V2SZ).
    rewrite EVB1 in V2B, V2C, DVC, TZ8. rewrite EVT1 in V2E, DVE, TZ8. fold L Bz Tz in V2B, V2E, V2C, DVE, DVC, LCAP2, TZ8.
    pose proof LK2 as (L2root & L2cb & L2ce & L2ccap & L2vb & L2ve & L2vcap & L2zp & L2zf & L2c0 & L2D).
    cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in L2root, L2cb, L2ce, L2ccap, L2vb, L2ve, L2vcap, L2zp, L2zf, L2c0, L2D.
    pose proof (pf g2 P2) as (VC' & EC' & SC' & VV' & EV8' & SV'' & LV' & LA' & ZV').
    pose proof P2 as (_ & _ & _ & CC' & _ & _ & _ & CV' & _ & DLIM' & _ & _).
    set (V2 := if isV then u_vstk g2 else u_cstk g2) in *.
    set (bm' := bmem_of segs M') in *.
    pose proof V2VAL as (W1 & W2 & W3 & W4).
    assert (V2BY : v_bytes V2 = L) by (unfold v_bytes; rewrite V2ELT; alia).
    pose proof (proj1 O2 _ V2OWN) as V2LB. rewrite V2BY in V2LB, V2OWN.

    pose proof (Preg1 kN rN FN) as ROKN. pose proof (Preg1 kT rT FT) as ROKT.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
    assert (HIN' : hiZ E1 rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
    assert (HIT' : hiZ E1 rT = 8) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT', EVT1 in RTr. fold Tz in RTr.
    assert (WNd1 : wden E1 wN = Win Nz (2 * L) HeapOp.K_BLOCK) by exact (WNd E1 EVN1).
    assert (WTd1 : wden E1 wT = Win Tz 8 (to_Z KD)) by (rewrite (WTd E1), EVT1, KDv; reflexivity).
    assert (DISJN : forall ob, In ob (owned g2) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk2 _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
    { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
      intros a Ha Hb. apply (DISJN _ V2OWN a Ha). unfold in_iv. cbn [fst snd]. rewrite V2B. exact Hb. }
    assert (BYN : forall a, Nz <= a < Nz + 2 * L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (bytes_of_region segs _ E1 M' kN rN a ROKN KN0). rewrite LON', HIN', EVN1. fold Nz. alia. }

    assert (NLB : In (Nz, 2 * L) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KDx _]|[[_ IN]|[KDx _]]]).
      - cbn in KDx. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KDx. discriminate KDx.
      - exact IN.
      - cbn in KDx. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KDx. exfalso. clear - KDx. lia. }

    assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
    { intros i Hi. destruct (COPYB i Hi) as (b0 & C1 & C2 & _). fold Nz Bz in C1, C2. rewrite C1, C2. reflexivity. }
    assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
    { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite (RBC i Hi). reflexivity. }
    pose proof (bv_unsigned_in_range 64 (ev E kN)) as RNz. rewrite bv_modulus_64 in RNz. fold Nz in RNz.
    pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr1. rewrite LON', HIN', EVN1 in RNr1. fold Nz in RNr1.

      set (VN := vec_regrow V2 Nz).
      set (g' := mkUnp (u_ctx g2) (u_vis g2) (u_data g2) (u_len g2) (u_levels g2) (if isV then u_cstk g2 else VN) (if isV then VN else u_vstk g2) (u_zone g2)).
      assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V2 /\ v_cap VN = 2 * v_cap V2 /\ v_elt VN = 8 /\ v_bytes VN = 2 * L /\
                    v_end VN = NT + 8 /\ v_capend VN = Nz + 2 * L).
      { subst VN. unfold vec_regrow, v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite V2ELT, V2SC. subst NT. repeat split; alia. }
      destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
      assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
      assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
      assert (TZB : Tz = Bz + L - 8) by alia.
      assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply G1.neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
      assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

      assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
      { intros a Ha Hb. apply (DISJN _ V2OWN a Ha). unfold in_iv. cbn [fst snd]. rewrite V2B. exact Hb. }

      assert (BYNT : forall a, NT <= a < NT + 16 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
      { intros a Ha. apply BYN. subst NT. alia. }
      assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
      { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ M' mo' _ a HA' V2LB). unfold in_iv. cbn [fst snd]. rewrite V2B. alia. }

      assert (ECINV : forall r gi cs, elem_cells isV r gi = Some cs -> exists gr, IMap.find gi (rg_cells r) = Some gr /\ cs = g_cells gr).
      { intros r gi cs H. unfold elem_cells in H. destruct (IMap.find gi (rg_cells r)) as [gr|]; [|discriminate]. exists gr. split; [reflexivity|].
        destruct isV; destruct (g_cells gr) as [|[i1 w1 v1] [|[i2 w2 v2] [|? ?]]]; try discriminate H;
          match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; reflexivity| discriminate H] end. }
      destruct (ECINV rT 0%uint63 topc ETOP) as (grT & FgrT & ->).
      destruct (ECINV rN (Uint63.of_Z (L / 8)) newc ENEW) as (grN & FgrN & ->).
      assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
      { apply keyZ_of_Z. unfold two62Z. clear - L16 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
      assert (L8E : 8 * (L / 8) = L) by (clear - L8 L16; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
      assert (STOP : slot_ok segs E1 M' Tz (g_cells grT)).
      { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kT rT FT) 0%uint63 grT FgrT) as X. rewrite EVT1 in X. fold Tz in X. change (keyZ 0%uint63) with 0 in X.
        rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
      assert (SNEW : slot_ok segs E1 M' (Nz + L) (g_cells grN)).
      { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kN rN FN) _ grN FgrN) as X. rewrite EVN1, KEYL, L8E in X. fold Nz in X. exact X. }
      assert (STOP' : slot_ok segs E1 M' NT (g_cells grT)).
      { apply (slot_ok_shift segs E1 M' M' Tz NT _ STOP). intros i Hi. subst NT. rewrite TZB.
        replace (Nz + L - 8 + i) with (Nz + (L - 8 + i)) by alia. rewrite (RBC (L - 8 + i)) by alia. f_equal. alia. }
      assert (SNEW' : slot_ok segs E1 M' (NT + 8) (g_cells grN)).
      { replace (NT + 8) with (Nz + L) by (subst NT; alia). exact SNEW. }
      assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region16 (g_cells grT) (g_cells grN))).
      { apply (region16_ok segs (s_priv st) E1 M' nT _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| exact STOP'| exact SNEW']. }
      destruct (empty_region_ok segs (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
                  ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).

      assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E1) ws) a /\ ~ in_ivs IMGX a).
      { intros a Ha.
        assert (SFE : safe 1 g2 (map (wden E1) ws) a).
        { clear - V2B V2E P2 O2 Ha TZB. subst V2. destruct isV; [apply (safe_vstk 1 g2 LB _ P2 O2)| apply (safe_cstk 1 g2 LB _ P2 O2)]; rewrite V2B, V2E; lia. }
        destruct (owned_byte_props segs IMGX AW _ LB M' mo' 1 g2 _ _ a HA' WF O2 Wk2 V2OWN ltac:(unfold in_iv; cbn [fst snd]; rewrite V2B; alia) SFE) as (_ & NI & NW & _).
        split; [exact NW| exact NI]. }

      set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
      set (wNT := top_win nT 16 KD).
      set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
      set (b' := VP kN wzero). set (e' := VP nT (wlit 8)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
      set (ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
                  else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]).
      assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
      { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
        apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
        split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
      assert (LENws' : Z.of_nat (length ws') < two63).
      { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
      assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
      { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
      assert (WNTd : wden E1 wNT = Win NT 16 (to_Z KD)) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
      assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
      assert (De' : bv_unsigned (den E1 e') = NT + 8).
      { subst e'. rewrite (G1.den_VP_nowrap E1 nT (wlit 8)); rewrite ?wlit_ok, NTV; change (to_Z 8%uint63) with 8; [reflexivity| subst NT; alia]. }
      assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
      { subst cap'. rewrite (G1.den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }
      apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH [kN; kT]
               [(nT, region16 (g_cells grT) (g_cells grN)); (kB, empty_region L)] (mk_args 1%uint63 aw ws' ca') _ (PrimInt63.add nT 1)).
      -   intros k [<-|[<-|[]]]; rewrite F5regs.
        + split; [exact KN0|]. exists rN. split; [exact FN| exact WN].
        + split; [exact KT0|]. exists rT. split; [exact FT| exact WT].
      -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
      -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
      -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
      -   intros k r a [H1|[H1|[]]] IR; injection H1 as <- <-.
        + right. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs. split; [exact FN|].
          unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LON', HIN'. fold Nz.
          change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
          change (to_Z 16%uint63) with 16 in IR. subst NT. alia.
        + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
          destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
          * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))).
            destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
          * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
            split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. alia.
      -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
          unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region16 (g_cells grT) (g_cells grN))) with 0;
          unfold hiZ; cbn [region16 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 16%uint63) with 16; intros [I1 I2].
        + apply (DISJ_BN a); subst NT; alia.
        + apply (DISJ_BN a); subst NT; alia.
      -   rewrite (ho_holds _ _ _ _ _ HOPS).
        exists 1, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
        split; [apply mk_args_sound; exact LENws'|].

        assert (N24 : ~ c24 (2 * L)).
        { destruct (OpsTwin.UOT.cap32_bytes _ V2CAP) as (k2 & Hk2 & E2). unfold c24, C24_LO, C24_HI.
          replace (2 * L) with (256 * 2 ^ (k2 + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
          exact (OpsTwin.UOT.pow2_not_c24 (k2 + 1) ltac:(lia)). }
        assert (WkE1 : wins_ok 1 g2 (map (wden E1) ws)) by exact Wk2.
        split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA');
                apply (UOK.unp_wins_keep_map E1 1 g2 LB ws ws' P2 O2 WkE1);
                [intros x Hx; destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]];
                 [left; exact Hx'
                 |right; right; rewrite WB'd; unfold w_iv; cbn [w_kind w_lo w_len]; split; [reflexivity|];
                  replace (Bz, L) with (v_begin V2, L) by (rewrite V2B; reflexivity); exact V2OWN
                 |right; left; subst wNT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]
                |intros x Hx; destruct (win3_eqb x wN) eqn:QK1;
                 [right; right; apply win3_eqb_eq in QK1; subst x; rewrite WNd1; cbn [w_kind w_iv w_lo w_len];
                  split; [reflexivity|]; split; [exact NLB| exact N24]|];
                 destruct (win3_eqb x wT) eqn:QK2;
                 [right; left; apply win3_eqb_eq in QK2; subst x; subst wT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity|];
                 left; subst ws'; apply in_or_app; left; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1, QK2; reflexivity]|]. split.
        +
          unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
          destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
          * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
          * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
            right; left. split; [reflexivity|]. rewrite <- V2B. exact V2LB.
          * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
            right; right. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_SUB; alia|].
            exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L16. lia.
        +
          cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb].
          assert (CA' : ca' = [root; (if isV then cb else b'); (if isV then ce else e'); (if isV then ccap else cap');
                               (if isV then b' else vb); (if isV then e' else ve); (if isV then cap' else vcap); zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh])
            by (subst ca'; destruct isV; reflexivity).
          rewrite CA'. cbn [map decode_uc].
          assert (VNV : vec_valid VN).
          { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, V2SC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }
          assert (VNC : cap32_b (v_cap VN) = true).
          { rewrite VN3. unfold cap32_b. apply cap32_double; [exact V2CAP| alia]. }

          assert (DJ2 : forall b, In b (owned g2) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv b a).
          { intros b0 Hb0 a Ha. pose proof (proj1 (Forall_forall _ _) Wk2 _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
            destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
            apply (DJ b0 Hb0 a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
          assert (RDJ2 : forall b, In b (owned g2) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
          { intros b0 Hb0. pose proof (owned_pos g2 P2 b0 Hb0) as PO. unfold rdisj.
            destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
            destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
            exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
            - apply (DJ2 b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
            - apply (DJ2 b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }

          assert (VNB : (v_begin VN, v_bytes VN) = (Nz, 2 * L)) by (rewrite VN1, VN5; reflexivity).
          assert (V2Bb : (v_begin V2, v_bytes V2) = (Bz, L)) by (rewrite V2B, V2BY; reflexivity).

          assert (DLEN2 : u_D g2 = Z.of_nat (length (u_levels g2))) by reflexivity.
          assert (DPOS : 1 <= u_D g2) by (clear - V2SZ V2SC CAP32 LCAP2 DLEN2; destruct isV; lia).
          assert (LNE : u_levels g2 <> []) by (intros X; rewrite X in DLEN2; cbn in DLEN2; alia).
          assert (RLEN : Z.of_nat (length (removelast (u_levels g2))) = u_D g2 - 1).
          { rewrite (removelast_length _ LNE). rewrite Nat2Z.inj_sub by (destruct (u_levels g2); [exfalso; exact (LNE eq_refl)| cbn; lia]). rewrite <- DLEN2. reflexivity. }
          exists g'. split; [| split; [| split; [| split; [| split]]]].
          *
            unfold link. subst g'. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels u_cur_slot c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
            destruct isV; cbn [u_cstk u_vstk];
              rewrite ?Db', ?De', ?Dcap', ?VN1, ?VN6, ?VN7.
            -- split; [exact L2root|]. split; [exact L2cb|]. split; [exact L2ce|]. split; [exact L2ccap|].
               split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
               split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
            -- split; [exact L2root|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
               split; [exact L2vb|]. split; [exact L2ve|]. split; [exact L2vcap|].
               split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
          *
            unfold pure_ok. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. unfold u_D. cbn [u_levels]. change (Z.of_nat (length (u_levels g2))) with (u_D g2).
            pose proof P2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
            clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 VNV VNC VN2 VN4 V2SZ V2.
            destruct isV; subst V2; cbn in V2SZ.
            -- split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact VNV|]. split; [exact VN4|].
               split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
            -- split; [exact VNV|]. split; [exact VN4|]. split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|].
               split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
          *

            assert (TIE' : blocks_tied (owned g')).
            { pose proof (own_tied g2 LB O2) as OT.
              pose proof P2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _).
              pose proof (cap32_pos _ B4) as C32c. pose proof (cap32_pos _ B8) as C32v. unfold EMBED_STACK in C32c, C32v.
              destruct B1 as (_ & SZc & _). destruct B5 as (_ & SZv & _).
              subst g'. unfold blocks_tied, owned, cstk_block, vstk_block. cbn [u_cstk u_vstk u_zone snd].
              unfold v_bytes in OT |- *. rewrite B2, B6 in OT.
              clear - OT B2 B3 B6 B7 C32c C32v SZc SZv V2SZ V2SC LCAP2 VN5 V2.
              unfold v_bytes in VN5. subst V2. destruct isV; cbn [u_cstk u_vstk]; rewrite ?B2, ?B6; unfold v_bytes in VN5; lia. }
            destruct O2 as [OL [OF _]]. unfold own_ok. unfold owned, cstk_block, vstk_block in OL, OF, RDJ2. unfold owned, cstk_block, vstk_block in TIE' |- *.
            subst g'. cbn [u_cstk u_vstk u_zone] in TIE' |- *. subst V2. destruct isV; cbn [u_cstk u_vstk u_zone] in TIE' |- *; rewrite VNB in TIE' |- *; rewrite V2Bb in OL, OF, RDJ2;
              (split; [| split; [| exact TIE']]).
            -- intros b0 [<-|[<-|Hb0]]; [apply OL; left; reflexivity| exact NLB| apply OL; right; right; exact Hb0].
            -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. destruct (FOP_cons _ _ _ F2) as [F3 F4].
                  constructor; [| constructor; [| exact F4]].
                  ** constructor; [apply (proj2 (RDJ2 _ ltac:(left; reflexivity)))|]. exact (Forall_inv_tail F1).
                  ** apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; right; exact Hc))).
            -- intros b0 [<-|[<-|Hb0]]; [exact NLB| apply OL; right; left; reflexivity| apply OL; right; right; exact Hb0].
            -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
                  apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; exact Hc))).
          *
            unfold wins_ok. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
            assert (OWN' : forall b0, In b0 (owned g') -> b0 = (Nz, 2 * L) \/ In b0 (owned g2)).
            { intros b0 Hb0. subst g'. unfold owned, cstk_block, vstk_block in Hb0 |- *. cbn [u_cstk u_vstk u_zone] in Hb0 |- *.
              clear - Hb0 VNB. destruct isV; rewrite VNB in Hb0; cbn [In] in Hb0 |- *;
                destruct Hb0 as [X|[X|X]]; (try (left; symmetry; exact X)); right; tauto. }
            destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
            --
               pose proof (proj1 (forallb_forall _ _) KL x Hx') as KLx. cbn beta iota in KLx. destruct (kind_of x) as [kd|] eqn:KDx; [|discriminate KLx].
               pose proof (kind_of_sound E1 x kd KDx) as WK.

               assert (XN : forall a, in_iv (w_iv (wden E1 x)) a -> ~ (Nz <= a < Nz + 2 * L)).
               { intros a Ha HN. destruct x as [[xlo xlen] xkd]. unfold kind_of in KDx. cbn [snd] in KDx.
                 destruct xkd as [kw| | | | | | | | | |]; try discriminate KDx. destruct (wt kw) eqn:KWT; [discriminate KDx|]. injection KDx as <-.
                 destruct (Z.eq_dec (to_Z (wl kw)) HeapOp.K_BLOCK) as [K1|NK1].
                 -
                   pose proof (proj1 (forallb_forall _ _) OBK _ Hx') as OB. cbn beta iota in OB. rewrite KWT in OB. cbn [orb] in OB.
                   assert (KW1 : PrimInt63.eqb (wl kw) 1 = true) by (apply (proj2 (Uint63.eqb_spec _ _)); apply Uint63.to_Z_inj; rewrite K1; reflexivity).
                   rewrite KW1 in OB. cbn [negb] in OB.
                   destruct xlo as [|kx ox| | | | | | | | |]; try discriminate OB.
                   destruct (PrimInt63.eqb kx kN) eqn:KXN.
                   + apply Uint63.eqb_correct in KXN. subst kx. pose proof (proj1 (forallb_forall _ _) NOA _ Hx') as NO. cbn beta iota in NO. rewrite Uint63.eqb_refl in NO. cbn [negb orb] in NO.
                     apply win3_eqb_eq in NO. exact (NxN NO).
                   + cbn [orb] in OB. apply andb_prop in OB as [OB FND]. apply andb_prop in OB as [OX KX0]. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
                     destruct (IMap.find kx (s_regs stS)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HX0].
                     apply Uint63.eqb_correct in LOX. destruct (decide_ltu fs (VL wzero) (rg_hi rx)) as [[|]|] eqn:DH; try discriminate HX0.
                     pose proof (decide_ltu_sound E1 fs Pfacts1 _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS. cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS.
                     apply Uint63.eqb_false_correct in KXN.

                     pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
                     destruct WFx as (_ & _ & _ & [[KS _]|[[_ INx]|[KS _]]]);
                       [rewrite WK in KS; unfold HeapOp.K_STACK, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia| | rewrite WK in KS; unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia].
                     unfold w_iv, wden in INx. cbn [w_lo w_len] in INx. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in INx.
                     unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in Ha.
                     destruct (Z.eq_dec (bv_unsigned (ev E1 kx)) Nz) as [EQX|NEX].
                     * apply (Pdisj1 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) Nz). unfold loZ, hiZ. rewrite LOX, EQX, LON, HIN. cbn [den]. rewrite wbv_unsigned, L2w.
                       change (keyZ 0%uint63) with 0. rewrite ?EVN1. fold Nz. clear - HPOS L16. lia.
                     * exact (aw_blocks_disj segs IMGX AW _ LB _ M' mo' _ _ a HA' INx NLB ltac:(cbn [fst]; exact NEX) Ha ltac:(unfold in_iv; cbn [fst snd]; exact HN)).
                 -
                   pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
                   assert (K2 : 2 <= to_Z (wl kw)).
                   { rewrite WK in NS. destruct WFx as (_ & _ & _ & [[KS _]|[[KS _]|[KS _]]]); rewrite WK in KS;
                       unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in NS, KS, NK1; clear - NS KS NK1; lia. }
                   pose proof (proj1 (forallb_forall _ _) SWO _ Hx') as SW. cbn beta iota in SW. rewrite KWT in SW. cbn [orb] in SW.
                   destruct (Z.ltb_spec (to_Z (wl kw)) 2); [lia|].
                   apply orb_prop in SW as [SW|SW]; [apply win3_eqb_eq in SW; exact (NxT SW)|].
                   apply orb_prop in SW as [GH|SW].
                   { pose proof (aw_ghost_apart segs IMGX AW _ _ _ _ _ HA') as GA.
                     refine (GA _ _ (in_map (wden E1) _ _ Hx') (in_map (wden E1) _ _ EXN) _ _ a Ha _).
                     - rewrite WK. unfold K_GHOST. apply Z.leb_le in GH. exact GH.
                     - rewrite WNd1. reflexivity.
                     - rewrite WNd1. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact HN. }
                   destruct xlo as [|kx ox| | | | | | | | |]; try discriminate SW.
                   apply andb_prop in SW as [SW FND]. apply andb_prop in SW as [SW KX0]. apply andb_prop in SW as [KXN OX].
                   apply negb_true_iff in KXN. apply Uint63.eqb_false_correct in KXN. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
                   destruct (IMap.find kx (s_regs stS)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HXR]. apply Uint63.eqb_correct in LOX. apply sv_eqb_eq in HXR.
                   unfold wden, w_iv, in_iv in Ha. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in Ha. cbn [w_lo w_len fst snd] in Ha.
                   apply (Pdisj1 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) a). unfold loZ, hiZ. rewrite LOX, HXR, LON, HIN.
                   change (den E1 (VL (wlit (Uint63.of_Z (2 * L))))) with (wbv (wlit (Uint63.of_Z (2 * L)))). rewrite wbv_unsigned, L2w.
                   change (keyZ 0%uint63) with 0. rewrite ?EVN1. fold Nz. alia. }
               destruct (proj1 (Forall_forall _ _) Wk2 (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDJ DJ]|[NB SOK]].
               ++ left. split; [exact KDJ|]. intros b0 Hb0 a Ha Hb. destruct (OWN' b0 Hb0) as [->|Hb2]; [| exact (DJ b0 Hb2 a Ha Hb)].
                  apply (XN a Ha). unfold in_iv in Hb. cbn [fst snd] in Hb. exact Hb.
               ++ right. split; [exact NB|]. unfold sub_ok in SOK |- *. cbv zeta in SOK |- *. subst g'. cbn [u_cstk u_vstk u_levels u_zone].
                  destruct SOK as [(KK & A)|[(KK & A)|[A|A]]]; [| | right; right; left; exact A| right; right; right; exact A].
                  **
                     destruct isV; [left; split; [exact KK| exact A]|].
                     exfalso. pose proof (only_kind_sound E1 (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
                  ** destruct isV; [| right; left; split; [exact KK| exact A]].
                     exfalso. pose proof (only_kind_sound E1 (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
            --
               left. rewrite WB'd. split; [left; reflexivity|]. intros b0 Hb0 a Ha Hb. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha. unfold in_iv in Hb.
               subst g'. unfold owned, cstk_block, vstk_block in Hb0. cbn [u_cstk u_vstk u_zone] in Hb0.
               pose proof (disj_cv g2 LB O2) as DCV. unfold rdisj in DCV.
               pose proof ZV' as (_ & _ & Z3' & _).
               subst V2. destruct isV; cbn [u_cstk u_vstk] in Hb0; rewrite VNB in Hb0; injection V2Bb as VB1 VB2; rewrite VB1, VB2 in DCV;
                 destruct Hb0 as [<-|[<-|Hc]]; cbn [fst snd] in Hb.
               ++ clear - DCV Ha Hb. lia.
               ++ exact (DISJ_BN a Hb Ha).
               ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_vc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
                  unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
               ++ exact (DISJ_BN a Hb Ha).
               ++ clear - DCV Ha Hb. lia.
               ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_cc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
                  unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
            --
               right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_BLOCK; clear; lia|].
               unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. rewrite KDv.
               destruct isV; [right; left| left]; (split; [reflexivity|]); rewrite VN1, VN6, VN7; subst NT; clear - L16; lia.
          *
            destruct M2 as (M21 & M22 & M23 & M24 & M25 & M26). unfold mem_ok. subst g'. cbn [u_levels u_cstk u_vstk u_zone u_root u_vis]. change (ms_mem ms') with M'. fold bm'.
            unfold V2 in V2B. unfold V2 in V2SZ.
            split; [| split; [| split; [| split; [exact M24| split; [exact M25| exact M26]]]]].
            -- destruct isV; [exact M21|]. cbn in V2B. rewrite VN1. apply (cstk_at_shift _ bm' bm' Bz Nz); [| rewrite <- V2B; exact M21].
               intros i Hi. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
            -- intros NN. destruct isV; [| exact (M22 NN)]. cbn in V2B. rewrite VN1. pose proof (M22 NN) as X. rewrite V2B in X. unfold u64_at in X |- *.
               rewrite (rdZ_shift bm' bm' 8 Bz Nz); [exact X|]. intros i Hi. apply COPY. clear - Hi L16. lia.
            -- destruct isV; [| exact M23]. cbn in V2B. rewrite VN1. apply (vstk_at_shift _ bm' bm' (Bz + 8) (Nz + 8)); [| rewrite <- V2B; exact M23].
               intros i Hi. rewrite <- !Z.add_assoc. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
          *
            split; [intros X; discriminate X|]. destruct AX2 as [AX2 SE2].
            assert (NP : forall w, In w (map (wden E1) ws') -> pot_win w -> In w (map (wden E1) ws)).
            { intros w Hw (K0 & _). apply in_map_iff in Hw as (x & <- & Hx). destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
              - apply in_map. exact Hx'.
              - exfalso. rewrite WB'd in K0. cbn [w_kind] in K0. unfold HeapOp.K_BLOCK, K_STACK in K0. lia.
              - exfalso. rewrite WNTd in K0. cbn [w_kind] in K0. unfold KD, G6RegrowAC.KD, K_STACK in K0.
                destruct isV; [change (to_Z 3%uint63) with 3 in K0| change (to_Z 2%uint63) with 2 in K0]; lia. }
            split; [exact (acct_pot_ws _ _ _ _ _ AX2 NP)|].

            change (u_zone g') with (u_zone g2).
            apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE2|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
            destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
            -- apply in_map. exact Hx'.
            -- exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. lia.
            -- exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold KD, G6RegrowAC.KD, Seal.K_TWIN in K9.

               destruct isV; [change (to_Z 3%uint63) with 3 in K9| change (to_Z 2%uint63) with 2 in K9]; lia.
      -
        intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
        apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws') _ a (mk_args_sound E1 1%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
        assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
        { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
        split.
        + destruct (in_ws_dec (map (wden E1) ws) a) as [IW|NIW].
          * right. apply (proj1 (in_ws_map_iff E1 ws a)) in IW as (w & Hw & Hin).
            destruct (win3_eqb w wN) eqn:QN; [| destruct (win3_eqb w wT) eqn:QT].
            -- apply win3_eqb_eq in QN. subst w. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs.
               split; [exact FN|]. rewrite WNd1 in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. unfold inR. rewrite EVN1, LON', HIN'. fold Nz. clear - Hin. lia.
            -- apply win3_eqb_eq in QT. subst w. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
               split; [exact FT|]. rewrite WTd1 in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin.
               unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. clear - Hin. lia.
            -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
               exact Hin.
          * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))). auto.
        + intros k r [H1|[H1|[]]] IR; injection H1 as <- <-.
          * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
            unfold inR in IR. rewrite NTV in IR. change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR.
            rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 16%uint63) with 16 in IR. alia.
          * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
            unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
      -
        assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
        assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 8))))) = Nz + (L - 8)).
        { rewrite (G1.den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
        constructor.
        { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
        constructor.
        { cbn [fact_holds]. rewrite Db', De'. subst NT. alia. }
        constructor.
        { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
        constructor.
        {
          cbn [fact_holds]. apply bv_eq. rewrite !G1.den_VAlu. cbn [alu64 alu]. rewrite !bv_sub_unsigned, !wrap64, De', Db'.
          assert (DVE1 : bv_unsigned (den E1 (VP kT (wlit 8))) = Tz + 8).
          { rewrite (G1.den_VP_nowrap E1 kT (wlit 8)); rewrite EVT1, wlit_ok; change (to_Z 8%uint63) with 8; fold Tz; [reflexivity| exact (proj2 RTr)]. }
          rewrite DVE1, (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. fold Bz. subst NT. f_equal. alia. }
        apply Forall_app. split.
        + apply (G4.anchor_facts_sound E1 fs kN (L - 8) (L - 8) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
        + rewrite ALN. constructor; [| constructor]. cbn [fact_holds]. rewrite NTV. change (2 ^ to_Z 3%uint63) with 8. subst NT.
          replace (Nz + L - 8) with (Nz + (L - 8)) by alia. rewrite Z.add_mod, NZ8, Z.add_0_l, Z.mod_mod by lia.
          apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 1). lia.
    }
Qed.

Theorem g6r_sound : contract_sound segs OPS MP PB (g6r_contract SRCPAT isV MEMCPY_PC).
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [g6r_contract c_apply c_pc] in HAP, Hpc.
  unfold g6r_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:AP; [|discriminate].
  destruct (PrimInt63.eqb mdi 1 && fresh_ok (sink st st1 r)) eqn:MDF; [|discriminate].
  apply andb_prop in MDF as [MD FRS]. apply Uint63.eqb_correct in MD. subst mdi.
  exact (regrow_sound st r hargs wnl st1 aw ws ca sts K E ms model Hpc TO AP FRS HAP HS0 HMP HPB Hk).
Qed.
End Sound.
End G6RegrowA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GUnp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GWin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G4 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G1 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G6A.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsKeep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.LiaFast.
Import Actr.TwinB.
Import G6RegrowAC.TwinB.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW CtrLib CtrFX.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Import G6A G6RegrowAC.TwinB.G6RegrowAC.

Module G6RegrowA.
Ltac is_arith T :=
  lazymatch T with
  | (@eq Z _ _) => idtac | (not (@eq Z _ _)) => idtac
  | Z.le _ _ => idtac | Z.lt _ _ => idtac | Z.ge _ _ => idtac | Z.gt _ _ => idtac
  | (_ /\ _) => idtac | (_ \/ _) => idtac
  | _ => fail
  end.
Ltac revert_arith :=
  repeat match goal with
         | H : ?T |- _ => tryif is_arith T then revert H else fail
         end.
Ltac alia := revert_arith; let K := fresh "aliaK" in pose proof I as K; clear - K; intros; unfold two64, two63, two62Z in *; lia.
Ltac inlist := cbn [In]; repeat first [left; reflexivity | right].

Lemma acall_pre_inv : forall room unw st r hargs wnl st1,
  ActrA.acall_pre room unw st = Some (r, hargs, wnl, st1) ->
  call_pre st = Some r /\ exists R', st1 = setregs st R'.
Proof.
  intros room unw st r hargs wnl st1 H. unfold ActrA.acall_pre in H.
  destruct (call_pre st) as [r0|] eqn:CP; [|discriminate].
  destruct (getr st X4) as [tp| | | | | | | | | |]; try discriminate.
  destruct (ActrA.aheap_windows st) as [[ha wl0]|]; [|discriminate].
  match type of H with (if ?c then _ else _) = _ => destruct c; [|discriminate] end.
  destruct (ActrA.forget_stack_below_sp_g st) as [s1|] eqn:FS; [|discriminate]. injection H as <- <- <- <-.
  split; [reflexivity|].
  unfold ActrA.forget_stack_below_sp_g in FS. destruct (ActrA.sp_region st) as [[[k off] rr]|]; [|discriminate].
  destruct (okey off) as [ksp|]; [|discriminate]. injection FS as <-. eexists. reflexivity.
Qed.

Lemma sink_fields : forall st R' r,
  let stS := sink st (setregs st R') r in
  s_facts stS = s_facts st /\ s_ops stS = s_ops st /\ s_priv stS = s_priv st /\ s_next stS = PrimInt63.add (s_next st) 15 /\
  getr stS X10 = getr st X10 /\ s_pc stS = r.
Proof.
  intros st R' r stS. subst stS. unfold sink.
  pose proof (setpc_fields (setr (clobber (setregs st R')) X10 (getr st X10)) r) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9).
  pose proof (setr_fields (clobber (setregs st R')) X10 (getr st X10)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
  pose proof (clobber_fields (setregs st R')) as (C1 & C2 & C3 & C4 & C5 & C6 & C7 & C8).
  pose proof (setregs_fields st R') as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9).
  rewrite P5, Y5, C5, Z6, P6, Y6, C6, Z7, P7, Y7, C7, Z8, P8, Y8, C8, Z9, P9.
  repeat split.
Qed.

Lemma cells_from_sound : forall r L, 0 <= L -> L mod 8 = 0 -> IMap.bst (rg_cells r) -> cells_from r L = true ->
  forall g gr c i, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> 0 <= to_Z (c_idx c) -> 0 <= i -> L <= 8 * keyZ g + to_Z (c_idx c) + i.
Proof.
  intros r L L0 L8 B H g gr c i Hf Hc Hidx Hi. unfold cells_from in H.
  pose proof (proj1 (IMap.forallb_inb _ _) H g gr (proj1 (IMap.find_inb g gr _ B) Hf)) as X. cbn beta in X. apply Z.leb_le in X.
  pose proof (Z.div_mod L 8 ltac:(lia)) as DM. rewrite L8 in DM. unfold St.keyZ in *. lia.
Qed.

Lemma regrow_geom : forall (isV : bool) E (fs : list fact) g wsZ kB kT oc,
  let V := if isV then u_vstk g else u_cstk g in
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs -> pure_ok g -> wins_ok 1 g wsZ ->
  v_begin V = bv_unsigned (den E (VP kB wzero)) -> v_end V = bv_unsigned (den E (VP kT (wlit 8%uint63))) -> v_capend V = bv_unsigned (den E (VP kB oc)) ->
  implied fs (FULe (VP kT (wlit 8%uint63)) (VP kB oc)) = true -> implied fs (FULe (VP kB oc) (VP kT (wlit 8%uint63))) = true ->
  wt oc = false -> 16 <= w2Z oc -> w2Z oc < 1099511627776 ->
  In (Win (bv_unsigned (ev E kT)) 8 (if isV then K_VTOP else K_CTOP)) wsZ ->
  vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\
  v_begin V = bv_unsigned (ev E kB) /\ v_end V = bv_unsigned (ev E kT) + 8 /\ v_capend V = bv_unsigned (ev E kB) + w2Z oc /\
  bv_unsigned (den E (VP kT (wlit 8%uint63))) = bv_unsigned (ev E kT) + 8 /\ bv_unsigned (den E (VP kB oc)) = bv_unsigned (ev E kB) + w2Z oc /\
  w2Z oc = 8 * v_cap V /\ v_size V = v_cap V /\ bv_unsigned (ev E kT) + 8 = bv_unsigned (ev E kB) + w2Z oc /\ 32 <= v_cap V /\
  In (v_begin V, v_bytes V) (owned g) /\ v_size V = (if isV then u_D g + 1 else u_D g).
Proof.
  intros isV E fs g wsZ kB kT oc V Pz0 Pfacts0 P Wk LVB LVE LVC IMP1 IMP2 OCT L16 L40 RT.
  pose proof (pf g P) as (VC & EC & SC & VV & EV8 & SV' & LV & LA & ZV).
  pose proof P as (_ & _ & _ & CC & _ & _ & _ & CV & _ & DLIM & _ & _).
  assert (VFACTS : vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\ In (v_begin V, v_bytes V) (owned g) /\ v_size V = (if isV then u_D g + 1 else u_D g)).
  { subst V. destruct isV.
    - split; [exact VV|]. split; [exact EV8|]. split; [exact CV|]. split; [exact (owned_vstk g)| exact SV'].
    - split; [exact VC|]. split; [exact EC|]. split; [exact CC|]. split; [exact (owned_cstk g)| exact SC]. }
  destruct VFACTS as (VVAL & VELT & VCAP & VOWN & VSZ).
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (L := w2Z oc) in *.
  pose proof (cap32_pos _ VCAP) as CAP32. unfold EMBED_STACK in CAP32.

  assert (RT' : Tz + 8 < two64).
  { pose proof (proj1 (Forall_forall _ _) Wk _ RT) as X. cbn [w_kind] in X.
    pose proof (bv_unsigned_in_range 64 (den E (VP kB oc))) as RC. rewrite bv_modulus_64 in RC.
    destruct (X ltac:(destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_STACK; lia)) as [[[KD|KD] _]|[_ SO]].
    - exfalso. destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_BLOCK in KD; lia.
    - exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_GHOST in KD; lia.
    - unfold sub_ok in SO. cbv zeta in SO. cbn [w_kind w_lo w_len] in SO. subst V.
      destruct SO as [(KK & _ & _ & E5)|[(KK & _ & _ & E5)|[(KK & _)|(KK & _)]]].
      + destruct isV; [exfalso; unfold K_VTOP, K_CTOP in KK; lia|]. rewrite LVC in E5. clear - E5 RC. unfold two64 in *. lia.
      + destruct isV; [| exfalso; unfold K_VTOP, K_CTOP in KK; lia]. rewrite LVC in E5. clear - E5 RC. unfold two64 in *. lia.
      + exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_SLOT in KK; lia.
      + exfalso. destruct isV; unfold K_VTOP, K_CTOP, K_ZONE in KK; lia. }
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in LVB. fold Bz in LVB.
  assert (DVE : bv_unsigned (den E (VP kT (wlit 8%uint63))) = Tz + 8).
  { apply G1.den_VP_nowrap. rewrite wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. exact RT'. }
  rewrite DVE in LVE.
  pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as IM1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as IM2.
  cbn [fact_holds] in IM1, IM2. rewrite DVE in IM1, IM2.
  assert (VCE : v_capend V = Bz + 8 * v_cap V) by (unfold v_capend; rewrite VELT, LVB; reflexivity).
  assert (VEN : v_end V = Bz + 8 * v_size V) by (unfold v_end; rewrite VELT, LVB; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.
  pose proof (w2Z_range oc) as ROC. fold L in ROC.
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { assert (DM : bv_unsigned (den E (VP kB oc)) = (Bz + L) mod two64) by (cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wrap64; reflexivity).
    destruct (Z_lt_le_dec (Bz + L) two64) as [LT2|GE2].
    - rewrite Z.mod_small in DM by (clear - LT2 RB ROC; lia). exact DM.
    - exfalso. rewrite <- (Z.mod_unique (Bz + L) two64 1 (Bz + L - two64)) in DM by (clear - GE2 RB ROC L40; unfold two64 in *; lia).
      rewrite VCE, DM in LVC. clear - LVC CAP32 L40 RB. unfold two64 in *. lia. }
  rewrite DVC in LVC, IM1, IM2.
  split; [exact VVAL|]. split; [exact VELT|]. split; [exact VCAP|]. split; [exact LVB|]. split; [exact LVE|]. split; [exact LVC|]. split; [exact DVE|]. split; [exact DVC|].
  split; [clear - VCE LVC; lia|]. split; [clear - VEN LVE VCE LVC IM1 IM2; lia|]. split; [clear - IM1 IM2; lia|]. split; [exact CAP32|]. split; [exact VOWN| exact VSZ].
Qed.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable isV : bool.
Variable MEMCPY_PC : int.

Definition KD : int := G6RegrowAC.TwinB.G6RegrowAC.KD isV.

Hypothesis AVECCOPY : forall st (K : TSet) E ms mo r hargs wnl st1 ka ra wlena kb nsv nZ md aw ws ca,
  st_ok segs OPS E st ms mo -> MP mo -> s_pc st = MEMCPY_PC ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) ->
  bv_unsigned (den E (getr st X10)) = bv_unsigned (ev E ka) -> IMap.find ka (s_regs st) = Some ra ->
  rg_bg ra = BGNone -> rg_lo ra = 0%uint63 -> rg_w ra = true ->
  CtrA.win_lookup wnl ka = Some (wlena, wlit 1%uint63) -> ActrA.twin_pat_ok st wnl ka = true ->
  0 < nZ -> nZ <= hiZ E ra -> hiZ E ra <= bv_unsigned (den E wlena) ->
  (forall g gr c i, IMap.find g (rg_cells ra) = Some gr -> In c (g_cells gr) -> 0 <= i < to_Z (c_w c) -> nZ <= 8 * keyZ g + to_Z (c_idx c) + i) ->
  bv_unsigned (den E (getr st X11)) = bv_unsigned (ev E kb) -> bv_unsigned (den E (getr st X12)) = nZ ->
  (bv_unsigned (ev E kb) + nZ <= bv_unsigned (ev E ka) \/ bv_unsigned (ev E ka) + nZ <= bv_unsigned (ev E kb)) ->
  SRCPAT st wnl kb nsv = true -> nZ <= bv_unsigned (den E nsv) ->
  the_op st = Some (md, aw, ws, ca) ->
  (forall LB, cw_holds (unp_cw segs XW) (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' ->
     (forall i, 0 <= i < nZ -> exists b, rb segs (ms_mem ms') (bv_unsigned (ev E ka) + i) = Some b /\ rb segs (ms_mem ms') (bv_unsigned (ev E kb) + i) = Some b /\
                                         rb segs (ms_mem ms) (bv_unsigned (ev E kb) + i) = Some b) ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Lemma regrow_sound : forall st r hargs wnl st1 aw ws ca sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (1%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  regrow SRCPAT isV st (sink st st1 r) wnl aw ws ca = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca sts K E ms model Hpc TO AP FRS HAP HS0 HMP HPB Hk.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  unfold regrow in HAP.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  cbv zeta in HAP. rewrite SF in HAP.
  remember (if isV then vb else cb) as b eqn:EB in HAP. remember (if isV then ve else ce) as e eqn:EE in HAP.
  remember (if isV then vcap else ccap) as cap eqn:ECAP in HAP.
  destruct b as [|kB ob| | | | | | | | |]; try discriminate.
  destruct e as [|kT oe| | | | | | | | |]; try discriminate.
  destruct cap as [|kB' oc| | | | | | | | |]; try discriminate.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs stS)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  destruct (elem_cells isV rT 0) as [topc|] eqn:ETOP; [|discriminate].
  destruct (elem_cells isV rN (Uint63.of_Z (L / 8))) as [newc|] eqn:ENEW; [|discriminate].
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SRCP]. apply andb_prop in COND as [COND VCP].
  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL]. apply andb_prop in COND as [COND NOB].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB]. apply andb_prop in COND as [COND NTB].
  apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [COND L16].
  apply andb_prop in COND as [COND OCT]. apply andb_prop in COND as [COND OE8]. apply andb_prop in COND as [KBB OB0].
  apply Uint63.eqb_correct in KBB. subst kB'.
  apply (proj1 (weqb_ok _ _)) in OB0. subst ob. apply (proj1 (weqb_ok _ _)) in OE8. subst oe. apply negb_true_iff in OCT.
  apply Z.leb_le in L16. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0.
  apply G1.neqb_neq in NNT. apply G1.neqb_neq in NNB. apply G1.neqb_neq in NTB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply G1.existsb_win_In in EXN. apply G1.existsb_win_In in EXT.
  apply andb_prop in COND2 as [COND2 WT]. apply andb_prop in COND2 as [COND2 HIT]. apply andb_prop in COND2 as [COND2 LOT].
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN. apply Uint63.eqb_correct in LOT. apply sv_eqb_eq in HIT.

  destruct (IMap.find kN (s_regs st)) as [ra|] eqn:FNst; [|discriminate VCP].
  destruct (CtrA.win_lookup wnl kN) as [[wlena kda]|] eqn:WLK; [|discriminate VCP].
  apply andb_prop in VCP as [VCP PATa]. apply andb_prop in VCP as [VCP KDa]. apply andb_prop in VCP as [VCP WLa]. apply andb_prop in VCP as [VCP CFa]. apply andb_prop in VCP as [VCP HIa].
  apply andb_prop in VCP as [VCP Wa]. apply andb_prop in VCP as [BGa LOa].
  apply Uint63.eqb_correct in LOa. apply sv_eqb_eq in HIa. apply sv_eqb_eq in WLa. apply (proj1 (weqb_ok _ _)) in KDa. subst wlena kda.
  assert (BGa' : rg_bg ra = BGNone) by (destruct (rg_bg ra); try discriminate BGa; reflexivity).
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & rav & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.
  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pcov0 Pminv0].
  set (m := ms_mem ms).

  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  change (G6RegrowAC.TwinB.G6RegrowAC.KD isV) with KD in *.
  set (wT := top_win kT 8 KD) in *.
  assert (KDv : to_Z KD = (if isV then K_VTOP else K_CTOP)) by (unfold KD, G6RegrowAC.TwinB.G6RegrowAC.KD; destruct isV; reflexivity).
  assert (WTd : forall E0, wden E0 wT = Win (bv_unsigned (ev E0 kT)) 8 (if isV then K_VTOP else K_CTOP)) by (intros E0; subst wT; rewrite top_win_den, KDv; reflexivity).
  assert (L40' : w2Z oc < 1099511627776) by exact L40.

  assert (GEOM : forall E0 u0 g0, ev E0 0%uint63 = Z_to_bv 64 0 -> facts_hold E0 fs ->
            decode_uc (map (den E0) [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]) = Some u0 ->
            link u0 g0 -> pure_ok g0 -> wins_ok 1 g0 (map (wden E0) ws) ->
            let V := if isV then u_vstk g0 else u_cstk g0 in
            vec_valid V /\ v_elt V = 8 /\ cap32_b (v_cap V) = true /\
            v_begin V = bv_unsigned (ev E0 kB) /\ v_end V = bv_unsigned (ev E0 kT) + 8 /\ v_capend V = bv_unsigned (ev E0 kB) + w2Z oc /\
            bv_unsigned (den E0 (VP kT (wlit 8%uint63))) = bv_unsigned (ev E0 kT) + 8 /\ bv_unsigned (den E0 (VP kB oc)) = bv_unsigned (ev E0 kB) + w2Z oc /\
            w2Z oc = 8 * v_cap V /\ v_size V = v_cap V /\ bv_unsigned (ev E0 kT) + 8 = bv_unsigned (ev E0 kB) + w2Z oc /\ 32 <= v_cap V /\
            In (v_begin V, v_bytes V) (owned g0) /\ v_size V = (if isV then u_D g0 + 1 else u_D g0)).
  { intros E0 u0 g0 Pz Pf DU LK0 P0 Wk0. cbn [map decode_uc] in DU. injection DU as <-.
    pose proof LK0 as (Lroot & Lcb & Lce & Lccap & Lvb & Lve & Lvcap & Lzp & Lzf & Lc0 & LD).
    cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in Lroot, Lcb, Lce, Lccap, Lvb, Lve, Lvcap, Lzp, Lzf, Lc0, LD.
    apply (regrow_geom isV E0 fs g0 (map (wden E0) ws) kB kT oc Pz Pf P0 Wk0); try assumption.
    - destruct isV; [rewrite EB; exact Lvb| rewrite EB; exact Lcb].
    - destruct isV; [rewrite EE; exact Lve| rewrite EE; exact Lce].
    - destruct isV; [rewrite ECAP; exact Lvcap| rewrite ECAP; exact Lccap].
    - rewrite <- (WTd E0). apply in_map. exact EXT. }

  pose proof HC as HCm.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & LK & P & O & Wk & M & CS0). clear CS0.
  destruct (GEOM E _ g Pz0 Pfacts0 eq_refl LK P Wk) as (VVAL & VELT & VCAP & LVB & LVE & LVC & DVE & DVC & LCAP & SZC & TZ8 & CAP32 & VOWN & VSZ).
  set (V := if isV then u_vstk g else u_cstk g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.
  fold L in LVC, DVC, LCAP, TZ8.
  pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  assert (VBY : v_bytes V = 8 * v_cap V) by (unfold v_bytes; rewrite VELT; reflexivity).

  pose proof (Preg0 kN ra FNst) as ROKa.
  assert (LOa' : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity).
  pose proof (w2Z_range oc) as ROC. fold L in ROC. unfold two40Z in L40.
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. alia. }
  assert (HIa' : hiZ E ra = 2 * L) by (unfold hiZ; rewrite HIa; cbn [den]; rewrite wbv_unsigned; exact L2w).
  pose proof (ro_range _ _ _ _ _ _ ROKa KN0) as RNr. rewrite LOa', HIa' in RNr. fold Nz in RNr.
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RBz. rewrite bv_modulus_64 in RBz. fold Bz in RBz.

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ8. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite G1.den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (G1.den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + L - L) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz (2 * L) HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) (v_bytes V) L); [| alia| alia| rewrite VBY; alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. rewrite LVB. exact Hb. }

  apply (AVECCOPY st K E ms model (wl rav) hargs wnl (setregs st R') kN ra (VL (wlit (Uint63.of_Z (2 * L)))) kB (VL oc) L 1%uint63 aw ws
           [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] HS0 HMP Hpc AP).
  - fold dx. rewrite DXV. reflexivity.
  - exact FNst.
  - exact BGa'.
  - exact LOa.
  - exact Wa.
  - exact WLK.
  - exact PATa.
  - alia.
  - rewrite HIa'. alia.
  - rewrite HIa'. cbn [den]. rewrite wbv_unsigned, L2w. apply Z.le_refl.
  - intros g0 gr cc i Hf Hc Hi. apply (cells_from_sound ra L ltac:(alia) L8 (ro_bst _ _ _ _ _ _ ROKa) CFa g0 gr cc i Hf Hc); [| lia].
    pose proof (Uint63.to_Z_bounded (c_idx cc)). lia.
  - rewrite X11B. exact (den_VP0 E kB wzero (weqb_refl _)).
  - fold n12. exact N12V.
  - fold Bz Nz. clear - SEP. lia.
  - exact SRCP.
  - cbn [den]. rewrite wbv_unsigned. fold L. apply Z.le_refl.
  - exact TO.
  -
    intros LB' HC'. change (to_Z 1%uint63) with 1 in HC'.
    cbn [cw_holds unp_cw] in HC'. unfold cw_unp_holds in HC'. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC'. cbn [map decode_uc] in HC'.
    destruct HC' as (g' & LK' & P' & O' & Wk' & _).
    destruct (GEOM E _ g' Pz0 Pfacts0 eq_refl LK' P' Wk') as (_ & VELT' & _ & LVB' & _ & _ & _ & _ & LCAP' & _ & _ & _ & VOWN' & _).
    cbn [den]. rewrite wbv_unsigned. fold L Bz. fold L in LCAP'. fold Bz in LVB'.
    pose proof VOWN' as OW'. rewrite LVB' in OW'. unfold v_bytes in OW'. rewrite VELT' in OW'. rewrite <- LCAP' in OW'.
    split; [exact (proj1 O' _ OW')|].

    intros w0 Hw0 KD0 a Ha0 Hb0.
    destruct (proj1 (Forall_forall _ _) Wk' w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[NB SOK]].
    + exact (DJ _ OW' a Ha0 Hb0).
    + exfalso. destruct KD0 as [KB1|KG]; [exact (NB KB1)|]. unfold sub_ok in SOK. cbv zeta in SOK.
      destruct SOK as [(KK & _)|[(KK & _)|[(KK & _)|(KK & _)]]]; unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_GHOST in *; lia.
  -
    intros E' ms' mo' HX' HMP' HSS COPYB.
    {
    clear DEC.
    clear g LK P O Wk M VVAL VELT VCAP LVB LVE LVC DVE DVC LCAP SZC TZ8 CAP32 VOWN VSZ VV1 VV2 VV3 VV4 VBY DISJN SEP HA WF HCm V LB.
    set (nT := s_next stS) in *.
    destruct (fresh_ok_inv stS FRS) as (VBS & NPOSS & N62S). fold nT in VBS, NPOSS, N62S.
    set (M' := ms_mem ms') in *.
    assert (TZ15 : to_Z nT = to_Z n0 + 15).
    { subst nT. rewrite SN. fold n0. rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia). reflexivity. }
    assert (TZ16 : to_Z (PrimInt63.add nT 1) = to_Z n0 + 16).
    { rewrite add_Z by (change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; alia). rewrite TZ15. change (to_Z 1%uint63) with 1. lia. }
    set (NT := Nz + L - 8).
    set (Fv := fun _ : Z => Z_to_bv 64 NT). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
    set (E1 := env_above E' nT Fv Gv).
    assert (HX1 : env_ext nT E' E1) by (subst E1; apply env_above_ext).
    assert (HX : env_ext n0 E E1) by (apply (env_ext_trans n0 nT E E' E1); [lia| exact HX'| exact HX1]).
    assert (ENT : ev E1 nT = Z_to_bv 64 NT) by (subst E1; rewrite ev_above by lia; reflexivity).

    assert (INCA : forall v, In v [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] -> In v (op_args o)).
    { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
    assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
    { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
      repeat split; right; right; right; apply in_app_iff; left; assumption. }
    assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
    { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    assert (INb : In (VP kB wzero) (op_args o)) by (rewrite EB; destruct isV; apply INCA; inlist).
    assert (INe : In (VP kT (wlit 8)) (op_args o)) by (rewrite EE; destruct isV; apply INCA; inlist).
    assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero INb).
    assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 8) INe).
    assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
    assert (EVN1 : ev E1 kN = ev E kN) by exact (proj1 (proj2 HX kN KN_LT)).
    assert (EVB1 : ev E1 kB = ev E kB) by exact (proj1 (proj2 HX kB KB_LT)).
    assert (EVT1 : ev E1 kT = ev E kT) by exact (proj1 (proj2 HX kT KT_LT)).
    assert (NTV : bv_unsigned (ev E1 nT) = NT).
    { rewrite ENT, Z_to_bv_unsigned. apply bv_wrap_small. rewrite bv_modulus_64. subst NT. alia. }
    pose proof (st_ok_reval segs OPS nT E' E1 HX1 stS ms' mo' NPOSS VBS HSS) as HSE1.
    pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 Pbst1 Preg1 Pdisj1 _ Pfacts1 Pops1 _ _ _ _].
    rewrite SF in Pfacts1. fold fs in Pfacts1.

    assert (DDX1 : den E1 dx = den E1 (VP kN wzero)).
    { rewrite (den_reval n0 E E1 HX dx VBdx), DXV. rewrite <- EVN1. apply bv_eq. symmetry. exact (den_VP0 E1 kN wzero (weqb_refl _)). }
    pose proof (setreg_sound segs OPS E1 stS _ mo' X10 (VP kN wzero) HSE1 ltac:(discriminate) ltac:(rewrite SX10; exact DDX1)) as HS3.
    pose proof (repl_regs_sound segs OPS kept_r5 dx (VP kN wzero) E1 _ _ mo' HS3 ltac:(cbn; intuition discriminate) DDX1) as HS5.
    apply (Hk st' (or_introl eq_refl) E1 ms' mo' HX HMP').
    set (st5 := repl_regs kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero))) in *.
    pose proof (repl_regs_fields kept_r5 dx (VP kN wzero) (setr stS X10 (VP kN wzero))) as (Q1 & Q2 & Q3 & Q4 & Q5 & Q6 & Q7 & Q8).
    pose proof (setr_fields stS X10 (VP kN wzero)) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6 & Y7 & Y8).
    assert (F5ops : s_ops st5 = opre ++ o :: opost) by (subst st5; rewrite Q6, Y6, SO; exact OPSEQ).
    assert (F5regs : s_regs st5 = s_regs stS) by (subst st5; rewrite Q4, Y4; reflexivity).
    assert (F5pv : s_priv st5 = s_priv st) by (subst st5; rewrite Q7, Y7; exact SPV).
    assert (F5fs : s_facts st5 = fs) by (subst st5; rewrite Q5, Y5; exact SF).
    subst st'.

    pose proof (ops_hold_in OPS _ _ _ _ o Pops1 ltac:(rewrite SO; exact (op_in_In st o OPS1))) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA' & WF & HC). change (ms_mem ms') with M' in HA', HC.
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
    cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
    destruct HC as (g2 & LK2 & P2 & O2 & Wk2 & M2 & _ & AX2).
    destruct (GEOM E1 _ g2 Pz1 Pfacts1 eq_refl LK2 P2 Wk2) as (V2VAL & V2ELT & V2CAP & V2B & V2E & V2C & DVE & DVC & LCAP2 & V2SC & TZ8 & CAP32 & V2OWN & V2SZ).
    rewrite EVB1 in V2B, V2C, DVC, TZ8. rewrite EVT1 in V2E, DVE, TZ8. fold L Bz Tz in V2B, V2E, V2C, DVE, DVC, LCAP2, TZ8.
    pose proof LK2 as (L2root & L2cb & L2ce & L2ccap & L2vb & L2ve & L2vcap & L2zp & L2zf & L2c0 & L2D).
    cbn [c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1] in L2root, L2cb, L2ce, L2ccap, L2vb, L2ve, L2vcap, L2zp, L2zf, L2c0, L2D.
    pose proof (pf g2 P2) as (VC' & EC' & SC' & VV' & EV8' & SV'' & LV' & LA' & ZV').
    pose proof P2 as (_ & _ & _ & CC' & _ & _ & _ & CV' & _ & DLIM' & _ & _).
    set (V2 := if isV then u_vstk g2 else u_cstk g2) in *.
    set (bm' := bmem_of segs M') in *.
    pose proof V2VAL as (W1 & W2 & W3 & W4).
    assert (V2BY : v_bytes V2 = L) by (unfold v_bytes; rewrite V2ELT; alia).
    pose proof (proj1 O2 _ V2OWN) as V2LB. rewrite V2BY in V2LB, V2OWN.

    pose proof (Preg1 kN rN FN) as ROKN. pose proof (Preg1 kT rT FT) as ROKT.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
    assert (HIN' : hiZ E1 rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
    assert (HIT' : hiZ E1 rT = 8) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT', EVT1 in RTr. fold Tz in RTr.
    assert (WNd1 : wden E1 wN = Win Nz (2 * L) HeapOp.K_BLOCK) by exact (WNd E1 EVN1).
    assert (WTd1 : wden E1 wT = Win Tz 8 (to_Z KD)) by (rewrite (WTd E1), EVT1, KDv; reflexivity).
    assert (DISJN : forall ob, In ob (owned g2) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk2 _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
    { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
      intros a Ha Hb. apply (DISJN _ V2OWN a Ha). unfold in_iv. cbn [fst snd]. rewrite V2B. exact Hb. }
    assert (BYN : forall a, Nz <= a < Nz + 2 * L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (bytes_of_region segs _ E1 M' kN rN a ROKN KN0). rewrite LON', HIN', EVN1. fold Nz. alia. }

    assert (NLB : In (Nz, 2 * L) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KDx _]|[[_ IN]|[KDx _]]]).
      - cbn in KDx. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KDx. discriminate KDx.
      - exact IN.
      - cbn in KDx. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KDx. exfalso. clear - KDx. lia. }

    assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
    { intros i Hi. destruct (COPYB i Hi) as (b0 & C1 & C2 & _). fold Nz Bz in C1, C2. rewrite C1, C2. reflexivity. }
    assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
    { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite (RBC i Hi). reflexivity. }
    pose proof (bv_unsigned_in_range 64 (ev E kN)) as RNz. rewrite bv_modulus_64 in RNz. fold Nz in RNz.
    pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr1. rewrite LON', HIN', EVN1 in RNr1. fold Nz in RNr1.

      set (VN := vec_regrow V2 Nz).
      set (g' := mkUnp (u_ctx g2) (u_vis g2) (u_data g2) (u_len g2) (u_levels g2) (if isV then u_cstk g2 else VN) (if isV then VN else u_vstk g2) (u_zone g2)).
      assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V2 /\ v_cap VN = 2 * v_cap V2 /\ v_elt VN = 8 /\ v_bytes VN = 2 * L /\
                    v_end VN = NT + 8 /\ v_capend VN = Nz + 2 * L).
      { subst VN. unfold vec_regrow, v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite V2ELT, V2SC. subst NT. repeat split; alia. }
      destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
      assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
      assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
      assert (TZB : Tz = Bz + L - 8) by alia.
      assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply G1.neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
      assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

      assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
      { intros a Ha Hb. apply (DISJN _ V2OWN a Ha). unfold in_iv. cbn [fst snd]. rewrite V2B. exact Hb. }

      assert (BYNT : forall a, NT <= a < NT + 16 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
      { intros a Ha. apply BYN. subst NT. alia. }
      assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
      { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ M' mo' _ a HA' V2LB). unfold in_iv. cbn [fst snd]. rewrite V2B. alia. }

      assert (ECINV : forall r gi cs, elem_cells isV r gi = Some cs -> exists gr, IMap.find gi (rg_cells r) = Some gr /\ cs = g_cells gr).
      { intros r gi cs H. unfold elem_cells in H. destruct (IMap.find gi (rg_cells r)) as [gr|]; [|discriminate]. exists gr. split; [reflexivity|].
        destruct isV; destruct (g_cells gr) as [|[i1 w1 v1] [|[i2 w2 v2] [|? ?]]]; try discriminate H;
          match type of H with (if ?c then _ else _) = _ => destruct c; [injection H as <-; reflexivity| discriminate H] end. }
      destruct (ECINV rT 0%uint63 topc ETOP) as (grT & FgrT & ->).
      destruct (ECINV rN (Uint63.of_Z (L / 8)) newc ENEW) as (grN & FgrN & ->).
      assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
      { apply keyZ_of_Z. unfold two62Z. clear - L16 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
      assert (L8E : 8 * (L / 8) = L) by (clear - L8 L16; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
      assert (STOP : slot_ok segs E1 M' Tz (g_cells grT)).
      { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kT rT FT) 0%uint63 grT FgrT) as X. rewrite EVT1 in X. fold Tz in X. change (keyZ 0%uint63) with 0 in X.
        rewrite Z.mul_0_r, Z.add_0_r in X. exact X. }
      assert (SNEW : slot_ok segs E1 M' (Nz + L) (g_cells grN)).
      { pose proof (ro_cells _ _ _ _ _ _ (Preg1 kN rN FN) _ grN FgrN) as X. rewrite EVN1, KEYL, L8E in X. fold Nz in X. exact X. }
      assert (STOP' : slot_ok segs E1 M' NT (g_cells grT)).
      { apply (slot_ok_shift segs E1 M' M' Tz NT _ STOP). intros i Hi. subst NT. rewrite TZB.
        replace (Nz + L - 8 + i) with (Nz + (L - 8 + i)) by alia. rewrite (RBC (L - 8 + i)) by alia. f_equal. alia. }
      assert (SNEW' : slot_ok segs E1 M' (NT + 8) (g_cells grN)).
      { replace (NT + 8) with (Nz + L) by (subst NT; alia). exact SNEW. }
      assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region16 (g_cells grT) (g_cells grN))).
      { apply (region16_ok segs (s_priv st) E1 M' nT _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| exact STOP'| exact SNEW']. }
      destruct (empty_region_ok segs (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
                  ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).

      assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E1) ws) a /\ ~ in_ivs IMGX a).
      { intros a Ha.
        assert (SFE : safe 1 g2 (map (wden E1) ws) a).
        { clear - V2B V2E P2 O2 Ha TZB. subst V2. destruct isV; [apply (safe_vstk 1 g2 LB _ P2 O2)| apply (safe_cstk 1 g2 LB _ P2 O2)]; rewrite V2B, V2E; lia. }
        destruct (owned_byte_props segs IMGX AW _ LB M' mo' 1 g2 _ _ a HA' WF O2 Wk2 V2OWN ltac:(unfold in_iv; cbn [fst snd]; rewrite V2B; alia) SFE) as (_ & NI & NW & _).
        split; [exact NW| exact NI]. }

      set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
      set (wNT := top_win nT 16 KD).
      set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
      set (b' := VP kN wzero). set (e' := VP nT (wlit 8)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
      set (ca' := if isV then [root; cb; ce; ccap; b'; e'; cap'; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]
                  else [root; b'; e'; cap'; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh]).
      assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
      { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
        apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
        split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
      assert (LENws' : Z.of_nat (length ws') < two63).
      { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
      assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
      { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
      assert (WNTd : wden E1 wNT = Win NT 16 (to_Z KD)) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
      assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
      assert (De' : bv_unsigned (den E1 e') = NT + 8).
      { subst e'. rewrite (G1.den_VP_nowrap E1 nT (wlit 8)); rewrite ?wlit_ok, NTV; change (to_Z 8%uint63) with 8; [reflexivity| subst NT; alia]. }
      assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
      { subst cap'. rewrite (G1.den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }
      apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH [kN; kT]
               [(nT, region16 (g_cells grT) (g_cells grN)); (kB, empty_region L)] (mk_args 1%uint63 aw ws' ca') _ (PrimInt63.add nT 1)).
      -   intros k [<-|[<-|[]]]; rewrite F5regs.
        + split; [exact KN0|]. exists rN. split; [exact FN| exact WN].
        + split; [exact KT0|]. exists rT. split; [exact FT| exact WT].
      -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
      -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
      -   intros k r [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
      -   intros k r a [H1|[H1|[]]] IR; injection H1 as <- <-.
        + right. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs. split; [exact FN|].
          unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LON', HIN'. fold Nz.
          change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
          change (to_Z 16%uint63) with 16 in IR. subst NT. alia.
        + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
          destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
          * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))).
            destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
          * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
            split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. alia.
      -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
          unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region16 (g_cells grT) (g_cells grN))) with 0;
          unfold hiZ; cbn [region16 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 16%uint63) with 16; intros [I1 I2].
        + apply (DISJ_BN a); subst NT; alia.
        + apply (DISJ_BN a); subst NT; alia.
      -   rewrite (ho_holds _ _ _ _ _ HOPS).
        exists 1, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
        split; [apply mk_args_sound; exact LENws'|].

        assert (N24 : ~ c24 (2 * L)).
        { destruct (OpsTwin.UOT.cap32_bytes _ V2CAP) as (k2 & Hk2 & E2). unfold c24, C24_LO, C24_HI.
          replace (2 * L) with (256 * 2 ^ (k2 + 1)) by (rewrite Z.pow_add_r by lia; change (2 ^ 1) with 2; lia).
          exact (OpsTwin.UOT.pow2_not_c24 (k2 + 1) ltac:(lia)). }
        assert (WkE1 : wins_ok 1 g2 (map (wden E1) ws)) by exact Wk2.
        split; [apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA');
                apply (UOK.unp_wins_keep_map E1 1 g2 LB ws ws' P2 O2 WkE1);
                [intros x Hx; destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]];
                 [left; exact Hx'
                 |right; right; rewrite WB'd; unfold w_iv; cbn [w_kind w_lo w_len]; split; [reflexivity|];
                  replace (Bz, L) with (v_begin V2, L) by (rewrite V2B; reflexivity); exact V2OWN
                 |right; left; subst wNT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity]
                |intros x Hx; destruct (win3_eqb x wN) eqn:QK1;
                 [right; right; apply win3_eqb_eq in QK1; subst x; rewrite WNd1; cbn [w_kind w_iv w_lo w_len];
                  split; [reflexivity|]; split; [exact NLB| exact N24]|];
                 destruct (win3_eqb x wT) eqn:QK2;
                 [right; left; apply win3_eqb_eq in QK2; subst x; subst wT; apply UOK.kind_sub; unfold KD; destruct isV; vm_compute; reflexivity|];
                 left; subst ws'; apply in_or_app; left; apply filter_In; split; [exact Hx|]; cbv beta; rewrite QK1, QK2; reflexivity]|]. split.
        +
          unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
          destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
          * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
          * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
            right; left. split; [reflexivity|]. rewrite <- V2B. exact V2LB.
          * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
            right; right. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_SUB; alia|].
            exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L16. lia.
        +
          cbn [cw_holds unp_cw]. unfold cw_unp_holds. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb].
          assert (CA' : ca' = [root; (if isV then cb else b'); (if isV then ce else e'); (if isV then ccap else cap');
                               (if isV then b' else vb); (if isV then e' else ve); (if isV then cap' else vcap); zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh])
            by (subst ca'; destruct isV; reflexivity).
          rewrite CA'. cbn [map decode_uc].
          assert (VNV : vec_valid VN).
          { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, V2SC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }
          assert (VNC : cap32_b (v_cap VN) = true).
          { rewrite VN3. unfold cap32_b. apply cap32_double; [exact V2CAP| alia]. }

          assert (DJ2 : forall b, In b (owned g2) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv b a).
          { intros b0 Hb0 a Ha. pose proof (proj1 (Forall_forall _ _) Wk2 _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
            destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
            apply (DJ b0 Hb0 a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
          assert (RDJ2 : forall b, In b (owned g2) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
          { intros b0 Hb0. pose proof (owned_pos g2 P2 b0 Hb0) as PO. unfold rdisj.
            destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
            destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
            exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
            - apply (DJ2 b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
            - apply (DJ2 b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }

          assert (VNB : (v_begin VN, v_bytes VN) = (Nz, 2 * L)) by (rewrite VN1, VN5; reflexivity).
          assert (V2Bb : (v_begin V2, v_bytes V2) = (Bz, L)) by (rewrite V2B, V2BY; reflexivity).

          assert (DLEN2 : u_D g2 = Z.of_nat (length (u_levels g2))) by reflexivity.
          assert (DPOS : 1 <= u_D g2) by (clear - V2SZ V2SC CAP32 LCAP2 DLEN2; destruct isV; lia).
          assert (LNE : u_levels g2 <> []) by (intros X; rewrite X in DLEN2; cbn in DLEN2; alia).
          assert (RLEN : Z.of_nat (length (removelast (u_levels g2))) = u_D g2 - 1).
          { rewrite (removelast_length _ LNE). rewrite Nat2Z.inj_sub by (destruct (u_levels g2); [exfalso; exact (LNE eq_refl)| cbn; lia]). rewrite <- DLEN2. reflexivity. }
          exists g'. split; [| split; [| split; [| split; [| split]]]].
          *
            unfold link. subst g'. cbn [u_root u_vis u_cstk u_vstk u_zone u_levels u_cur_slot c_root c_cb c_ce c_ccap c_vb c_ve c_vcap c_zptr c_zfree c_c0 c_slot c_tD c_restD c_rootT c_n1 c_P1].
            destruct isV; cbn [u_cstk u_vstk];
              rewrite ?Db', ?De', ?Dcap', ?VN1, ?VN6, ?VN7.
            -- split; [exact L2root|]. split; [exact L2cb|]. split; [exact L2ce|]. split; [exact L2ccap|].
               split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
               split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
            -- split; [exact L2root|]. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|].
               split; [exact L2vb|]. split; [exact L2ve|]. split; [exact L2vcap|].
               split; [exact L2zp|]. split; [exact L2zf|]. split; [exact L2c0|]. exact L2D.
          *
            unfold pure_ok. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. unfold u_D. cbn [u_levels]. change (Z.of_nat (length (u_levels g2))) with (u_D g2).
            pose proof P2 as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & A8 & A9 & A10 & A11 & A12).
            clear - A1 A2 A3 A4 A5 A6 A7 A8 A9 A10 A11 A12 VNV VNC VN2 VN4 V2SZ V2.
            destruct isV; subst V2; cbn in V2SZ.
            -- split; [exact A1|]. split; [exact A2|]. split; [exact A3|]. split; [exact A4|]. split; [exact VNV|]. split; [exact VN4|].
               split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
            -- split; [exact VNV|]. split; [exact VN4|]. split; [rewrite VN2; exact V2SZ|]. split; [exact VNC|].
               split; [exact A5|]. split; [exact A6|]. split; [exact A7|]. split; [exact A8|]. split; [exact A9|]. split; [exact A10|]. split; [exact A11| exact A12].
          *

            assert (TIE' : blocks_tied (owned g')).
            { pose proof (own_tied g2 LB O2) as OT.
              pose proof P2 as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & B8 & _).
              pose proof (cap32_pos _ B4) as C32c. pose proof (cap32_pos _ B8) as C32v. unfold EMBED_STACK in C32c, C32v.
              destruct B1 as (_ & SZc & _). destruct B5 as (_ & SZv & _).
              subst g'. unfold blocks_tied, owned, cstk_block, vstk_block. cbn [u_cstk u_vstk u_zone snd].
              unfold v_bytes in OT |- *. rewrite B2, B6 in OT.
              clear - OT B2 B3 B6 B7 C32c C32v SZc SZv V2SZ V2SC LCAP2 VN5 V2.
              unfold v_bytes in VN5. subst V2. destruct isV; cbn [u_cstk u_vstk]; rewrite ?B2, ?B6; unfold v_bytes in VN5; lia. }
            destruct O2 as [OL [OF _]]. unfold own_ok. unfold owned, cstk_block, vstk_block in OL, OF, RDJ2. unfold owned, cstk_block, vstk_block in TIE' |- *.
            subst g'. cbn [u_cstk u_vstk u_zone] in TIE' |- *. subst V2. destruct isV; cbn [u_cstk u_vstk u_zone] in TIE' |- *; rewrite VNB in TIE' |- *; rewrite V2Bb in OL, OF, RDJ2;
              (split; [| split; [| exact TIE']]).
            -- intros b0 [<-|[<-|Hb0]]; [apply OL; left; reflexivity| exact NLB| apply OL; right; right; exact Hb0].
            -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. destruct (FOP_cons _ _ _ F2) as [F3 F4].
                  constructor; [| constructor; [| exact F4]].
                  ** constructor; [apply (proj2 (RDJ2 _ ltac:(left; reflexivity)))|]. exact (Forall_inv_tail F1).
                  ** apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; right; exact Hc))).
            -- intros b0 [<-|[<-|Hb0]]; [exact NLB| apply OL; right; left; reflexivity| apply OL; right; right; exact Hb0].
            -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
                  apply Forall_forall. intros c Hc. apply (proj1 (RDJ2 _ ltac:(right; exact Hc))).
          *
            unfold wins_ok. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
            assert (OWN' : forall b0, In b0 (owned g') -> b0 = (Nz, 2 * L) \/ In b0 (owned g2)).
            { intros b0 Hb0. subst g'. unfold owned, cstk_block, vstk_block in Hb0 |- *. cbn [u_cstk u_vstk u_zone] in Hb0 |- *.
              clear - Hb0 VNB. destruct isV; rewrite VNB in Hb0; cbn [In] in Hb0 |- *;
                destruct Hb0 as [X|[X|X]]; (try (left; symmetry; exact X)); right; tauto. }
            destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
            --
               pose proof (proj1 (forallb_forall _ _) KL x Hx') as KLx. cbn beta iota in KLx. destruct (kind_of x) as [kd|] eqn:KDx; [|discriminate KLx].
               pose proof (kind_of_sound E1 x kd KDx) as WK.

               assert (XN : forall a, in_iv (w_iv (wden E1 x)) a -> ~ (Nz <= a < Nz + 2 * L)).
               { intros a Ha HN. destruct x as [[xlo xlen] xkd]. unfold kind_of in KDx. cbn [snd] in KDx.
                 destruct xkd as [kw| | | | | | | | | |]; try discriminate KDx. destruct (wt kw) eqn:KWT; [discriminate KDx|]. injection KDx as <-.
                 destruct (Z.eq_dec (to_Z (wl kw)) HeapOp.K_BLOCK) as [K1|NK1].
                 -
                   pose proof (proj1 (forallb_forall _ _) OBK _ Hx') as OB. cbn beta iota in OB. rewrite KWT in OB. cbn [orb] in OB.
                   assert (KW1 : PrimInt63.eqb (wl kw) 1 = true) by (apply (proj2 (Uint63.eqb_spec _ _)); apply Uint63.to_Z_inj; rewrite K1; reflexivity).
                   rewrite KW1 in OB. cbn [negb] in OB.
                   destruct xlo as [|kx ox| | | | | | | | |]; try discriminate OB.
                   destruct (PrimInt63.eqb kx kN) eqn:KXN.
                   + apply Uint63.eqb_correct in KXN. subst kx. pose proof (proj1 (forallb_forall _ _) NOA _ Hx') as NO. cbn beta iota in NO. rewrite Uint63.eqb_refl in NO. cbn [negb orb] in NO.
                     apply win3_eqb_eq in NO. exact (NxN NO).
                   + cbn [orb] in OB. apply andb_prop in OB as [OB FND]. apply andb_prop in OB as [OX KX0]. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
                     destruct (IMap.find kx (s_regs stS)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HX0].
                     apply Uint63.eqb_correct in LOX. destruct (decide_ltu fs (VL wzero) (rg_hi rx)) as [[|]|] eqn:DH; try discriminate HX0.
                     pose proof (decide_ltu_sound E1 fs Pfacts1 _ _ _ DH) as HPOS. apply (proj1 (ltu_iff _ _ true)) in HPOS. cbn [den] in HPOS. rewrite wbv_unsigned, wzero_ok in HPOS.
                     apply Uint63.eqb_false_correct in KXN.

                     pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
                     destruct WFx as (_ & _ & _ & [[KS _]|[[_ INx]|[KS _]]]);
                       [rewrite WK in KS; unfold HeapOp.K_STACK, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia| | rewrite WK in KS; unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KS, K1; clear - KS K1; lia].
                     unfold w_iv, wden in INx. cbn [w_lo w_len] in INx. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in INx.
                     unfold wden, w_iv, in_iv in Ha. cbn [w_lo w_len fst snd] in Ha. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in Ha.
                     destruct (Z.eq_dec (bv_unsigned (ev E1 kx)) Nz) as [EQX|NEX].
                     * apply (Pdisj1 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) Nz). unfold loZ, hiZ. rewrite LOX, EQX, LON, HIN. cbn [den]. rewrite wbv_unsigned, L2w.
                       change (keyZ 0%uint63) with 0. rewrite ?EVN1. fold Nz. clear - HPOS L16. lia.
                     * exact (aw_blocks_disj segs IMGX AW _ LB _ M' mo' _ _ a HA' INx NLB ltac:(cbn [fst]; exact NEX) Ha ltac:(unfold in_iv; cbn [fst snd]; exact HN)).
                 -
                   pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')) as WFx.
                   assert (K2 : 2 <= to_Z (wl kw)).
                   { rewrite WK in NS. destruct WFx as (_ & _ & _ & [[KS _]|[[KS _]|[KS _]]]); rewrite WK in KS;
                       unfold HeapOp.K_STACK, HeapOp.K_BLOCK, HeapOp.K_SUB in NS, KS, NK1; clear - NS KS NK1; lia. }
                   pose proof (proj1 (forallb_forall _ _) SWO _ Hx') as SW. cbn beta iota in SW. rewrite KWT in SW. cbn [orb] in SW.
                   destruct (Z.ltb_spec (to_Z (wl kw)) 2); [lia|].
                   apply orb_prop in SW as [SW|SW]; [apply win3_eqb_eq in SW; exact (NxT SW)|].
                   apply orb_prop in SW as [GH|SW].
                   { pose proof (aw_ghost_apart segs IMGX AW _ _ _ _ _ HA') as GA.
                     refine (GA _ _ (in_map (wden E1) _ _ Hx') (in_map (wden E1) _ _ EXN) _ _ a Ha _).
                     - rewrite WK. unfold K_GHOST. apply Z.leb_le in GH. exact GH.
                     - rewrite WNd1. reflexivity.
                     - rewrite WNd1. unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact HN. }
                   destruct xlo as [|kx ox| | | | | | | | |]; try discriminate SW.
                   apply andb_prop in SW as [SW FND]. apply andb_prop in SW as [SW KX0]. apply andb_prop in SW as [KXN OX].
                   apply negb_true_iff in KXN. apply Uint63.eqb_false_correct in KXN. apply (proj1 (weqb_ok _ _)) in OX. subst ox. apply negb_true_iff in KX0.
                   destruct (IMap.find kx (s_regs stS)) as [rx|] eqn:FX; [|discriminate FND]. apply andb_prop in FND as [LOX HXR]. apply Uint63.eqb_correct in LOX. apply sv_eqb_eq in HXR.
                   unfold wden, w_iv, in_iv in Ha. rewrite (den_VP0 E1 kx wzero (weqb_refl _)) in Ha. cbn [w_lo w_len fst snd] in Ha.
                   apply (Pdisj1 kx rx kN rN FX FN KXN KX0 KN0 (or_intror WN) a). unfold loZ, hiZ. rewrite LOX, HXR, LON, HIN.
                   change (den E1 (VL (wlit (Uint63.of_Z (2 * L))))) with (wbv (wlit (Uint63.of_Z (2 * L)))). rewrite wbv_unsigned, L2w.
                   change (keyZ 0%uint63) with 0. rewrite ?EVN1. fold Nz. alia. }
               destruct (proj1 (Forall_forall _ _) Wk2 (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDJ DJ]|[NB SOK]].
               ++ left. split; [exact KDJ|]. intros b0 Hb0 a Ha Hb. destruct (OWN' b0 Hb0) as [->|Hb2]; [| exact (DJ b0 Hb2 a Ha Hb)].
                  apply (XN a Ha). unfold in_iv in Hb. cbn [fst snd] in Hb. exact Hb.
               ++ right. split; [exact NB|]. unfold sub_ok in SOK |- *. cbv zeta in SOK |- *. subst g'. cbn [u_cstk u_vstk u_levels u_zone].
                  destruct SOK as [(KK & A)|[(KK & A)|[A|A]]]; [| | right; right; left; exact A| right; right; right; exact A].
                  **
                     destruct isV; [left; split; [exact KK| exact A]|].
                     exfalso. pose proof (only_kind_sound E1 (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
                  ** destruct isV; [| right; left; split; [exact KK| exact A]].
                     exfalso. pose proof (only_kind_sound E1 (to_Z KD) _ ws OKT x Hx' ltac:(rewrite KK, KDv; reflexivity)) as X. injection X as <-. exact (NxT eq_refl).
            --
               left. rewrite WB'd. split; [left; reflexivity|]. intros b0 Hb0 a Ha Hb. unfold in_iv, w_iv in Ha. cbn [w_lo w_len fst snd] in Ha. unfold in_iv in Hb.
               subst g'. unfold owned, cstk_block, vstk_block in Hb0. cbn [u_cstk u_vstk u_zone] in Hb0.
               pose proof (disj_cv g2 LB O2) as DCV. unfold rdisj in DCV.
               pose proof ZV' as (_ & _ & Z3' & _).
               subst V2. destruct isV; cbn [u_cstk u_vstk] in Hb0; rewrite VNB in Hb0; injection V2Bb as VB1 VB2; rewrite VB1, VB2 in DCV;
                 destruct Hb0 as [<-|[<-|Hc]]; cbn [fst snd] in Hb.
               ++ clear - DCV Ha Hb. lia.
               ++ exact (DISJ_BN a Hb Ha).
               ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_vc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
                  unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
               ++ exact (DISJ_BN a Hb Ha).
               ++ clear - DCV Ha Hb. lia.
               ++ apply in_map_iff in Hc as (ch & <- & Hch). pose proof (disj_cc g2 LB O2 ch Hch) as D. unfold rdisj in D. rewrite VB1, VB2 in D.
                  unfold chunk_block, CHUNK_HDR in Hb. cbn [fst snd] in Hb. clear - D Ha Hb. unfold CHUNK_HDR in D. lia.
            --
               right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [rewrite KDv; destruct isV; unfold K_VTOP, K_CTOP, HeapOp.K_BLOCK; clear; lia|].
               unfold sub_ok. cbv zeta. cbn [w_kind w_lo w_len]. subst g'. cbn [u_cstk u_vstk u_levels u_zone]. rewrite KDv.
               destruct isV; [right; left| left]; (split; [reflexivity|]); rewrite VN1, VN6, VN7; subst NT; clear - L16; lia.
          *
            destruct M2 as (M21 & M22 & M23 & M24 & M25 & M26). unfold mem_ok. subst g'. cbn [u_levels u_cstk u_vstk u_zone u_root u_vis]. change (ms_mem ms') with M'. fold bm'.
            unfold V2 in V2B. unfold V2 in V2SZ.
            split; [| split; [| split; [| split; [exact M24| split; [exact M25| exact M26]]]]].
            -- destruct isV; [exact M21|]. cbn in V2B. rewrite VN1. apply (cstk_at_shift _ bm' bm' Bz Nz); [| rewrite <- V2B; exact M21].
               intros i Hi. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
            -- intros NN. destruct isV; [| exact (M22 NN)]. cbn in V2B. rewrite VN1. pose proof (M22 NN) as X. rewrite V2B in X. unfold u64_at in X |- *.
               rewrite (rdZ_shift bm' bm' 8 Bz Nz); [exact X|]. intros i Hi. apply COPY. clear - Hi L16. lia.
            -- destruct isV; [| exact M23]. cbn in V2B. rewrite VN1. apply (vstk_at_shift _ bm' bm' (Bz + 8) (Nz + 8)); [| rewrite <- V2B; exact M23].
               intros i Hi. rewrite <- !Z.add_assoc. apply COPY. rewrite RLEN in Hi. cbn in V2SZ. clear - Hi V2SZ V2SC LCAP2 DPOS. subst V2. lia.
          *
            split; [intros X; discriminate X|]. destruct AX2 as [AX2 SE2].
            assert (NP : forall w, In w (map (wden E1) ws') -> pot_win w -> In w (map (wden E1) ws)).
            { intros w Hw (K0 & _). apply in_map_iff in Hw as (x & <- & Hx). destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
              - apply in_map. exact Hx'.
              - exfalso. rewrite WB'd in K0. cbn [w_kind] in K0. unfold HeapOp.K_BLOCK, K_STACK in K0. lia.
              - exfalso. rewrite WNTd in K0. cbn [w_kind] in K0. unfold KD, G6RegrowAC.TwinB.G6RegrowAC.KD, K_STACK in K0.
                destruct isV; [change (to_Z 3%uint63) with 3 in K0| change (to_Z 2%uint63) with 2 in K0]; lia. }
            split; [exact (acct_pot_ws _ _ _ _ _ AX2 NP)|].

            change (u_zone g') with (u_zone g2).
            apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE2|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
            destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
            -- apply in_map. exact Hx'.
            -- exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. lia.
            -- exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold KD, G6RegrowAC.TwinB.G6RegrowAC.KD, Seal.K_TWIN in K9.

               destruct isV; [change (to_Z 3%uint63) with 3 in K9| change (to_Z 2%uint63) with 2 in K9]; lia.
      -
        intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
        apply (proj1 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws') _ a (mk_args_sound E1 1%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
        assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
        { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
        split.
        + destruct (in_ws_dec (map (wden E1) ws) a) as [IW|NIW].
          * right. apply (proj1 (in_ws_map_iff E1 ws a)) in IW as (w & Hw & Hin).
            destruct (win3_eqb w wN) eqn:QN; [| destruct (win3_eqb w wT) eqn:QT].
            -- apply win3_eqb_eq in QN. subst w. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs.
               split; [exact FN|]. rewrite WNd1 in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin. unfold inR. rewrite EVN1, LON', HIN'. fold Nz. clear - Hin. lia.
            -- apply win3_eqb_eq in QT. subst w. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
               split; [exact FT|]. rewrite WTd1 in Hin. unfold in_iv, w_iv in Hin. cbn [w_lo w_len fst snd] in Hin.
               unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 8%uint63) with 8. fold Tz. clear - Hin. lia.
            -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
               exact Hin.
          * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 1 _ (map (wden E1) ws) _ a (DECf E1))). auto.
        + intros k r [H1|[H1|[]]] IR; injection H1 as <- <-.
          * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
            unfold inR in IR. rewrite NTV in IR. change (loZ (region16 (g_cells grT) (g_cells grN))) with 0 in IR. unfold hiZ in IR. cbn [region16 rg_hi den] in IR.
            rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 16%uint63) with 16 in IR. alia.
          * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
            unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
      -
        assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
        assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 8))))) = Nz + (L - 8)).
        { rewrite (G1.den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
        constructor.
        { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
        constructor.
        { cbn [fact_holds]. rewrite Db', De'. subst NT. alia. }
        constructor.
        { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
        constructor.
        {
          cbn [fact_holds]. apply bv_eq. rewrite !G1.den_VAlu. cbn [alu64 alu]. rewrite !bv_sub_unsigned, !wrap64, De', Db'.
          assert (DVE1 : bv_unsigned (den E1 (VP kT (wlit 8))) = Tz + 8).
          { rewrite (G1.den_VP_nowrap E1 kT (wlit 8)); rewrite EVT1, wlit_ok; change (to_Z 8%uint63) with 8; fold Tz; [reflexivity| exact (proj2 RTr)]. }
          rewrite DVE1, (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. fold Bz. subst NT. f_equal. alia. }
        apply Forall_app. split.
        + apply (G4.anchor_facts_sound E1 fs kN (L - 8) (L - 8) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
        + rewrite ALN. constructor; [| constructor]. cbn [fact_holds]. rewrite NTV. change (2 ^ to_Z 3%uint63) with 8. subst NT.
          replace (Nz + L - 8) with (Nz + (L - 8)) by alia. rewrite Z.add_mod, NZ8, Z.add_0_l, Z.mod_mod by lia.
          apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 1). lia.
    }
Qed.

Theorem g6r_sound : contract_sound segs OPS MP PB (g6r_contract SRCPAT isV MEMCPY_PC).
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [g6r_contract c_apply c_pc] in HAP, Hpc.
  unfold g6r_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:AP; [|discriminate].
  destruct (PrimInt63.eqb mdi 1 && fresh_ok (sink st st1 r)) eqn:MDF; [|discriminate].
  apply andb_prop in MDF as [MD FRS]. apply Uint63.eqb_correct in MD. subst mdi.
  exact (regrow_sound st r hargs wnl st1 aw ws ca sts K E ms model Hpc TO AP FRS HAP HS0 HMP HPB Hk).
Qed.
End Sound.
End G6RegrowA.
End TwinB.
