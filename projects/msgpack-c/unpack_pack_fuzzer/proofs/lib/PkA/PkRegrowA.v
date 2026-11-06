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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Arith Steps OpsBridge Ops Tree PkOps PkLib GLib GUnp G3 GWin PkStack PkAux.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import LiaFast.
Unset Nia Cache. Unset Nra Cache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Seal OpsKeep PkRegrow.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Bridge Require Import Actr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.PkA Require Import PkRegrowAC.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW TR PK PKL CtrLib CtrFX PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Import PkRegrow PkRegrowAC.

Module PkRegrowA.
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

Section Geom.
Variable segs : list Segment.

Lemma regrow1_geom : forall E (fs : list fact) LB wsZ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP,
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs ->
  implied fs (FULe (VP kT (wlit 24%uint63)) (VP kB oc)) = true -> implied fs (FULe (VP kB oc) (VP kT (wlit 24%uint63))) = true ->
  wt oc = false -> 24 <= w2Z oc -> w2Z oc < 140737488355328 ->
  In (Win (bv_unsigned (ev E kT)) 24 6) wsZ ->
  PK.cw_pk_holds segs (map (den E) [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP]) LB wsZ m ->
  exists g ls u, decode_pk (map (den E) [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP]) = Some u /\
    link_pk u g ls /\ pure_pk g ls /\ own_pk g LB /\ wins_pk g wsZ /\ mem_pk (bmem_of segs m) u g ls /\ ghost_pk g wsZ /\ cost_pk u g ls wsZ /\
    v_begin (k_evec g) = bv_unsigned (ev E kB) /\ v_end (k_evec g) = bv_unsigned (ev E kT) + 24 /\ v_capend (k_evec g) = bv_unsigned (ev E kB) + w2Z oc /\
    bv_unsigned (den E (VP kT (wlit 24%uint63))) = bv_unsigned (ev E kT) + 24 /\ bv_unsigned (den E (VP kB oc)) = bv_unsigned (ev E kB) + w2Z oc /\
    vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g)) /\ w2Z oc = 24 * v_cap (k_evec g) /\ v_size (k_evec g) = v_cap (k_evec g) /\
    bv_unsigned (ev E kT) + 24 = bv_unsigned (ev E kB) + w2Z oc.
Proof.
  intros E fs LB wsZ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40 RT HC.
  unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & LK & P & O & Wk & M & GH & CO).
  exists g, ls. eexists. split; [cbn [map decode_pk]; reflexivity|].
  split; [exact LK|]. split; [exact P|]. split; [exact O|]. split; [exact Wk|]. split; [exact M|]. split; [exact GH|]. split; [exact CO|].
  pose proof LK as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  set (V := k_evec g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (L := w2Z oc) in *.
  change (v_begin V = bv_unsigned (den E (VP kB wzero))) in Leb.
  change (v_end V = bv_unsigned (den E (VP kT (wlit 24%uint63)))) in Lee.
  change (v_capend V = bv_unsigned (den E (VP kB oc))) in Lecap.
  assert (RT' : Tz + 24 < two64).
  { pose proof (proj1 (Forall_forall _ _) Wk _ RT) as X. cbn [w_kind] in X.
    destruct (X ltac:(unfold HeapOp.K_STACK; lia)) as [[[KD|KD] _]|[_ ET]].
    - unfold HeapOp.K_BLOCK in KD. discriminate KD.
    - unfold K_GHOST in KD. lia.
    - destruct ET as (_ & _ & _ & _ & E5). cbn [w_lo w_len] in E5. fold V in E5. rewrite Lecap in E5.
      pose proof (bv_unsigned_in_range 64 (den E (VP kB oc))) as RC. rewrite bv_modulus_64 in RC. clear - E5 RC. unfold two64 in *. lia. }
  clear RT. rename RT' into RT.
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in Leb. fold Bz in Leb.
  assert (DVE : bv_unsigned (den E (VP kT (wlit 24%uint63))) = Tz + 24).
  { apply den_VP_nowrap. rewrite wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. exact RT. }
  rewrite DVE in Lee.
  pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as IM1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as IM2.
  cbn [fact_holds] in IM1, IM2. rewrite DVE in IM1, IM2.
  assert (VCE : v_capend V = Bz + 24 * v_cap V) by (unfold v_capend; rewrite EL, Leb; reflexivity).
  assert (VEN : v_end V = Bz + 24 * v_size V) by (unfold v_end; rewrite EL, Leb; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.
  pose proof (bv_unsigned_in_range 64 (ev E kT)) as RTz. rewrite bv_modulus_64 in RTz. fold Tz in RTz.
  pose proof (w2Z_range oc) as ROC. fold L in ROC.
  assert (VVAL : vec_valid V /\ ecap_ok (v_cap V)).
  { destruct VE as [(B0 & C0 & LS0)|VV]; [| exact VV]. exfalso.
    rewrite VEN in Lee. subst ls. cbn [length Z.of_nat] in SZ. rewrite SZ, <- Leb, B0 in Lee. clear - Lee RTz. lia. }
  destruct VVAL as (VVAL & CPOS & CPOW).
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { assert (DM : bv_unsigned (den E (VP kB oc)) = (Bz + L) mod two64) by (cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wrap64; reflexivity).
    destruct (Z_lt_le_dec (Bz + L) two64) as [LT2|GE2].
    - rewrite Z.mod_small in DM by (clear - LT2 RB ROC; lia). exact DM.
    - exfalso. rewrite <- (Z.mod_unique (Bz + L) two64 1 (Bz + L - two64)) in DM by (clear - GE2 RB ROC L40; unfold two64 in *; lia).
      rewrite VCE, DM in Lecap. clear - Lecap CPOS L40 RB. unfold two64 in *. lia. }
  rewrite DVC in Lecap, IM1, IM2.
  split; [exact Leb|]. split; [exact Lee|]. split; [exact Lecap|]. split; [exact DVE|]. split; [exact DVC|].
  split; [exact VVAL|]. split; [exact (conj CPOS CPOW)|].
  split; [clear - VCE Lecap; lia|]. split; [clear - VEN Lee VCE Lecap IM1 IM2; lia| clear - IM1 IM2; lia].
Qed.
End Geom.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Hypothesis CW3' : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m -> cw_holds CW 3 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable MEMCPY_PC : int.

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
  (forall LB, cw_holds CW (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' ->
     (forall i, 0 <= i < nZ -> exists b, rb segs (ms_mem ms') (bv_unsigned (ev E ka) + i) = Some b /\ rb segs (ms_mem ms') (bv_unsigned (ev E kb) + i) = Some b /\
                                         rb segs (ms_mem ms) (bv_unsigned (ev E kb) + i) = Some b) ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Hypothesis AVECCOPY0 : forall st (K : TSet) E ms mo r hargs wnl st1,
  st_ok segs OPS E st ms mo -> MP mo -> s_pc st = MEMCPY_PC ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) ->
  bv_unsigned (den E (getr st X12)) = 0 ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Lemma regrow0_sound : forall st r hargs wnl st1 aw ws ca c sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  PkStack.parse_ca ca = Some c -> (exists b0, PkStack.c_eb c = VL b0 /\ weqb b0 wzero = true) ->
  regrow0 st (sink st st1 r) aw ws c = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca c sts K E ms model Hpc TO AP FRS PCA (b0 & EB & B00) HAP HS0 HMP HPB Hk.
  apply (proj1 (weqb_ok _ _)) in B00. subst b0.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb] in EB. subst eb.
  unfold regrow0 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP. rewrite SF in HAP.
  set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 0) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B]. apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [EE0 EC0].
  apply sv_eqb_eq in EE0. apply sv_eqb_eq in EC0. subst ee ecap.
  apply negb_true_iff in KN0. apply negb_true_iff in KN1. apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN.
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN.
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & rav & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.
  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pcov0 Pminv0].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VL wzero; VL wzero; VL wzero; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  set (Nz := bv_unsigned (ev E kN)) in *.
  pose proof (bv_unsigned_in_range 64 (ev E kN)) as RNz. rewrite bv_modulus_64 in RNz. fold Nz in RNz.

  assert (N12V : bv_unsigned (den E n12) = 0).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu den]. rewrite bv_sub_unsigned, wrap64, wbv_unsigned, wzero_ok. reflexivity.
    - apply sv_eqb_eq in LEN. rewrite LEN. replace (sv_alu ALU_SUB (VL wzero) (VL wzero)) with (VL wzero) by (vm_compute; reflexivity).
      cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? 0) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; unfold two64 in *; lia).
      rewrite Q2. fold Nz. replace (Nz + 0 - 0) with Nz by lia. rewrite Z.mod_small by (unfold two64 in *; lia). subst Nz. reflexivity. }

  apply (AVECCOPY0 st K E ms model (wl rav) hargs wnl (setregs st R') HS0 HMP Hpc AP).
  - fold n12. exact N12V.
  - intros E' ms' mo' HX' HMP' HSS.
    {
    set (E1 := E') in *. set (M' := ms_mem ms') in *. set (nT := s_next stS) in *.
    assert (HX : env_ext n0 E E1) by exact HX'.
    assert (EVN1 : ev E1 kN = ev E kN) by exact (proj1 (proj2 HX kN KN_LT)).
    pose proof HSS as HSE1.
    pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 Pbst1 Preg1 Pdisj1 _ Pfacts1 Pops1 _ _ _ _].
    fold stS in Pfacts1, Pops1, Preg1, Pdisj1. rewrite SF in Pfacts1. fold fs in Pfacts1.
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
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
    apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
    destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
    pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
    cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
    pose proof P as (LV & EL & SZ & VE & CE & ZV).
    pose proof M as (M1 & M2 & M3 & M4 & M5).
    assert (VB0 : v_begin (k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
    destruct VE as [(_ & VC0 & LS0)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)]. subst ls.
    set (bm' := bmem_of segs M') in *.

    pose proof (Preg1 kN rN FN) as ROKN.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (HIN' : hiZ E1 rN = 24) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr. rewrite LON', HIN', EVN1 in RNr. fold Nz in RNr.
    pose proof (aw_ceiling_small segs IMGX AW mo') as CEIL. unfold two62Z in CEIL.
    set (wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63))) in *.
    assert (WNd1 : wden E1 wN = Win Nz 24 HeapOp.K_BLOCK).
    { unfold wden, wN. rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1. cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity. }

    assert (NLB : In (Nz, 24) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
      - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
      - exact IN.
      - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
    assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 24 -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
    assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
    pose proof HA as HA'.

    set (wNT := top_win kN 24%uint63 ETOPk).
    set (ws' := map (fun w => if win3_eqb w wN then wNT else w) ws).
    set (ca' := [root; rootT; n1; P1; zh; c0; VP kN wzero; VP kN wzero; VP kN (wlit 24%uint63); tptr; trest; tmap; tkey; cf; fT; fN; fP]).
    assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN) \/ w = wNT).
    { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQx & Hx). destruct (win3_eqb x wN) eqn:Q.
      - right. symmetry. exact EQx.
      - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate Q. }
    assert (LENws' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; clear - WLEN; lia).
    assert (WNTd : wden E1 wNT = Win Nz 24 6) by (subst wNT; rewrite top_win_den, EVN1; reflexivity).
    assert (Db' : bv_unsigned (den E1 (VP kN wzero)) = Nz) by (rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
    assert (Dcap' : bv_unsigned (den E1 (VP kN (wlit 24%uint63))) = Nz + 24).
    { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, EVN1; fold Nz; change (to_Z 24%uint63) with 24; [reflexivity| alia]. }
    set (g' := PKG (k_tree g) (mkVec Nz 0 1 24) (k_zone g)).
    apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH []
             [] (mk_args 3%uint63 aw ws' ca') _ nT).
    -   intros k [].
    -   constructor.
    -   intros k rr [].
    -   intros k rr [].
    -   intros k rr a [].
    -   intros k1 r1 k2 r2 a [].
    -   rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
      split; [apply mk_args_sound; exact LENws'|].
      split.
      { pose proof HA' as HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
        - intros x Hx. destruct (KEPTW x Hx) as [[Hx' _]| ->]; [left; exact Hx'| right; apply UOK.kind_new_sub; reflexivity].
        - intros x Hx. destruct (UOK.map_replace_old ws wN wNT x Hx) as [H1| ->]; [left; exact H1| right].
          rewrite WNd1. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
          exists (Nz, 24). split; [exact NLB|]. split; [unfold in_iv; cbn [fst snd w_lo]; clear; lia|]. left. unfold c24, C24_LO, C24_HI. cbn [snd]. clear. lia. }
      split.
      +
        unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPTW x Hx) as [[Hx' _]| ->].
        * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
        * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
          right; right. split; [unfold HeapOp.K_SUB; alia|]. exists (Nz, 24). split; [exact NLB|]. intros a Ha. exact Ha.
      +
        apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
        assert (VNV : vec_valid (mkVec Nz 0 1 24)) by (unfold vec_valid; cbn [v_elt v_size v_cap v_begin]; split; [alia|]; split; [alia|]; split; [exact NZ0| exact NZ8]).
        assert (OWN' : owned g' = (Nz, 24) :: map chunk_block (z_chunks (k_zone g))).
        { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone v_begin]. rewrite (proj2 (Z.eqb_neq _ _) NZ0). reflexivity. }
        assert (OWNo : owned g = map chunk_block (z_chunks (k_zone g))).
        { unfold owned, evec_blocks. rewrite VB0. reflexivity. }
        exists g', []. split; [| split; [| split; [| split]]].
        *
          unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP last_opt rev].
          rewrite Db', Dcap'. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
          split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
          split; [reflexivity|]. split; [alia|]. split; [alia|].
          cbn [last_opt rev] in LTOP. split; [exact LTOP|].
          intros CF. destruct (LCF CF) as (X & _). exfalso. exact (X eq_refl).
        *
          unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone v_elt v_size v_cap v_begin]. unfold v_capend. cbn [v_begin v_elt v_cap].
          split; [exact LV|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; split; [exact VNV| split; [lia| split; [reflexivity| lia]]]|]. split; [alia| exact ZV].
        *
          unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF. split.
          -- intros b [<-|Hb]; [exact NLB| exact (OL b Hb)].
          -- constructor; [| exact OF]. apply Forall_forall. intros cb Hcb.
             pose proof (DISJN cb ltac:(rewrite OWNo; exact Hcb)) as D. unfold rdisj. cbn [fst snd].
             apply in_map_iff in Hcb as (ch & <- & Hch). unfold chunk_block. cbn [fst snd].
             destruct ZV as ((_ & _ & V3 & _) & _). destruct (V3 ch Hch) as (_ & _ & S3).
             destruct (Z_lt_le_dec (fst ch) (Nz + 24)) as [A1|A1]; [| left; exact A1].
             destruct (Z_lt_le_dec Nz (fst ch + (CHUNK_HDR + snd ch))) as [A2|A2]; [| right; exact A2].
             exfalso. destruct (Z_lt_le_dec (fst ch) Nz) as [A3|A3].
             ++ apply (D Nz ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
             ++ apply (D (fst ch) ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
        *
          unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
          rewrite OWN'.
          destruct (KEPTW x Hx) as [[Hx' NxN]| ->].
          --
             destruct (proj1 (Forall_forall _ _) Wk (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]]; [| destruct ET as (_ & NE0 & _); exfalso; exact (NE0 VB0)].
             left. split; [exact KDx|]. intros b [<-|Hb] a Ha Hb'.
             ++ unfold in_iv in Hb'. cbn [fst snd] in Hb'.
                pose proof (new_block_apart segs IMGX AW E1 fs (s_regs stS) _ LB M' mo' kN rN 24 ws wN wN x Pfacts1 Pdisj1 FN KN0 LON HIN' ltac:(lia) WN HA
                         ltac:(rewrite EVN1; exact NLB) WF KL OBK NOA SWO EXN ltac:(rewrite EVN1; exact WNd1) Hx' NxN NxN NS a Ha) as NBA. rewrite EVN1 in NBA. exact (NBA Hb').
             ++ exact (DJ b ltac:(rewrite OWNo; exact Hb) a Ha Hb').
          -- right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
             unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
             split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia.
        *
          split.
          2: { split; [destruct GH as [SE EP]; split|].
               3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| reflexivity].
                    intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                    destruct (KEPTW x Hx) as [[Hx' _]| ->]; [apply in_map; exact Hx'|].
                    exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
               - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
                 destruct (KEPTW x Hx) as [[Hx' _]| ->]; [apply in_map; exact Hx'|].
                 exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
               - intros _. exists (wden E1 wNT). split.
                 + apply in_map. subst ws'. apply in_map_iff. exists wN. rewrite win3_eqb_refl. split; [reflexivity| exact EXN].
                 + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
                   split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia. }
          unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone v_begin]. fold bm'.
          split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
          split; [exact M4|]. intros _. cbn. exact I.
    -
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
      assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
      { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
      split; [| intros k rr []].
      left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))).
      split; [exact RA0|]. split; [exact NI|]. intros IW. apply (proj1 (in_ws_map_iff E1 ws a)) in IW as (w & Hw & Hin).
      destruct (win3_eqb w wN) eqn:QN.
      + apply win3_eqb_eq in QN. subst w. apply (NWi wNT); [subst ws'; apply in_map_iff; exists wN; rewrite win3_eqb_refl; auto|].
        rewrite WNTd. rewrite WNd1 in Hin. exact Hin.
      + apply (NWi w); [subst ws'; apply in_map_iff; exists w; rewrite QN; auto|]. exact Hin.
    -   constructor.
    }
Qed.

Lemma regrow1_sound : forall st r hargs wnl st1 aw ws ca c kB kT oc sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  PkStack.parse_ca ca = Some c -> PkStack.c_eb c = VP kB wzero -> PkStack.c_ee c = VP kT (wlit 24%uint63) -> PkStack.c_ecap c = VP kB oc ->
  regrow1 SRCPAT st (sink st st1 r) wnl aw ws c kB kT oc = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca c kB kT oc sts K E ms model Hpc TO AP FRS PCA EB EE EC HAP HS0 HMP HPB Hk.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb PkStack.c_ee PkStack.c_ecap] in EB, EE, EC. subst eb ee ecap.
  unfold regrow1 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP. rewrite SF in HAP.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs stS)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  destruct (gcells rT 0%uint63) as [t0|] eqn:GT0; [|discriminate]. destruct (gcells rT 1%uint63) as [t1|] eqn:GT1; [|discriminate].
  destruct (gcells rT 2%uint63) as [t2|] eqn:GT2; [|discriminate].
  destruct (gcells rN (Uint63.of_Z (L / 8))) as [e0|] eqn:GN0; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 1%uint63)) as [e1|] eqn:GN1; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 2%uint63)) as [e2|] eqn:GN2; [|discriminate].
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SRCP]. apply andb_prop in COND as [COND VCP].
  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND TKB].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [OCT L24].
  apply negb_true_iff in OCT. apply Z.leb_le in L24. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0. apply negb_true_iff in KN1.
  apply neqb_neq in NNT. apply neqb_neq in NNB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN. apply existsb_win_In in EXT.
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

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  pose proof HC as HCm. apply CW3 in HC.
  set (wT := top_win kT 24%uint63 ETOPk) in *.
  assert (WTd : forall E0, wden E0 wT = Win (bv_unsigned (ev E0 kT)) 24 6) by (intros E0; subst wT; rewrite top_win_den; reflexivity).
  assert (L40' : w2Z oc < 140737488355328) by exact L40.
  destruct (regrow1_geom segs E fs LB _ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40'
              ltac:(rewrite <- (WTd E); apply in_map; exact EXT) HC)
    as (g & ls & u & DU & LK & P & O & Wk & M & GH & CO & Leb & Lee & Lecap & DVE & DVC & VVAL & (CPOS & CPOW) & LCAP & SZC & TZ24).
  fold L in Lecap, DVC, LCAP, TZ24.
  pose proof P as (LV & EL & SZ & VE & CE & ZV). pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  set (V := k_evec g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.

  pose proof (Preg0 kN ra FNst) as ROKa.
  assert (LOa' : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity).
  pose proof (w2Z_range oc) as ROC. fold L in ROC. unfold two40Z in L40.
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. alia. }
  assert (HIa' : hiZ E ra = 2 * L) by (unfold hiZ; rewrite HIa; cbn [den]; rewrite wbv_unsigned; exact L2w).
  pose proof (ro_range _ _ _ _ _ _ ROKa KN0) as RNr. rewrite LOa', HIa' in RNr. fold Nz in RNr.

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + L - L) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz (2 * L) HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (VBY : v_bytes V = 24 * v_cap V) by (unfold v_bytes; rewrite EL; reflexivity).
  assert (VOWN : In (Bz, L) (owned g)) by (rewrite <- Leb, LCAP, <- VBY; apply owned_evec; fold V; exact VV3).
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }

  apply (AVECCOPY st K E ms model (wl rav) hargs wnl (setregs st R') kN ra (VL (wlit (Uint63.of_Z (2 * L)))) kB (VL oc) L 3%uint63 aw ws
           [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] HS0 HMP Hpc AP).
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
    intros LB' HC'. change (to_Z 3%uint63) with 3 in HC'. apply CW3 in HC'.
    destruct (regrow1_geom segs E fs LB' _ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40'
                ltac:(rewrite <- (WTd E); apply in_map; exact EXT) HC')
      as (g' & ls' & u' & _ & _ & P' & O' & Wk' & _ & _ & _ & Leb' & _ & _ & _ & _ & VVAL' & _ & LCAP' & _ & _).
    cbn [den]. rewrite wbv_unsigned. fold L Bz.
    destruct P' as (_ & EL' & _). destruct VVAL' as (_ & _ & VV3' & _).
    pose proof (owned_evec g' VV3') as OW'. rewrite Leb' in OW'. unfold v_bytes in OW'. rewrite EL' in OW'. unfold ELEM_SIZE in OW'. fold L in LCAP'. rewrite <- LCAP' in OW'. fold Bz in OW'.
    split; [exact (proj1 O' _ OW')|].
    intros w0 Hw0 KD0 a Ha0 Hb0.
    destruct (proj1 (Forall_forall _ _) Wk' w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
    + exact (DJ _ OW' a Ha0 Hb0).
    + destruct ET as (K6 & _). unfold K_ETOP, HeapOp.K_BLOCK, K_GHOST in *. lia.
  -
    intros E' ms' mo' HX' HMP' HSS COPYB.
    {
    clear DEC.
    clear g ls u DU LK P O Wk M GH CO Leb Lee Lecap DVE DVC VVAL CPOS CPOW LCAP SZC TZ24 LV EL SZ VE CE ZV VV1 VV2 VV3 VV4 VBY VOWN DISJN SEP HA WF HC HCm V LB.
    set (nT := s_next stS) in *.
    destruct (fresh_ok_inv stS FRS) as (VBS & NPOSS & N62S). fold nT in VBS, NPOSS, N62S.
    set (M' := ms_mem ms') in *.
    assert (TZ15 : to_Z nT = to_Z n0 + 15).
    { subst nT. rewrite SN. fold n0. rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia). reflexivity. }
    assert (TZ16 : to_Z (PrimInt63.add nT 1) = to_Z n0 + 16).
    { rewrite add_Z by (change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; alia). rewrite TZ15. change (to_Z 1%uint63) with 1. lia. }
    set (NT := Nz + L - 24).
    set (Fv := fun _ : Z => Z_to_bv 64 NT). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
    set (E1 := env_above E' nT Fv Gv).
    assert (HX1 : env_ext nT E' E1) by (subst E1; apply env_above_ext).
    assert (HX : env_ext n0 E E1) by (apply (env_ext_trans n0 nT E E' E1); [lia| exact HX'| exact HX1]).
    assert (ENT : ev E1 nT = Z_to_bv 64 NT) by (subst E1; rewrite ev_above by lia; reflexivity).

    assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
    { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
    assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
    { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
      repeat split; right; right; right; apply in_app_iff; left; assumption. }
    assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
    { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero (INCA (VP kB wzero) ltac:(inlist))).
    assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 24%uint63) (INCA (VP kT (wlit 24%uint63)) ltac:(inlist))).
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
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
    apply CW3 in HC.
    destruct (regrow1_geom segs E1 fs LB _ M' root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz1 Pfacts1 IMP1 IMP2 OCT L24 L40'
                ltac:(rewrite <- (WTd E1); apply in_map; exact EXT) HC)
      as (g & ls & u & DU & LK & P & O & Wk & M & GH & CO & Leb & Lee & Lecap & DVE & DVC & VVAL & (CPOS & CPOW) & LCAP & SZC & TZ24).
    rewrite EVB1 in Leb, Lecap, DVC, TZ24. rewrite EVT1 in Lee, DVE, TZ24. fold L Bz Tz in Leb, Lee, Lecap, DVE, DVC, LCAP, TZ24.
    cbn [map decode_pk] in DU. injection DU as <-.
    pose proof LK as (LT & LN & LP & Lc0 & _ & _ & _ & LTOP & LCF).
    cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, LTOP, LCF.
    pose proof P as (LV & EL & SZ & VE & CE & ZV). pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
    pose proof M as (TW2 & KA2 & ICB2 & CH2 & PE2).
    set (V := k_evec g) in *.
    set (bm' := bmem_of segs M') in *.
    pose proof (aw_ceiling_small segs IMGX AW mo') as CEIL. unfold two62Z in CEIL.
    assert (VCE : v_capend V = Bz + 24 * v_cap V) by (unfold v_capend; rewrite EL, Leb; reflexivity).
    assert (VEN : v_end V = Bz + 24 * v_size V) by (unfold v_end; rewrite EL, Leb; reflexivity).
    assert (VBY : v_bytes V = 24 * v_cap V) by (unfold v_bytes; rewrite EL; reflexivity).
    pose proof (proj1 O _ (owned_evec g VV3)) as VLB. fold V in VLB. rewrite Leb in VLB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ M' mo' _ HA VLB) as (Bb1 & Bb2 & Bb3 & Bb4 & _). cbn [fst snd] in Bb1, Bb2, Bb3.
    assert (CAP2 : 2 * v_cap V <= 1024).
    { apply (PKL.cap_double_ok (k_tree g) ls); [exact (proj1 CPOW)| exact LV| exact (proj2 ZV)| rewrite <- SZC; exact SZ]. }

    pose proof (Preg1 kN rN FN) as ROKN. pose proof (Preg1 kT rT FT) as ROKT.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
    assert (HIN' : hiZ E1 rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
    assert (HIT' : hiZ E1 rT = 24) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT', EVT1 in RTr. fold Tz in RTr.
    assert (WNd1 : wden E1 wN = Win Nz (2 * L) HeapOp.K_BLOCK) by exact (WNd E1 EVN1).
    assert (WTd1 : wden E1 wT = Win Tz 24 6) by (rewrite (WTd E1), EVT1; reflexivity).
    assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (VOWN : In (Bz, L) (owned g)) by (rewrite <- Leb, LCAP, <- VBY; apply owned_evec; fold V; exact VV3).
    assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
    { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
      intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }
    assert (BYN : forall a, Nz <= a < Nz + 2 * L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (bytes_of_region segs _ E1 M' kN rN a ROKN KN0). rewrite LON', HIN', EVN1. fold Nz. alia. }

    assert (NLB : In (Nz, 2 * L) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
      - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
      - exact IN.
      - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
    destruct (aw_blocks_ok segs IMGX AW _ LB _ M' mo' _ HA NLB) as (Nb1 & Nb2 & Nb3 & _). cbn [fst snd] in Nb1, Nb2, Nb3.

    assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
    { intros i Hi. destruct (COPYB i Hi) as (b & C1 & C2 & _). fold Nz Bz in C1, C2. rewrite C1, C2. reflexivity. }
    assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
    { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite (RBC i Hi). reflexivity. }

    set (VN := mkVec Nz (v_size V) (2 * v_cap V) 24).
    set (g' := PKG (k_tree g) VN (k_zone g)).
    assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V /\ v_cap VN = 2 * v_cap V /\ v_elt VN = 24 /\ v_bytes VN = 2 * L /\
                  v_end VN = NT + 24 /\ v_capend VN = Nz + 2 * L).
    { subst VN. unfold v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite SZC. subst NT. repeat split; alia. }
    destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
    assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
    assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
    assert (TZB : Tz = Bz + L - 24) by alia.
    assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
    assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

    assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
    { intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }

    assert (BYNT : forall a, NT <= a < NT + 48 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply BYN. subst NT. alia. }
    assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ M' mo' _ a HA VLB). unfold in_iv. cbn [fst snd]. rewrite VBY. alia. }

    assert (GCINV : forall rr gi cs, gcells rr gi = Some cs -> exists gr, IMap.find gi (rg_cells rr) = Some gr /\ cs = g_cells gr).
    { intros rr gi cs H. unfold gcells in H. destruct (IMap.find gi (rg_cells rr)) as [gr|]; [|discriminate]. injection H as <-. exists gr. auto. }
    assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
    { apply keyZ_of_Z. unfold two62Z. clear - L24 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
    assert (L8E : 8 * (L / 8) = L) by (clear - L8 L24; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
    assert (L8R : 0 <= L / 8 < 2 ^ 44) by (clear - L24 L40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (OFZ : forall d, 0 <= d <= 2 -> PrimInt63.add (Uint63.of_Z (L / 8)) (Uint63.of_Z d) = Uint63.of_Z (L / 8 + d)).
    { intros d Hd. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec. rewrite wB_two63, two63_eq. clear - Hd L8R.
      rewrite (Z.mod_small (L / 8)) by lia. rewrite (Z.mod_small d) by lia. rewrite ?(Z.mod_small (L / 8 + d)) by lia. first [reflexivity | symmetry; apply Z.mod_small; lia | apply Z.mod_small; lia]. }
    assert (KEYL1 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 1) = L / 8 + 1).
    { change 1%uint63 with (Uint63.of_Z 1). rewrite (OFZ 1) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
    assert (KEYL2 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 2) = L / 8 + 2).
    { change 2%uint63 with (Uint63.of_Z 2). rewrite (OFZ 2) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
    assert (SLOT : forall E0 rr kk gi cs, IMap.find kk (s_regs stS) = Some rr -> st_ok segs OPS E0 stS ms' mo' -> gcells rr gi = Some cs ->
              slot_ok segs E0 M' (bv_unsigned (ev E0 kk) + 8 * keyZ gi) cs).
    { intros E0 rr kk gi cs Hf HSx Hg. destruct (GCINV rr gi cs Hg) as (gr & Fgr & ->). exact (ro_cells _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HSx kk rr Hf) gi gr Fgr). }
    pose proof (SLOT E1 rT kT 0%uint63 t0 FT HSE1 GT0) as ST0. pose proof (SLOT E1 rT kT 1%uint63 t1 FT HSE1 GT1) as ST1.
    pose proof (SLOT E1 rT kT 2%uint63 t2 FT HSE1 GT2) as ST2.
    pose proof (SLOT E1 rN kN _ e0 FN HSE1 GN0) as SN0. pose proof (SLOT E1 rN kN _ e1 FN HSE1 GN1) as SN1. pose proof (SLOT E1 rN kN _ e2 FN HSE1 GN2) as SN2.
    rewrite EVT1 in ST0, ST1, ST2. fold Tz in ST0, ST1, ST2. change (keyZ 0%uint63) with 0 in ST0. change (keyZ 1%uint63) with 1 in ST1. change (keyZ 2%uint63) with 2 in ST2.
    rewrite EVN1 in SN0, SN1, SN2. fold Nz in SN0, SN1, SN2. rewrite KEYL in SN0. rewrite KEYL1 in SN1. rewrite KEYL2 in SN2.
    assert (TZB' : Tz = Bz + L - 24) by alia.
    assert (SHIFT_T : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 M' (Tz + 8 * j) cs -> slot_ok segs E1 M' (NT + 8 * j) cs).
    { intros j cs Hj S0. apply (slot_ok_shift segs E1 M' M' (Tz + 8 * j) (NT + 8 * j) _ S0). intros i Hi. subst NT.
      replace (Nz + L - 24 + 8 * j + i) with (Nz + (L - 24 + 8 * j + i)) by alia. rewrite (RBC (L - 24 + 8 * j + i)) by alia.
      f_equal. alia. }
    assert (SHIFT_N : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 M' (Nz + 8 * (L / 8 + j)) cs -> slot_ok segs E1 M' (NT + 24 + 8 * j) cs).
    { intros j cs Hj S0. replace (NT + 24 + 8 * j) with (Nz + 8 * (L / 8 + j)) by (subst NT; alia). exact S0. }
    assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region48 t0 t1 t2 e0 e1 e2)).
    { apply (region48_ok segs (s_priv st) E1 M' nT _ _ _ _ _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| | | | | |].
      - replace NT with (NT + 8 * 0) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 0) with Tz by alia. rewrite Z.mul_0_r, Z.add_0_r in ST0. exact ST0.
      - replace (NT + 8) with (NT + 8 * 1) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 1) with (Tz + 8) by alia. exact ST1.
      - replace (NT + 16) with (NT + 8 * 2) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 2) with (Tz + 16) by alia. exact ST2.
      - replace (NT + 24) with (NT + 24 + 8 * 0) by alia. apply SHIFT_N; [lia|]. replace (L / 8 + 0) with (L / 8) by alia. exact SN0.
      - replace (NT + 32) with (NT + 24 + 8 * 1) by alia. apply SHIFT_N; [lia|]. exact SN1.
      - replace (NT + 40) with (NT + 24 + 8 * 2) by alia. apply SHIFT_N; [lia|]. exact SN2. }
    destruct (empty_region_ok segs (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
                ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).
    pose proof HA as HA'.

    assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E1) ws) a /\ ~ in_ivs IMGX a).
    { intros a Ha.
      assert (SFE : PK.safe g (map (wden E1) ws) a).
      { intros w Hw (K6 & NE0 & E1' & E2' & E3') Hin. fold V in E1', E2', E3'. rewrite VEN, SZC in E2'. unfold ELEM_SIZE in E2'.
        unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. clear - Ha Hin E2' TZB LCAP. lia. }
      destruct (pk_owned_byte_props segs IMGX AW _ LB M' mo' g _ _ a HA WF O Wk VOWN ltac:(unfold in_iv; cbn [fst snd]; alia) SFE) as (_ & NI & NW & _).
      split; [exact NW| exact NI]. }

    set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
    set (wNT := top_win nT 48%uint63 ETOPk).
    set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
    set (b' := VP kN wzero). set (e' := VP nT (wlit 24%uint63)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
    set (ca' := [root; rootT; n1; P1; zh; c0; b'; e'; cap'; tptr; trest; tmap; tkey; cf; fT; fN; fP]).
    assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
    { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
      apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
      split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
    assert (LENws' : Z.of_nat (length ws') < two63).
    { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
    assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
    { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
    assert (WNTd : wden E1 wNT = Win NT 48 6) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
    assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
    assert (De' : bv_unsigned (den E1 e') = NT + 24).
    { subst e'. rewrite (den_VP_nowrap E1 nT (wlit 24%uint63)); rewrite ?wlit_ok, NTV; change (to_Z 24%uint63) with 24; [reflexivity| subst NT; alia]. }
    assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
    { subst cap'. rewrite (den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }

    assert (LSNE : ls <> []) by (intros X; rewrite X in SZ; cbn in SZ; alia).
    assert (RLEN : Z.of_nat (length (removelast ls)) = v_size V - 1).
    { rewrite (removelast_length _ LSNE). rewrite Nat2Z.inj_sub by (destruct ls; [exfalso; exact (LSNE eq_refl)| cbn; lia]). rewrite <- SZ. reflexivity. }
    apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH [kN; kT]
             [(nT, region48 t0 t1 t2 e0 e1 e2); (kB, empty_region L)] (mk_args 3%uint63 aw ws' ca') _ (PrimInt63.add nT 1)).
    -   intros k [<-|[<-|[]]]; rewrite F5regs.
      + split; [exact KN0|]. exists rN. split; [exact FN| exact WN].
      + split; [exact KT0|]. exists rT. split; [exact FT| exact WT].
    -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
    -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
    -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
    -   intros k rr a [H1|[H1|[]]] IR; injection H1 as <- <-.
      + right. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs. split; [exact FN|].
        unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LON', HIN'. fold Nz.
        change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
        change (to_Z 48%uint63) with 48 in IR. subst NT. alia.
      + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
        destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
        * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))).
          destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
        * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
          split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. alia.
    -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
        unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0;
        unfold hiZ; cbn [region48 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 48%uint63) with 48; intros [J1 J2].
      + apply (DISJ_BN a); subst NT; alia.
      + apply (DISJ_BN a); subst NT; alia.
    -   rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
      split; [apply mk_args_sound; exact LENws'|].
      split.
      { pose proof HA' as HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
        - intros x Hx. destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [left; exact Hx'| right| right; apply UOK.kind_new_sub; reflexivity].

          rewrite WB'd. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|].
          intros _ g0 Hg KG a Ha Hb. apply in_map_iff in Hg as (y & <- & Hy).
          destruct (KEPTW y Hy) as [(Hy' & _ & _)|[->| ->]].
          +
            destruct (proj1 (Forall_forall _ _) Wk (wden E1 y) (in_map _ _ _ Hy') ltac:(unfold K_STACK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
            * exact (DJ (Bz, L) VOWN a Ha Hb).
            * destruct ET as (K6 & _). unfold PK.K_ETOP, K_GHOST in *. lia.
          + rewrite WB'd in KG. cbn [w_kind] in KG. unfold K_GHOST, HeapOp.K_BLOCK in KG. lia.
          + rewrite WNTd in KG. cbn [w_kind] in KG. unfold K_GHOST in KG. lia.
        - intros x Hx. destruct (UOK.filter_old ws [wB'; wNT] (fun w => negb (win3_eqb w wN || win3_eqb w wT)) x Hx) as [H1|F]; [left; exact H1| right].
          apply negb_false_iff in F. apply orb_prop in F as [F|F]; apply win3_eqb_eq in F; subst x.
          +
            rewrite WNd1. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
            apply (block_keep_evidence LB _ Nz (2 * L) _ (wden E1 wNT) NLB).
            * cbn [w_lo]. alia.
            * apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
            * rewrite WNTd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
            * rewrite WNTd. cbn [w_len]. clear. lia.
            * rewrite WNTd. cbn [w_lo]. subst NT. alia.
          +
            rewrite WTd1. split; [unfold aw_tied, K_STACK, K_GHOST; cbn [w_kind]; clear; lia|]. intros _ _.
            apply (block_keep_evidence LB _ Bz L _ (wden E1 wB') (proj1 O _ VOWN)).
            * cbn [w_lo]. alia.
            * apply in_map. subst ws'. apply in_app_iff. right. left. reflexivity.
            * rewrite WB'd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
            * rewrite WB'd. cbn [w_len]. alia.
            * rewrite WB'd. cbn [w_lo]. alia. }
      split.
      +
        unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
        * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
        * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
          right; left. split; [reflexivity|]. unfold w_iv. cbn [w_lo w_len]. rewrite LCAP, <- VBY. exact VLB.
        * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
          right; right. split; [unfold HeapOp.K_SUB; alia|].
          exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L24. lia.
      +
        apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
        assert (VNV : vec_valid VN).
        { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, SZC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }

        assert (RDJ2 : forall b, In b (owned g) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
        { intros b0 Hb0. pose proof (PK.owned_pos g ls P b0 Hb0) as PO. unfold rdisj.
          destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
          destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
          exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
          - apply (DISJN b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
          - apply (DISJN b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }
        assert (OWNo : owned g = (Bz, L) :: map chunk_block (z_chunks (k_zone g))).
        { unfold owned, evec_blocks. fold V. rewrite Leb. replace (Bz =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite <- Leb; exact VV3). rewrite VBY, <- LCAP. reflexivity. }
        assert (OWN' : owned g' = (Nz, 2 * L) :: map chunk_block (z_chunks (k_zone g))).
        { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone]. rewrite VN1, VN5. replace (Nz =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ0). reflexivity. }
        exists g', ls. split; [| split; [| split; [| split]]].
        *
          unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
          rewrite Db', De', Dcap', VN1, VN6, VN7.
          split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact LTOP| exact LCF].
        *
          unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone]. rewrite VN1, VN2, VN3, VN4, VN7.
          split; [exact LV|]. split; [reflexivity|]. split; [exact SZ|]. split; [right; split; [exact VNV| split; [alia| split; [apply pow2_b_double; [exact (proj1 CPOW)| alia]| clear - CAP2; alia]]]|]. split; [alia| exact ZV].
        *
          unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF, RDJ2. split.
          -- intros b0 [<-|Hb0]; [exact NLB| apply OL; right; exact Hb0].
          -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
             apply Forall_forall. intros cb Hcb. apply (proj1 (RDJ2 _ ltac:(right; exact Hcb))).
        *
          unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx). rewrite OWN'.
          destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
          --
             destruct (proj1 (Forall_forall _ _) Wk (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]];
               [| exfalso; pose proof (only_kind_sound E1 6 _ ws OKT x Hx' (proj1 ET)) as X; injection X as <-; exact (NxT eq_refl)].
             left. split; [exact KDx|]. intros b0 [<-|Hb0] a Ha Hb.
             ++ unfold in_iv in Hb. cbn [fst snd] in Hb.
                pose proof (new_block_apart segs IMGX AW E1 fs (s_regs stS) _ LB M' mo' kN rN (2 * L) ws wN wT x Pfacts1 Pdisj1 FN KN0 LON HIN' ltac:(alia) WN HA
                         ltac:(rewrite EVN1; exact NLB) WF KL OBK NOA SWO EXN ltac:(rewrite EVN1; exact WNd1) Hx' NxN NxT NS a Ha) as NBA. rewrite EVN1 in NBA. exact (NBA Hb).
             ++ exact (DJ b0 ltac:(rewrite OWNo; right; exact Hb0) a Ha Hb).
          --
             left. rewrite WB'd. split; [left; reflexivity|]. intros b0 [<-|Hb0] a Ha Hb; unfold in_iv, w_iv in Ha; cbn [w_lo w_len fst snd] in Ha; unfold in_iv in Hb; cbn [fst snd] in Hb.
             ++ exact (DISJ_BN a Hb Ha).
             ++ destruct O as [OL OF]. rewrite OWNo in OF. destruct (FOP_cons _ _ _ OF) as [F1 _].
                pose proof (proj1 (Forall_forall _ _) F1 b0 Hb0) as D. unfold rdisj in D. cbn [fst snd] in D. clear - D Ha Hb. lia.
          --
             right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
             unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
             split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia.
        *
          split.
          2: { split; [destruct GH as [SE EP]; split|].
               3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| reflexivity].
                    intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                    destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [apply in_map; exact Hx'| |].
                    - exfalso. apply NV. apply pku_val_none_kind. rewrite WB'd. cbn [w_kind]. unfold HeapOp.K_BLOCK. clear. lia.
                    - exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
               - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
                 destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [apply in_map; exact Hx'| |].
                 + exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. clear - K9. lia.
                 + exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
               - intros _. exists (wden E1 wNT). split.
                 + apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
                 + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
                   split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia. }
          unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone a_root]. rewrite VN1. fold bm'.
          split; [exact TW2|]. split; [exact KA2|]. split; [exact ICB2|]. split; [exact CH2|].
          intros _. pose proof (PE2 ltac:(fold V; rewrite Leb; rewrite <- Leb; exact VV3)) as X. fold V in X. rewrite Leb in X.
          apply (pelems_at_shift _ bm' bm' Bz Nz); [| exact X].
          intros i Hi. apply COPY. rewrite length_map, RLEN in Hi. unfold ELEM_SIZE in Hi. clear - Hi SZC LCAP CPOS. lia.
    -
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
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
             unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. clear - Hin. lia.
          -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
             exact Hin.
        * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))). auto.
      + intros k rr [H1|[H1|[]]] IR; injection H1 as <- <-.
        * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
          unfold inR in IR. rewrite NTV in IR. change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR.
          rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 48%uint63) with 48 in IR. alia.
        * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
          unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
    -
      assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
      assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 24))))) = Nz + (L - 24)).
      { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
      constructor.
      { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
      constructor.
      { cbn [fact_holds]. rewrite Db', DnT0. subst NT. alia. }
      constructor.
      { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
      apply Forall_app. split.
      + apply (top_facts_sound E1 fs b' nT Pfacts1); rewrite Db', NTV; [subst NT; alia|].
        subst NT. replace (Nz + L - 24 - Nz) with (L - 24) by alia. apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 3). lia.
      + apply (anchor_facts_sound E1 fs kN (L - 24) (L - 24) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
    }
Qed.

Theorem pkregrow_sound : contract_sound segs OPS MP PB (pkregrow_contract SRCPAT MEMCPY_PC).
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [pkregrow_contract c_apply c_pc] in HAP, Hpc.
  unfold pkregrow_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:AP; [|discriminate].
  destruct (PrimInt63.eqb mdi 3 && fresh_ok (sink st st1 r)) eqn:MDF; [|discriminate].
  apply andb_prop in MDF as [MD FRS]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct (PkStack.parse_ca ca) as [c|] eqn:PCA; [|discriminate].
  destruct (PkStack.c_eb c) as [b0|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  - destruct (weqb b0 wzero) eqn:B00; [|discriminate].
    exact (regrow0_sound st r hargs wnl st1 aw ws ca c sts K E ms model Hpc TO AP FRS PCA (ex_intro _ b0 (conj EB B00)) HAP HS0 HMP HPB Hk).
  - destruct (PkStack.c_ee c) as [|kT oe| | | | | | | | |] eqn:EE; try discriminate.
    destruct (PkStack.c_ecap c) as [|kB' oc| | | | | | | | |] eqn:EC; try discriminate.
    destruct (PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63)) eqn:Q; [|discriminate].
    apply andb_prop in Q as [Q OE]. apply andb_prop in Q as [KBB OB]. apply Uint63.eqb_correct in KBB. subst kB'.
    apply (proj1 (weqb_ok _ _)) in OB. apply (proj1 (weqb_ok _ _)) in OE. subst ob oe.
    exact (regrow1_sound st r hargs wnl st1 aw ws ca c kB kT oc sts K E ms model Hpc TO AP FRS PCA EB EE EC HAP HS0 HMP HPB Hk).
Qed.
End Sound.
End PkRegrowA.

Module TwinB.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Sem.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.PropExec OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.MState OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Cells OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Frame OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Lib.Omono.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.CtrFX OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br.MemFX.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Arith OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Ops OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Tree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GUnp OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.G3 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GWin OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStack OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkAux.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.LiaFast.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Seal OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsKeep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkRegrow.
Import Actr.TwinB.
Import PkRegrowAC.TwinB.

Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP PlanS UB HeapOp UO UG GU G3 GW TR PK PKL CtrLib CtrFX PkAux.
Open Scope Z_scope.
Unset Lia Cache.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Import PkRegrow PkRegrowAC.TwinB.PkRegrowAC.

Module PkRegrowA.
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

Section Geom.
Variable segs : list Segment.

Lemma regrow1_geom : forall E (fs : list fact) LB wsZ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP,
  ev E 0%uint63 = Z_to_bv 64 0 -> facts_hold E fs ->
  implied fs (FULe (VP kT (wlit 24%uint63)) (VP kB oc)) = true -> implied fs (FULe (VP kB oc) (VP kT (wlit 24%uint63))) = true ->
  wt oc = false -> 24 <= w2Z oc -> w2Z oc < 140737488355328 ->
  In (Win (bv_unsigned (ev E kT)) 24 6) wsZ ->
  PK.cw_pk_holds segs (map (den E) [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP]) LB wsZ m ->
  exists g ls u, decode_pk (map (den E) [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP]) = Some u /\
    link_pk u g ls /\ pure_pk g ls /\ own_pk g LB /\ wins_pk g wsZ /\ mem_pk (bmem_of segs m) u g ls /\ ghost_pk g wsZ /\ cost_pk u g ls wsZ /\
    v_begin (k_evec g) = bv_unsigned (ev E kB) /\ v_end (k_evec g) = bv_unsigned (ev E kT) + 24 /\ v_capend (k_evec g) = bv_unsigned (ev E kB) + w2Z oc /\
    bv_unsigned (den E (VP kT (wlit 24%uint63))) = bv_unsigned (ev E kT) + 24 /\ bv_unsigned (den E (VP kB oc)) = bv_unsigned (ev E kB) + w2Z oc /\
    vec_valid (k_evec g) /\ ecap_ok (v_cap (k_evec g)) /\ w2Z oc = 24 * v_cap (k_evec g) /\ v_size (k_evec g) = v_cap (k_evec g) /\
    bv_unsigned (ev E kT) + 24 = bv_unsigned (ev E kB) + w2Z oc.
Proof.
  intros E fs LB wsZ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40 RT HC.
  unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & LK & P & O & Wk & M & GH & CO).
  exists g, ls. eexists. split; [cbn [map decode_pk]; reflexivity|].
  split; [exact LK|]. split; [exact P|]. split; [exact O|]. split; [exact Wk|]. split; [exact M|]. split; [exact GH|]. split; [exact CO|].
  pose proof LK as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  set (V := k_evec g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (L := w2Z oc) in *.
  change (v_begin V = bv_unsigned (den E (VP kB wzero))) in Leb.
  change (v_end V = bv_unsigned (den E (VP kT (wlit 24%uint63)))) in Lee.
  change (v_capend V = bv_unsigned (den E (VP kB oc))) in Lecap.
  assert (RT' : Tz + 24 < two64).
  { pose proof (proj1 (Forall_forall _ _) Wk _ RT) as X. cbn [w_kind] in X.
    destruct (X ltac:(unfold HeapOp.K_STACK; lia)) as [[[KD|KD] _]|[_ ET]].
    - unfold HeapOp.K_BLOCK in KD. discriminate KD.
    - unfold K_GHOST in KD. lia.
    - destruct ET as (_ & _ & _ & _ & E5). cbn [w_lo w_len] in E5. fold V in E5. rewrite Lecap in E5.
      pose proof (bv_unsigned_in_range 64 (den E (VP kB oc))) as RC. rewrite bv_modulus_64 in RC. clear - E5 RC. unfold two64 in *. lia. }
  clear RT. rename RT' into RT.
  rewrite (den_VP0 E kB wzero (weqb_refl _)) in Leb. fold Bz in Leb.
  assert (DVE : bv_unsigned (den E (VP kT (wlit 24%uint63))) = Tz + 24).
  { apply den_VP_nowrap. rewrite wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. exact RT. }
  rewrite DVE in Lee.
  pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP1) as IM1. pose proof (implied_sound E fs _ Pz0 Pfacts0 IMP2) as IM2.
  cbn [fact_holds] in IM1, IM2. rewrite DVE in IM1, IM2.
  assert (VCE : v_capend V = Bz + 24 * v_cap V) by (unfold v_capend; rewrite EL, Leb; reflexivity).
  assert (VEN : v_end V = Bz + 24 * v_size V) by (unfold v_end; rewrite EL, Leb; reflexivity).
  pose proof (bv_unsigned_in_range 64 (ev E kB)) as RB. rewrite bv_modulus_64 in RB. fold Bz in RB.
  pose proof (bv_unsigned_in_range 64 (ev E kT)) as RTz. rewrite bv_modulus_64 in RTz. fold Tz in RTz.
  pose proof (w2Z_range oc) as ROC. fold L in ROC.
  assert (VVAL : vec_valid V /\ ecap_ok (v_cap V)).
  { destruct VE as [(B0 & C0 & LS0)|VV]; [| exact VV]. exfalso.
    rewrite VEN in Lee. subst ls. cbn [length Z.of_nat] in SZ. rewrite SZ, <- Leb, B0 in Lee. clear - Lee RTz. lia. }
  destruct VVAL as (VVAL & CPOS & CPOW).
  assert (DVC : bv_unsigned (den E (VP kB oc)) = Bz + L).
  { assert (DM : bv_unsigned (den E (VP kB oc)) = (Bz + L) mod two64) by (cbn [den]; rewrite bv_add_unsigned, wbv_unsigned, wrap64; reflexivity).
    destruct (Z_lt_le_dec (Bz + L) two64) as [LT2|GE2].
    - rewrite Z.mod_small in DM by (clear - LT2 RB ROC; lia). exact DM.
    - exfalso. rewrite <- (Z.mod_unique (Bz + L) two64 1 (Bz + L - two64)) in DM by (clear - GE2 RB ROC L40; unfold two64 in *; lia).
      rewrite VCE, DM in Lecap. clear - Lecap CPOS L40 RB. unfold two64 in *. lia. }
  rewrite DVC in Lecap, IM1, IM2.
  split; [exact Leb|]. split; [exact Lee|]. split; [exact Lecap|]. split; [exact DVE|]. split; [exact DVC|].
  split; [exact VVAL|]. split; [exact (conj CPOS CPOW)|].
  split; [clear - VCE Lecap; lia|]. split; [clear - VEN Lee VCE Lecap IM1 IM2; lia| clear - IM1 IM2; lia].
Qed.
End Geom.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Hypothesis CW3' : forall ca LB ws m, PK.cw_pk_holds segs ca LB ws m -> cw_holds CW 3 ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Variable SRCPAT : sstate -> list (int * sv * w64) -> int -> sv -> bool.
Variable MEMCPY_PC : int.

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
  (forall LB, cw_holds CW (to_Z md) (map (den E) ca) LB (map (wden E) ws) (ms_mem ms) ->
     In (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) LB /\
     (forall w, In w (map (wden E) ws) -> (w_kind w = HeapOp.K_BLOCK \/ K_GHOST <= w_kind w) ->
                forall a, in_iv (w_iv w) a -> ~ in_iv (bv_unsigned (ev E kb), bv_unsigned (den E nsv)) a)) ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' ->
     (forall i, 0 <= i < nZ -> exists b, rb segs (ms_mem ms') (bv_unsigned (ev E ka) + i) = Some b /\ rb segs (ms_mem ms') (bv_unsigned (ev E kb) + i) = Some b /\
                                         rb segs (ms_mem ms) (bv_unsigned (ev E kb) + i) = Some b) ->
     realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Hypothesis AVECCOPY0 : forall st (K : TSet) E ms mo r hargs wnl st1,
  st_ok segs OPS E st ms mo -> MP mo -> s_pc st = MEMCPY_PC ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) ->
  bv_unsigned (den E (getr st X12)) = 0 ->
  (forall E' ms' mo', env_ext (s_next st) E E' -> MP mo' -> st_ok segs OPS E' (sink st st1 r) ms' mo' -> realizes segs (mkCfg ms' mo') K) ->
  realizes segs (mkCfg ms mo) K.

Lemma regrow0_sound : forall st r hargs wnl st1 aw ws ca c sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  PkStack.parse_ca ca = Some c -> (exists b0, PkStack.c_eb c = VL b0 /\ weqb b0 wzero = true) ->
  regrow0 st (sink st st1 r) aw ws c = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca c sts K E ms model Hpc TO AP FRS PCA (b0 & EB & B00) HAP HS0 HMP HPB Hk.
  apply (proj1 (weqb_ok _ _)) in B00. subst b0.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb] in EB. subst eb.
  unfold regrow0 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP. rewrite SF in HAP.
  set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 0) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OK6]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B]. apply andb_prop in COND as [COND WLEN].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [EE0 EC0].
  apply sv_eqb_eq in EE0. apply sv_eqb_eq in EC0. subst ee ecap.
  apply negb_true_iff in KN0. apply negb_true_iff in KN1. apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN.
  apply andb_prop in COND2 as [COND2 BGN]. apply andb_prop in COND2 as [COND2 WN]. apply andb_prop in COND2 as [LON HIN].
  apply Uint63.eqb_correct in LON. apply sv_eqb_eq in HIN.
  destruct (call_pre_inv st r CP) as (RESV & FROK & EVEN & rav & X1V & RWT & RLT & ->).
  destruct (fresh_ok_inv st FROK) as (VB & NPOS & N62). fold n0 in VB, NPOS, N62.
  pose proof HS0 as [Ppc0 Px00 Pregs0 Pfregs0 Psvc0 Presv0 Pfcsr0 Prom0 Pz0 Pbst0 Preg0 Pdisj0 Ppub0 Pfacts0 Pops0 Papart0 Pmf0 Pcov0 Pminv0].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VL wzero; VL wzero; VL wzero; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
  assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
  { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
    repeat split; right; right; right; apply in_app_iff; left; assumption. }
  assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
  { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
  assert (KN_LT : to_Z kN < to_Z n0) by exact (LTn kN wzero (proj1 (INW _ EXN))).
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).
  set (Nz := bv_unsigned (ev E kN)) in *.
  pose proof (bv_unsigned_in_range 64 (ev E kN)) as RNz. rewrite bv_modulus_64 in RNz. fold Nz in RNz.

  assert (N12V : bv_unsigned (den E n12) = 0).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu den]. rewrite bv_sub_unsigned, wrap64, wbv_unsigned, wzero_ok. reflexivity.
    - apply sv_eqb_eq in LEN. rewrite LEN. replace (sv_alu ALU_SUB (VL wzero) (VL wzero)) with (VL wzero) by (vm_compute; reflexivity).
      cbn [den]. rewrite wbv_unsigned, wzero_ok. reflexivity.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? 0) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; unfold two64 in *; lia).
      rewrite Q2. fold Nz. replace (Nz + 0 - 0) with Nz by lia. rewrite Z.mod_small by (unfold two64 in *; lia). subst Nz. reflexivity. }

  apply (AVECCOPY0 st K E ms model (wl rav) hargs wnl (setregs st R') HS0 HMP Hpc AP).
  - fold n12. exact N12V.
  - intros E' ms' mo' HX' HMP' HSS.
    {
    set (E1 := E') in *. set (M' := ms_mem ms') in *. set (nT := s_next stS) in *.
    assert (HX : env_ext n0 E E1) by exact HX'.
    assert (EVN1 : ev E1 kN = ev E kN) by exact (proj1 (proj2 HX kN KN_LT)).
    pose proof HSS as HSE1.
    pose proof HSE1 as [_ _ _ _ _ _ _ _ Pz1 Pbst1 Preg1 Pdisj1 _ Pfacts1 Pops1 _ _ _ _].
    fold stS in Pfacts1, Pops1, Preg1, Pdisj1. rewrite SF in Pfacts1. fold fs in Pfacts1.
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
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
    apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
    destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
    pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
    cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
    pose proof P as (LV & EL & SZ & VE & CE & ZV).
    pose proof M as (M1 & M2 & M3 & M4 & M5).
    assert (VB0 : v_begin (k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
    destruct VE as [(_ & VC0 & LS0)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)]. subst ls.
    set (bm' := bmem_of segs M') in *.

    pose proof (Preg1 kN rN FN) as ROKN.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (HIN' : hiZ E1 rN = 24) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKN KN0) as RNr. rewrite LON', HIN', EVN1 in RNr. fold Nz in RNr.
    pose proof (aw_ceiling_small segs IMGX AW mo') as CEIL. unfold two62Z in CEIL.
    set (wN := (VP kN wzero, VL (wlit 24%uint63), VL (wlit 1%uint63))) in *.
    assert (WNd1 : wden E1 wN = Win Nz 24 HeapOp.K_BLOCK).
    { unfold wden, wN. rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1. cbn [den]. rewrite !wbv_unsigned, !wlit_ok. reflexivity. }

    assert (NLB : In (Nz, 24) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
      - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
      - exact IN.
      - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
    assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 24 -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
    assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
    pose proof HA as HA'.

    set (wNT := top_win kN 24%uint63 ETOPk).
    set (ws' := map (fun w => if win3_eqb w wN then wNT else w) ws).
    set (ca' := [root; rootT; n1; P1; zh; c0; VP kN wzero; VP kN wzero; VP kN (wlit 24%uint63); tptr; trest; tmap; tkey; cf; fT; fN; fP]).
    assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN) \/ w = wNT).
    { intros w Hw. subst ws'. apply in_map_iff in Hw as (x & EQx & Hx). destruct (win3_eqb x wN) eqn:Q.
      - right. symmetry. exact EQx.
      - left. subst w. split; [exact Hx|]. intros ->. rewrite win3_eqb_refl in Q. discriminate Q. }
    assert (LENws' : Z.of_nat (length ws') < two63) by (subst ws'; rewrite length_map; unfold two63; clear - WLEN; lia).
    assert (WNTd : wden E1 wNT = Win Nz 24 6) by (subst wNT; rewrite top_win_den, EVN1; reflexivity).
    assert (Db' : bv_unsigned (den E1 (VP kN wzero)) = Nz) by (rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
    assert (Dcap' : bv_unsigned (den E1 (VP kN (wlit 24%uint63))) = Nz + 24).
    { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, EVN1; fold Nz; change (to_Z 24%uint63) with 24; [reflexivity| alia]. }
    set (g' := PKG (k_tree g) (mkVec Nz 0 1 24) (k_zone g)).
    apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH []
             [] (mk_args 3%uint63 aw ws' ca') _ nT).
    -   intros k [].
    -   constructor.
    -   intros k rr [].
    -   intros k rr [].
    -   intros k rr a [].
    -   intros k1 r1 k2 r2 a [].
    -   rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
      split; [apply mk_args_sound; exact LENws'|].
      split.
      { pose proof HA' as HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
        - intros x Hx. destruct (KEPTW x Hx) as [[Hx' _]| ->]; [left; exact Hx'| right; apply UOK.kind_new_sub; reflexivity].
        - intros x Hx. destruct (UOK.map_replace_old ws wN wNT x Hx) as [H1| ->]; [left; exact H1| right].
          rewrite WNd1. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
          exists (Nz, 24). split; [exact NLB|]. split; [unfold in_iv; cbn [fst snd w_lo]; clear; lia|]. left. unfold c24, C24_LO, C24_HI. cbn [snd]. clear. lia. }
      split.
      +
        unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPTW x Hx) as [[Hx' _]| ->].
        * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
        * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
          right; right. split; [unfold HeapOp.K_SUB; alia|]. exists (Nz, 24). split; [exact NLB|]. intros a Ha. exact Ha.
      +
        apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
        assert (VNV : vec_valid (mkVec Nz 0 1 24)) by (unfold vec_valid; cbn [v_elt v_size v_cap v_begin]; split; [alia|]; split; [alia|]; split; [exact NZ0| exact NZ8]).
        assert (OWN' : owned g' = (Nz, 24) :: map chunk_block (z_chunks (k_zone g))).
        { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone v_begin]. rewrite (proj2 (Z.eqb_neq _ _) NZ0). reflexivity. }
        assert (OWNo : owned g = map chunk_block (z_chunks (k_zone g))).
        { unfold owned, evec_blocks. rewrite VB0. reflexivity. }
        exists g', []. split; [| split; [| split; [| split]]].
        *
          unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP last_opt rev].
          rewrite Db', Dcap'. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
          split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
          split; [reflexivity|]. split; [alia|]. split; [alia|].
          cbn [last_opt rev] in LTOP. split; [exact LTOP|].
          intros CF. destruct (LCF CF) as (X & _). exfalso. exact (X eq_refl).
        *
          unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone v_elt v_size v_cap v_begin]. unfold v_capend. cbn [v_begin v_elt v_cap].
          split; [exact LV|]. split; [reflexivity|]. split; [reflexivity|]. split; [right; split; [exact VNV| split; [lia| split; [reflexivity| lia]]]|]. split; [alia| exact ZV].
        *
          unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF. split.
          -- intros b [<-|Hb]; [exact NLB| exact (OL b Hb)].
          -- constructor; [| exact OF]. apply Forall_forall. intros cb Hcb.
             pose proof (DISJN cb ltac:(rewrite OWNo; exact Hcb)) as D. unfold rdisj. cbn [fst snd].
             apply in_map_iff in Hcb as (ch & <- & Hch). unfold chunk_block. cbn [fst snd].
             destruct ZV as ((_ & _ & V3 & _) & _). destruct (V3 ch Hch) as (_ & _ & S3).
             destruct (Z_lt_le_dec (fst ch) (Nz + 24)) as [A1|A1]; [| left; exact A1].
             destruct (Z_lt_le_dec Nz (fst ch + (CHUNK_HDR + snd ch))) as [A2|A2]; [| right; exact A2].
             exfalso. destruct (Z_lt_le_dec (fst ch) Nz) as [A3|A3].
             ++ apply (D Nz ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
             ++ apply (D (fst ch) ltac:(alia)). unfold in_iv, chunk_block. cbn [fst snd]. unfold CHUNK_HDR, CHUNK_SIZE0 in *. alia.
        *
          unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx).
          rewrite OWN'.
          destruct (KEPTW x Hx) as [[Hx' NxN]| ->].
          --
             destruct (proj1 (Forall_forall _ _) Wk (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]]; [| destruct ET as (_ & NE0 & _); exfalso; exact (NE0 VB0)].
             left. split; [exact KDx|]. intros b [<-|Hb] a Ha Hb'.
             ++ unfold in_iv in Hb'. cbn [fst snd] in Hb'.
                pose proof (new_block_apart segs IMGX AW E1 fs (s_regs stS) _ LB M' mo' kN rN 24 ws wN wN x Pfacts1 Pdisj1 FN KN0 LON HIN' ltac:(lia) WN HA
                         ltac:(rewrite EVN1; exact NLB) WF KL OBK NOA SWO EXN ltac:(rewrite EVN1; exact WNd1) Hx' NxN NxN NS a Ha) as NBA. rewrite EVN1 in NBA. exact (NBA Hb').
             ++ exact (DJ b ltac:(rewrite OWNo; exact Hb) a Ha Hb').
          -- right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
             unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
             split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia.
        *
          split.
          2: { split; [destruct GH as [SE EP]; split|].
               3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| reflexivity].
                    intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                    destruct (KEPTW x Hx) as [[Hx' _]| ->]; [apply in_map; exact Hx'|].
                    exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
               - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
                 destruct (KEPTW x Hx) as [[Hx' _]| ->]; [apply in_map; exact Hx'|].
                 exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
               - intros _. exists (wden E1 wNT). split.
                 + apply in_map. subst ws'. apply in_map_iff. exists wN. rewrite win3_eqb_refl. split; [reflexivity| exact EXN].
                 + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec v_begin]. unfold v_end, v_capend. cbn [v_begin v_elt v_size v_cap].
                   split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. alia. }
          unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone v_begin]. fold bm'.
          split; [exact M1|]. split; [exact M2|]. split; [exact M3|].
          split; [exact M4|]. intros _. cbn. exact I.
    -
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
      assert (NWi : forall w, In w ws' -> ~ in_iv (w_iv (wden E1 w)) a).
      { intros w Hw Hin. apply NW. apply (proj2 (in_ws_map_iff E1 ws' a)). exists w. auto. }
      split; [| intros k rr []].
      left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))).
      split; [exact RA0|]. split; [exact NI|]. intros IW. apply (proj1 (in_ws_map_iff E1 ws a)) in IW as (w & Hw & Hin).
      destruct (win3_eqb w wN) eqn:QN.
      + apply win3_eqb_eq in QN. subst w. apply (NWi wNT); [subst ws'; apply in_map_iff; exists wN; rewrite win3_eqb_refl; auto|].
        rewrite WNTd. rewrite WNd1 in Hin. exact Hin.
      + apply (NWi w); [subst ws'; apply in_map_iff; exists w; rewrite QN; auto|]. exact Hin.
    -   constructor.
    }
Qed.

Lemma regrow1_sound : forall st r hargs wnl st1 aw ws ca c kB kT oc sts (K : TSet) E ms model,
  s_pc st = MEMCPY_PC -> the_op st = Some (3%uint63, aw, ws, ca) ->
  ActrA.acall_pre ActrA.ASTACK None st = Some (r, hargs, wnl, st1) -> fresh_ok (sink st st1 r) = true ->
  PkStack.parse_ca ca = Some c -> PkStack.c_eb c = VP kB wzero -> PkStack.c_ee c = VP kT (wlit 24%uint63) -> PkStack.c_ecap c = VP kB oc ->
  regrow1 SRCPAT st (sink st st1 r) wnl aw ws c kB kT oc = Some sts ->
  st_ok segs OPS E st ms model -> MP model -> PB (eb E) ->
  (forall st', In st' sts -> forall E' ms' model', env_ext (s_next st) E E' -> MP model' -> st_ok segs OPS E' st' ms' model' ->
     realizes segs (mkCfg ms' model') K) ->
  realizes segs (mkCfg ms model) K.
Proof.
  intros st r hargs wnl st1 aw ws ca c kB kT oc sts K E ms model Hpc TO AP FRS PCA EB EE EC HAP HS0 HMP HPB Hk.
  destruct (acall_pre_inv _ _ _ _ _ _ _ AP) as (CP & R' & ->).
  pose proof (sink_fields st R' r) as (SF & SO & SPV & SN & SX10 & SPC). cbv zeta in SF, SO, SPV, SN, SX10, SPC.
  set (stS := sink st (setregs st R') r) in *.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate PCA.
  cbn [PkStack.parse_ca] in PCA. injection PCA as <-.
  cbn [PkStack.c_eb PkStack.c_ee PkStack.c_ecap] in EB, EE, EC. subst eb ee ecap.
  unfold regrow1 in HAP.
  cbn [PkStack.c_root PkStack.c_rootT PkStack.c_n1 PkStack.c_P1 PkStack.c_zh PkStack.c_c0 PkStack.c_eb PkStack.c_ee PkStack.c_ecap
       PkStack.c_tptr PkStack.c_trest PkStack.c_tmap PkStack.c_tkey PkStack.c_cf PkStack.c_fT PkStack.c_fN PkStack.c_fP PkStack.unparse_ca] in HAP.
  cbv zeta in HAP. rewrite SF in HAP.
  set (L := w2Z oc) in HAP. set (dx := getr st X10) in HAP. set (n12 := getr st X12) in HAP.
  destruct (dst_anchor dx n12 L) as [kN|] eqn:DA; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND; [|discriminate] end.
  destruct (IMap.find kN (s_regs stS)) as [rN|] eqn:FN; [|discriminate].
  destruct (IMap.find kT (s_regs stS)) as [rT|] eqn:FT; [|discriminate].
  match type of HAP with (if ?cc then _ else _) = _ => destruct cc eqn:COND2; [|discriminate] end.
  destruct (gcells rT 0%uint63) as [t0|] eqn:GT0; [|discriminate]. destruct (gcells rT 1%uint63) as [t1|] eqn:GT1; [|discriminate].
  destruct (gcells rT 2%uint63) as [t2|] eqn:GT2; [|discriminate].
  destruct (gcells rN (Uint63.of_Z (L / 8))) as [e0|] eqn:GN0; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 1%uint63)) as [e1|] eqn:GN1; [|discriminate].
  destruct (gcells rN (PrimInt63.add (Uint63.of_Z (L / 8)) 2%uint63)) as [e2|] eqn:GN2; [|discriminate].
  match type of HAP with Some [?X] = Some _ => set (st' := X) in HAP end.
  injection HAP as <-.
  set (n0 := s_next st) in *. set (fs := s_facts st) in *.

  apply andb_prop in COND as [COND SRCP]. apply andb_prop in COND as [COND VCP].
  apply andb_prop in COND as [COND SWO]. apply andb_prop in COND as [COND OBK]. apply andb_prop in COND as [COND KL].
  apply andb_prop in COND as [COND RNZ]. apply andb_prop in COND as [COND ALN].
  apply andb_prop in COND as [COND OKT]. apply andb_prop in COND as [COND EXT]. apply andb_prop in COND as [COND NOA]. apply andb_prop in COND as [COND EXN].
  apply andb_prop in COND as [COND IMP2]. apply andb_prop in COND as [COND IMP1]. apply andb_prop in COND as [COND LEN]. apply andb_prop in COND as [COND X11B].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND TKB].
  apply andb_prop in COND as [COND NNT]. apply andb_prop in COND as [COND NNB].
  apply andb_prop in COND as [COND KN1]. apply andb_prop in COND as [COND KN0]. apply andb_prop in COND as [COND KT0]. apply andb_prop in COND as [COND KB0].
  apply andb_prop in COND as [COND L40]. apply andb_prop in COND as [COND L8]. apply andb_prop in COND as [OCT L24].
  apply negb_true_iff in OCT. apply Z.leb_le in L24. apply Z.eqb_eq in L8. apply Z.ltb_lt in L40.
  apply negb_true_iff in KN0. apply negb_true_iff in KT0. apply negb_true_iff in KB0. apply negb_true_iff in KN1.
  apply neqb_neq in NNT. apply neqb_neq in NNB.
  apply Z.ltb_lt in WLEN. apply sv_eqb_eq in X11B.
  apply existsb_win_In in EXN. apply existsb_win_In in EXT.
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

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n0 st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n0) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBdx : sv_vars_below n0 dx = true) by (subst dx; unfold getr; exact (rf_allb_get _ _ _ VBrf X10)).

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  pose proof HC as HCm. apply CW3 in HC.
  set (wT := top_win kT 24%uint63 ETOPk) in *.
  assert (WTd : forall E0, wden E0 wT = Win (bv_unsigned (ev E0 kT)) 24 6) by (intros E0; subst wT; rewrite top_win_den; reflexivity).
  assert (L40' : w2Z oc < 140737488355328) by exact L40.
  destruct (regrow1_geom segs E fs LB _ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40'
              ltac:(rewrite <- (WTd E); apply in_map; exact EXT) HC)
    as (g & ls & u & DU & LK & P & O & Wk & M & GH & CO & Leb & Lee & Lecap & DVE & DVC & VVAL & (CPOS & CPOW) & LCAP & SZC & TZ24).
  fold L in Lecap, DVC, LCAP, TZ24.
  pose proof P as (LV & EL & SZ & VE & CE & ZV). pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
  set (V := k_evec g) in *.
  set (Bz := bv_unsigned (ev E kB)) in *. set (Tz := bv_unsigned (ev E kT)) in *. set (Nz := bv_unsigned (ev E kN)) in *.

  pose proof (Preg0 kN ra FNst) as ROKa.
  assert (LOa' : loZ ra = 0) by (unfold loZ; rewrite LOa; reflexivity).
  pose proof (w2Z_range oc) as ROC. fold L in ROC. unfold two40Z in L40.
  assert (L2w : w2Z (wlit (Uint63.of_Z (2 * L))) = 2 * L).
  { rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63, two63_eq. alia. }
  assert (HIa' : hiZ E ra = 2 * L) by (unfold hiZ; rewrite HIa; cbn [den]; rewrite wbv_unsigned; exact L2w).
  pose proof (ro_range _ _ _ _ _ _ ROKa KN0) as RNr. rewrite LOa', HIa' in RNr. fold Nz in RNr.

  assert (N12V : bv_unsigned (den E n12) = L).
  { unfold len_ok in LEN. apply orb_prop in LEN as [LEN|LEN]; [apply orb_prop in LEN as [LEN|LEN]|].
    - apply sv_eqb_eq in LEN. rewrite LEN, den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - apply sv_eqb_eq in LEN. rewrite LEN, den_sv_alu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, DVE, (den_VP0 E kB wzero (weqb_refl _)). fold Bz Tz.
      rewrite TZ24. replace (Bz + L - Bz) with L by (clear; lia). apply Z.mod_small. clear - ROC. unfold two64 in *. lia.
    - destruct n12 as [w| | | | | | | | | |]; try discriminate. apply andb_prop in LEN as [NT WL]. apply negb_true_iff in NT. apply Z.eqb_eq in WL.
      cbn [den]. rewrite wbv_unsigned. exact WL. }
  assert (DXV : den E dx = ev E kN).
  { unfold dst_anchor in DA. destruct dx as [|k o0|op a1 a2| | | | | | | |] eqn:EDX; try discriminate.
    - destruct (weqb o0 wzero) eqn:Q; [|discriminate]. injection DA as ->. apply (proj1 (weqb_ok _ _)) in Q. subst o0.
      apply bv_eq. exact (den_VP0 E kN wzero (weqb_refl _)).
    - destruct op; try discriminate. destruct a1 as [|k o0| | | | | | | | |]; try discriminate.
      destruct (negb (wt o0) && (w2Z o0 =? L) && sv_eqb a2 n12) eqn:Q; [|discriminate]. injection DA as ->.
      apply andb_prop in Q as [Q Q3]. apply andb_prop in Q as [Q1 Q2]. apply sv_eqb_eq in Q3. subst a2. apply Z.eqb_eq in Q2.
      apply bv_eq. rewrite den_VAlu. cbn [alu64 alu]. rewrite bv_sub_unsigned, wrap64, N12V, (den_VP_nowrap E kN o0) by (rewrite Q2; fold Nz; alia).
      rewrite Q2. fold Nz. replace (Nz + L - L) with Nz by alia. rewrite Z.mod_small by (unfold two64; alia). subst Nz. reflexivity. }

  set (wN := (VP kN wzero, VL (wlit (Uint63.of_Z (2 * L))), VL (wlit 1%uint63))) in *.
  assert (WNd : forall E0, ev E0 kN = ev E kN -> wden E0 wN = Win Nz (2 * L) HeapOp.K_BLOCK).
  { intros E0 EV0. unfold wden, wN. rewrite (den_VP0 E0 kN wzero (weqb_refl _)), EV0. cbn [den]. rewrite !wbv_unsigned, L2w, wlit_ok. reflexivity. }
  assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
  { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite (WNd E eq_refl) in WW.
    destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
    apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
  assert (VBY : v_bytes V = 24 * v_cap V) by (unfold v_bytes; rewrite EL; reflexivity).
  assert (VOWN : In (Bz, L) (owned g)) by (rewrite <- Leb, LCAP, <- VBY; apply owned_evec; fold V; exact VV3).
  assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
  { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
    intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }

  apply (AVECCOPY st K E ms model (wl rav) hargs wnl (setregs st R') kN ra (VL (wlit (Uint63.of_Z (2 * L)))) kB (VL oc) L 3%uint63 aw ws
           [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] HS0 HMP Hpc AP).
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
    intros LB' HC'. change (to_Z 3%uint63) with 3 in HC'. apply CW3 in HC'.
    destruct (regrow1_geom segs E fs LB' _ m root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz0 Pfacts0 IMP1 IMP2 OCT L24 L40'
                ltac:(rewrite <- (WTd E); apply in_map; exact EXT) HC')
      as (g' & ls' & u' & _ & _ & P' & O' & Wk' & _ & _ & _ & Leb' & _ & _ & _ & _ & VVAL' & _ & LCAP' & _ & _).
    cbn [den]. rewrite wbv_unsigned. fold L Bz.
    destruct P' as (_ & EL' & _). destruct VVAL' as (_ & _ & VV3' & _).
    pose proof (owned_evec g' VV3') as OW'. rewrite Leb' in OW'. unfold v_bytes in OW'. rewrite EL' in OW'. unfold ELEM_SIZE in OW'. fold L in LCAP'. rewrite <- LCAP' in OW'. fold Bz in OW'.
    split; [exact (proj1 O' _ OW')|].
    intros w0 Hw0 KD0 a Ha0 Hb0.
    destruct (proj1 (Forall_forall _ _) Wk' w0 Hw0 ltac:(unfold HeapOp.K_STACK, HeapOp.K_BLOCK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
    + exact (DJ _ OW' a Ha0 Hb0).
    + destruct ET as (K6 & _). unfold K_ETOP, HeapOp.K_BLOCK, K_GHOST in *. lia.
  -
    intros E' ms' mo' HX' HMP' HSS COPYB.
    {
    clear DEC.
    clear g ls u DU LK P O Wk M GH CO Leb Lee Lecap DVE DVC VVAL CPOS CPOW LCAP SZC TZ24 LV EL SZ VE CE ZV VV1 VV2 VV3 VV4 VBY VOWN DISJN SEP HA WF HC HCm V LB.
    set (nT := s_next stS) in *.
    destruct (fresh_ok_inv stS FRS) as (VBS & NPOSS & N62S). fold nT in VBS, NPOSS, N62S.
    set (M' := ms_mem ms') in *.
    assert (TZ15 : to_Z nT = to_Z n0 + 15).
    { subst nT. rewrite SN. fold n0. rewrite add_Z by (change (to_Z 15%uint63) with 15; rewrite wB_two63, two63_eq; alia). reflexivity. }
    assert (TZ16 : to_Z (PrimInt63.add nT 1) = to_Z n0 + 16).
    { rewrite add_Z by (change (to_Z 1%uint63) with 1; rewrite wB_two63, two63_eq; alia). rewrite TZ15. change (to_Z 1%uint63) with 1. lia. }
    set (NT := Nz + L - 24).
    set (Fv := fun _ : Z => Z_to_bv 64 NT). set (Gv := fun (_ : Z) (_ : Z) => Z_to_bv 8 0).
    set (E1 := env_above E' nT Fv Gv).
    assert (HX1 : env_ext nT E' E1) by (subst E1; apply env_above_ext).
    assert (HX : env_ext n0 E E1) by (apply (env_ext_trans n0 nT E E' E1); [lia| exact HX'| exact HX1]).
    assert (ENT : ev E1 nT = Z_to_bv 64 NT) by (subst E1; rewrite ev_above by lia; reflexivity).

    assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; VP kB wzero; VP kT (wlit 24%uint63); VP kB oc; tptr; trest; tmap; tkey; cf; fT; fN; fP] -> In v (op_args o)).
    { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }
    assert (INW : forall w, In w ws -> In (fst (fst w)) (op_args o) /\ In (snd (fst w)) (op_args o) /\ In (snd w) (op_args o)).
    { intros [[w1 w2] w3] Hw. destruct (in_flat_windows ws w1 w2 w3 Hw) as (I1 & I2 & I3). rewrite ARGS. cbn [fst snd].
      repeat split; right; right; right; apply in_app_iff; left; assumption. }
    assert (LTn : forall k o', In (VP k o') (op_args o) -> to_Z k < to_Z n0).
    { intros k o' Hko. pose proof (VBo _ Hko) as X. cbn [sv_vars_below] in X. apply Uint63.ltb_spec in X. exact X. }
    assert (KB_LT : to_Z kB < to_Z n0) by exact (LTn kB wzero (INCA (VP kB wzero) ltac:(inlist))).
    assert (KT_LT : to_Z kT < to_Z n0) by exact (LTn kT (wlit 24%uint63) (INCA (VP kT (wlit 24%uint63)) ltac:(inlist))).
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
    destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
    pose proof (DECf E1) as DEC. rewrite DEC in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
    apply CW3 in HC.
    destruct (regrow1_geom segs E1 fs LB _ M' root rootT n1 P1 zh c0 kB kT oc tptr trest tmap tkey cf fT fN fP Pz1 Pfacts1 IMP1 IMP2 OCT L24 L40'
                ltac:(rewrite <- (WTd E1); apply in_map; exact EXT) HC)
      as (g & ls & u & DU & LK & P & O & Wk & M & GH & CO & Leb & Lee & Lecap & DVE & DVC & VVAL & (CPOS & CPOW) & LCAP & SZC & TZ24).
    rewrite EVB1 in Leb, Lecap, DVC, TZ24. rewrite EVT1 in Lee, DVE, TZ24. fold L Bz Tz in Leb, Lee, Lecap, DVE, DVC, LCAP, TZ24.
    cbn [map decode_pk] in DU. injection DU as <-.
    pose proof LK as (LT & LN & LP & Lc0 & _ & _ & _ & LTOP & LCF).
    cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, LTOP, LCF.
    pose proof P as (LV & EL & SZ & VE & CE & ZV). pose proof VVAL as (VV1 & VV2 & VV3 & VV4).
    pose proof M as (TW2 & KA2 & ICB2 & CH2 & PE2).
    set (V := k_evec g) in *.
    set (bm' := bmem_of segs M') in *.
    pose proof (aw_ceiling_small segs IMGX AW mo') as CEIL. unfold two62Z in CEIL.
    assert (VCE : v_capend V = Bz + 24 * v_cap V) by (unfold v_capend; rewrite EL, Leb; reflexivity).
    assert (VEN : v_end V = Bz + 24 * v_size V) by (unfold v_end; rewrite EL, Leb; reflexivity).
    assert (VBY : v_bytes V = 24 * v_cap V) by (unfold v_bytes; rewrite EL; reflexivity).
    pose proof (proj1 O _ (owned_evec g VV3)) as VLB. fold V in VLB. rewrite Leb in VLB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ M' mo' _ HA VLB) as (Bb1 & Bb2 & Bb3 & Bb4 & _). cbn [fst snd] in Bb1, Bb2, Bb3.
    assert (CAP2 : 2 * v_cap V <= 1024).
    { apply (PKL.cap_double_ok (k_tree g) ls); [exact (proj1 CPOW)| exact LV| exact (proj2 ZV)| rewrite <- SZC; exact SZ]. }

    pose proof (Preg1 kN rN FN) as ROKN. pose proof (Preg1 kT rT FT) as ROKT.
    assert (LON' : loZ rN = 0) by (unfold loZ; rewrite LON; reflexivity).
    assert (LOT' : loZ rT = 0) by (unfold loZ; rewrite LOT; reflexivity).
    assert (HIN' : hiZ E1 rN = 2 * L) by (unfold hiZ; rewrite HIN; cbn [den]; rewrite wbv_unsigned; exact L2w).
    assert (HIT' : hiZ E1 rT = 24) by (unfold hiZ; rewrite HIT; cbn [den]; rewrite wbv_unsigned, wlit_ok; reflexivity).
    pose proof (ro_range _ _ _ _ _ _ ROKT KT0) as RTr. rewrite LOT', HIT', EVT1 in RTr. fold Tz in RTr.
    assert (WNd1 : wden E1 wN = Win Nz (2 * L) HeapOp.K_BLOCK) by exact (WNd E1 EVN1).
    assert (WTd1 : wden E1 wT = Win Tz 24 6) by (rewrite (WTd E1), EVT1; reflexivity).
    assert (DISJN : forall ob, In ob (owned g) -> forall a, Nz <= a < Nz + 2 * L -> ~ in_iv ob a).
    { intros ob Hob a Ha. pose proof (proj1 (Forall_forall _ _) Wk _ (in_map _ _ _ EXN)) as WW. rewrite WNd1 in WW.
      destruct (WW ltac:(cbn; unfold HeapOp.K_BLOCK, HeapOp.K_STACK; lia)) as [[_ DJ]|[NB _]]; [| exfalso; apply NB; reflexivity].
      apply (DJ ob Hob a). unfold in_iv, w_iv. cbn [w_lo w_len fst snd]. exact Ha. }
    assert (VOWN : In (Bz, L) (owned g)) by (rewrite <- Leb, LCAP, <- VBY; apply owned_evec; fold V; exact VV3).
    assert (SEP : Bz + L <= Nz \/ Nz + L <= Bz).
    { apply (iv_sep Nz Bz (2 * L) L L); [| alia| alia| alia].
      intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }
    assert (BYN : forall a, Nz <= a < Nz + 2 * L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (bytes_of_region segs _ E1 M' kN rN a ROKN KN0). rewrite LON', HIN', EVN1. fold Nz. alia. }

    assert (NLB : In (Nz, 2 * L) LB).
    { pose proof (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ EXN)) as X. rewrite WNd1 in X. destruct X as (_ & _ & _ & [[KD _]|[[_ IN]|[KD _]]]).
      - cbn in KD. unfold HeapOp.K_BLOCK, HeapOp.K_STACK in KD. discriminate KD.
      - exact IN.
      - cbn in KD. unfold HeapOp.K_SUB, HeapOp.K_BLOCK in KD. exfalso. clear - KD. lia. }
    destruct (aw_blocks_ok segs IMGX AW _ LB _ M' mo' _ HA NLB) as (Nb1 & Nb2 & Nb3 & _). cbn [fst snd] in Nb1, Nb2, Nb3.

    assert (RBC : forall i, 0 <= i < L -> rb segs M' (Nz + i) = rb segs M' (Bz + i)).
    { intros i Hi. destruct (COPYB i Hi) as (b & C1 & C2 & _). fold Nz Bz in C1, C2. rewrite C1, C2. reflexivity. }
    assert (COPY : forall i, 0 <= i < L -> bm' (Nz + i) = bm' (Bz + i)).
    { intros i Hi. subst bm'. rewrite !bmem_of_in by alia. rewrite (RBC i Hi). reflexivity. }

    set (VN := mkVec Nz (v_size V) (2 * v_cap V) 24).
    set (g' := PKG (k_tree g) VN (k_zone g)).
    assert (VNf : v_begin VN = Nz /\ v_size VN = v_size V /\ v_cap VN = 2 * v_cap V /\ v_elt VN = 24 /\ v_bytes VN = 2 * L /\
                  v_end VN = NT + 24 /\ v_capend VN = Nz + 2 * L).
    { subst VN. unfold v_bytes, v_end, v_capend. cbn [v_begin v_size v_cap v_elt]. rewrite SZC. subst NT. repeat split; alia. }
    destruct VNf as (VN1 & VN2 & VN3 & VN4 & VN5 & VN6 & VN7).
    assert (NZ0 : Nz <> 0) by (subst Nz; exact (range_nz_sound E fs kN Pfacts0 RNZ)).
    assert (NZ8 : Nz mod 8 = 0) by (subst Nz; exact (mod8_of_align E fs kN Pfacts0 ALN)).
    assert (TZB : Tz = Bz + L - 24) by alia.
    assert (NT0 : PrimInt63.eqb nT 0%uint63 = false) by (apply neq_eqb; intros X; apply (f_equal to_Z) in X; change (to_Z 0%uint63) with 0 in X; alia).
    assert (NTkB : nT <> kB) by (intros X; apply (f_equal to_Z) in X; alia).

    assert (DISJ_BN : forall a, Nz <= a < Nz + 2 * L -> ~ (Bz <= a < Bz + L)).
    { intros a Ha Hb. apply (DISJN _ VOWN a Ha). unfold in_iv. cbn [fst snd]. exact Hb. }

    assert (BYNT : forall a, NT <= a < NT + 48 -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply BYN. subst NT. alia. }
    assert (BYB : forall a, Bz <= a < Bz + L -> M' (Z_to_bv 64 a) <> None /\ find_segment segs a 1 = None).
    { intros a Ha. apply (aw_user_ok segs IMGX AW _ LB _ M' mo' _ a HA VLB). unfold in_iv. cbn [fst snd]. rewrite VBY. alia. }

    assert (GCINV : forall rr gi cs, gcells rr gi = Some cs -> exists gr, IMap.find gi (rg_cells rr) = Some gr /\ cs = g_cells gr).
    { intros rr gi cs H. unfold gcells in H. destruct (IMap.find gi (rg_cells rr)) as [gr|]; [|discriminate]. injection H as <-. exists gr. auto. }
    assert (KEYL : keyZ (Uint63.of_Z (L / 8)) = L / 8).
    { apply keyZ_of_Z. unfold two62Z. clear - L24 L40. pose proof (Z.div_mod L 8 ltac:(lia)) as X. pose proof (Z.mod_pos_bound L 8 ltac:(lia)) as Y. lia. }
    assert (L8E : 8 * (L / 8) = L) by (clear - L8 L24; pose proof (Z.div_mod L 8 ltac:(lia)); lia).
    assert (L8R : 0 <= L / 8 < 2 ^ 44) by (clear - L24 L40; split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
    assert (OFZ : forall d, 0 <= d <= 2 -> PrimInt63.add (Uint63.of_Z (L / 8)) (Uint63.of_Z d) = Uint63.of_Z (L / 8 + d)).
    { intros d Hd. apply Uint63.to_Z_inj. rewrite Uint63.add_spec, !Uint63.of_Z_spec. rewrite wB_two63, two63_eq. clear - Hd L8R.
      rewrite (Z.mod_small (L / 8)) by lia. rewrite (Z.mod_small d) by lia. rewrite ?(Z.mod_small (L / 8 + d)) by lia. first [reflexivity | symmetry; apply Z.mod_small; lia | apply Z.mod_small; lia]. }
    assert (KEYL1 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 1) = L / 8 + 1).
    { change 1%uint63 with (Uint63.of_Z 1). rewrite (OFZ 1) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
    assert (KEYL2 : keyZ (PrimInt63.add (Uint63.of_Z (L / 8)) 2) = L / 8 + 2).
    { change 2%uint63 with (Uint63.of_Z 2). rewrite (OFZ 2) by lia. apply keyZ_of_Z. unfold two62Z. clear - L8R. lia. }
    assert (SLOT : forall E0 rr kk gi cs, IMap.find kk (s_regs stS) = Some rr -> st_ok segs OPS E0 stS ms' mo' -> gcells rr gi = Some cs ->
              slot_ok segs E0 M' (bv_unsigned (ev E0 kk) + 8 * keyZ gi) cs).
    { intros E0 rr kk gi cs Hf HSx Hg. destruct (GCINV rr gi cs Hg) as (gr & Fgr & ->). exact (ro_cells _ _ _ _ _ _ (so_reg _ _ _ _ _ _ HSx kk rr Hf) gi gr Fgr). }
    pose proof (SLOT E1 rT kT 0%uint63 t0 FT HSE1 GT0) as ST0. pose proof (SLOT E1 rT kT 1%uint63 t1 FT HSE1 GT1) as ST1.
    pose proof (SLOT E1 rT kT 2%uint63 t2 FT HSE1 GT2) as ST2.
    pose proof (SLOT E1 rN kN _ e0 FN HSE1 GN0) as SN0. pose proof (SLOT E1 rN kN _ e1 FN HSE1 GN1) as SN1. pose proof (SLOT E1 rN kN _ e2 FN HSE1 GN2) as SN2.
    rewrite EVT1 in ST0, ST1, ST2. fold Tz in ST0, ST1, ST2. change (keyZ 0%uint63) with 0 in ST0. change (keyZ 1%uint63) with 1 in ST1. change (keyZ 2%uint63) with 2 in ST2.
    rewrite EVN1 in SN0, SN1, SN2. fold Nz in SN0, SN1, SN2. rewrite KEYL in SN0. rewrite KEYL1 in SN1. rewrite KEYL2 in SN2.
    assert (TZB' : Tz = Bz + L - 24) by alia.
    assert (SHIFT_T : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 M' (Tz + 8 * j) cs -> slot_ok segs E1 M' (NT + 8 * j) cs).
    { intros j cs Hj S0. apply (slot_ok_shift segs E1 M' M' (Tz + 8 * j) (NT + 8 * j) _ S0). intros i Hi. subst NT.
      replace (Nz + L - 24 + 8 * j + i) with (Nz + (L - 24 + 8 * j + i)) by alia. rewrite (RBC (L - 24 + 8 * j + i)) by alia.
      f_equal. alia. }
    assert (SHIFT_N : forall j cs, 0 <= j <= 2 -> slot_ok segs E1 M' (Nz + 8 * (L / 8 + j)) cs -> slot_ok segs E1 M' (NT + 24 + 8 * j) cs).
    { intros j cs Hj S0. replace (NT + 24 + 8 * j) with (Nz + 8 * (L / 8 + j)) by (subst NT; alia). exact S0. }
    assert (ROKT' : region_ok segs (s_priv st) E1 M' nT (region48 t0 t1 t2 e0 e1 e2)).
    { apply (region48_ok segs (s_priv st) E1 M' nT _ _ _ _ _ _ NT0); rewrite ?NTV; [subst NT; alia| exact BYNT| | | | | |].
      - replace NT with (NT + 8 * 0) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 0) with Tz by alia. rewrite Z.mul_0_r, Z.add_0_r in ST0. exact ST0.
      - replace (NT + 8) with (NT + 8 * 1) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 1) with (Tz + 8) by alia. exact ST1.
      - replace (NT + 16) with (NT + 8 * 2) by alia. apply SHIFT_T; [lia|]. replace (Tz + 8 * 2) with (Tz + 16) by alia. exact ST2.
      - replace (NT + 24) with (NT + 24 + 8 * 0) by alia. apply SHIFT_N; [lia|]. replace (L / 8 + 0) with (L / 8) by alia. exact SN0.
      - replace (NT + 32) with (NT + 24 + 8 * 1) by alia. apply SHIFT_N; [lia|]. exact SN1.
      - replace (NT + 40) with (NT + 24 + 8 * 2) by alia. apply SHIFT_N; [lia|]. exact SN2. }
    destruct (empty_region_ok segs (s_priv st) E1 M' kB L KB0 ltac:(unfold two62Z; alia) ltac:(rewrite EVB1; fold Bz; alia)
                ltac:(rewrite EVB1; fold Bz; exact BYB)) as (ROKB' & HIBe & LOBe).
    pose proof HA as HA'.

    assert (FPB : forall a, Bz <= a < Tz -> ~ in_ws (map (wden E1) ws) a /\ ~ in_ivs IMGX a).
    { intros a Ha.
      assert (SFE : PK.safe g (map (wden E1) ws) a).
      { intros w Hw (K6 & NE0 & E1' & E2' & E3') Hin. fold V in E1', E2', E3'. rewrite VEN, SZC in E2'. unfold ELEM_SIZE in E2'.
        unfold in_iv, w_iv in Hin. cbn [fst snd] in Hin. clear - Ha Hin E2' TZB LCAP. lia. }
      destruct (pk_owned_byte_props segs IMGX AW _ LB M' mo' g _ _ a HA WF O Wk VOWN ltac:(unfold in_iv; cbn [fst snd]; alia) SFE) as (_ & NI & NW & _).
      split; [exact NW| exact NI]. }

    set (wB' := (VP kB wzero, VL oc, VL (wlit 1%uint63))).
    set (wNT := top_win nT 48%uint63 ETOPk).
    set (ws' := List.filter (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws ++ [wB'; wNT]).
    set (b' := VP kN wzero). set (e' := VP nT (wlit 24%uint63)). set (cap' := VP kN (wlit (Uint63.of_Z (2 * L)))).
    set (ca' := [root; rootT; n1; P1; zh; c0; b'; e'; cap'; tptr; trest; tmap; tkey; cf; fT; fN; fP]).
    assert (KEPTW : forall w, In w ws' -> (In w ws /\ w <> wN /\ w <> wT) \/ w = wB' \/ w = wNT).
    { intros w Hw. subst ws'. apply in_app_iff in Hw as [Hw|[<-|[<-|[]]]]; [| right; left; reflexivity| right; right; reflexivity].
      apply filter_In in Hw as [Hw Q]. apply negb_true_iff in Q. apply orb_false_iff in Q as [QA QB]. left. split; [exact Hw|].
      split; intros ->; [rewrite win3_eqb_refl in QA; discriminate QA| rewrite win3_eqb_refl in QB; discriminate QB]. }
    assert (LENws' : Z.of_nat (length ws') < two63).
    { subst ws'. rewrite length_app. cbn [length]. pose proof (filter_length_le (fun w => negb (win3_eqb w wN || win3_eqb w wT)) ws) as FL. unfold two63. clear - FL WLEN. lia. }
    assert (WB'd : wden E1 wB' = Win Bz L HeapOp.K_BLOCK).
    { subst wB'. unfold wden. rewrite (den_VP0 E1 kB wzero (weqb_refl _)), EVB1. cbn [den]. rewrite !wbv_unsigned, wlit_ok. fold Bz L. reflexivity. }
    assert (WNTd : wden E1 wNT = Win NT 48 6) by (subst wNT; rewrite top_win_den, NTV; reflexivity).
    assert (Db' : bv_unsigned (den E1 b') = Nz) by (subst b'; rewrite (den_VP0 E1 kN wzero (weqb_refl _)), EVN1; reflexivity).
    assert (De' : bv_unsigned (den E1 e') = NT + 24).
    { subst e'. rewrite (den_VP_nowrap E1 nT (wlit 24%uint63)); rewrite ?wlit_ok, NTV; change (to_Z 24%uint63) with 24; [reflexivity| subst NT; alia]. }
    assert (Dcap' : bv_unsigned (den E1 cap') = Nz + 2 * L).
    { subst cap'. rewrite (den_VP_nowrap E1 kN _); rewrite L2w, EVN1; fold Nz; [reflexivity| alia]. }

    assert (LSNE : ls <> []) by (intros X; rewrite X in SZ; cbn in SZ; alia).
    assert (RLEN : Z.of_nat (length (removelast ls)) = v_size V - 1).
    { rewrite (removelast_length _ LSNE). rewrite Nat2Z.inj_sub by (destruct ls; [exfalso; exact (LSNE eq_refl)| cbn; lia]). rewrite <- SZ. reflexivity. }
    apply (surgery_sound segs OPS E1 (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st5 _ mo' o HS5 opre opost F5ops OID OPOTH [kN; kT]
             [(nT, region48 t0 t1 t2 e0 e1 e2); (kB, empty_region L)] (mk_args 3%uint63 aw ws' ca') _ (PrimInt63.add nT 1)).
    -   intros k [<-|[<-|[]]]; rewrite F5regs.
      + split; [exact KN0|]. exists rN. split; [exact FN| exact WN].
      + split; [exact KT0|]. exists rT. split; [exact FT| exact WT].
    -   cbn [map fst]. constructor; [intros [X|[]]; exact (NTkB (eq_sym X))| constructor; [intros []| constructor]].
    -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; [exact NT0| exact KB0].
    -   intros k rr [H1|[H1|[]]]; injection H1 as <- <-; rewrite F5pv; [exact ROKT'| exact ROKB'].
    -   intros k rr a [H1|[H1|[]]] IR; injection H1 as <- <-.
      + right. exists kN, rN. split; [left; reflexivity|]. rewrite F5regs. split; [exact FN|].
        unfold inR in IR |- *. rewrite NTV in IR. rewrite EVN1, LON', HIN'. fold Nz.
        change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR. rewrite wbv_unsigned, wlit_ok in IR.
        change (to_Z 48%uint63) with 48 in IR. subst NT. alia.
      + unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR.
        destruct (Z.lt_ge_cases a Tz) as [LTz|GEz].
        * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))).
          destruct (FPB a ltac:(alia)) as [NW NI]. split; [alia|]. split; [exact NI| exact NW].
        * right. exists kT, rT. split; [right; left; reflexivity|]. rewrite F5regs.
          split; [exact FT|]. unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. alia.
    -   intros q1 u1 q2 u2 a [H1|[H1|[]]] [H2|[H2|[]]] NE12; injection H1 as <- <-; injection H2 as <- <-; try (exfalso; exact (NE12 eq_refl));
        unfold inR; rewrite NTV, EVB1, LOBe, HIBe; fold Bz; change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0;
        unfold hiZ; cbn [region48 rg_hi den]; rewrite wbv_unsigned, wlit_ok; change (to_Z 48%uint63) with 48; intros [J1 J2].
      + apply (DISJ_BN a); subst NT; alia.
      + apply (DISJ_BN a); subst NT; alia.
    -   rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 3, (den E1 aw), (map (wden E1) ws'), (map (den E1) ca'), LB.
      split; [apply mk_args_sound; exact LENws'|].
      split.
      { pose proof HA' as HA2. apply (aw_keep segs IMGX AW _ _ _ _ _ _ HA2). apply (UOK.wins_keep_map_intro E1 LB ws ws').
        - intros x Hx. destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [left; exact Hx'| right| right; apply UOK.kind_new_sub; reflexivity].

          rewrite WB'd. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|].
          intros _ g0 Hg KG a Ha Hb. apply in_map_iff in Hg as (y & <- & Hy).
          destruct (KEPTW y Hy) as [(Hy' & _ & _)|[->| ->]].
          +
            destruct (proj1 (Forall_forall _ _) Wk (wden E1 y) (in_map _ _ _ Hy') ltac:(unfold K_STACK, K_GHOST in *; lia)) as [[_ DJ]|[_ ET]].
            * exact (DJ (Bz, L) VOWN a Ha Hb).
            * destruct ET as (K6 & _). unfold PK.K_ETOP, K_GHOST in *. lia.
          + rewrite WB'd in KG. cbn [w_kind] in KG. unfold K_GHOST, HeapOp.K_BLOCK in KG. lia.
          + rewrite WNTd in KG. cbn [w_kind] in KG. unfold K_GHOST in KG. lia.
        - intros x Hx. destruct (UOK.filter_old ws [wB'; wNT] (fun w => negb (win3_eqb w wN || win3_eqb w wT)) x Hx) as [H1|F]; [left; exact H1| right].
          apply negb_false_iff in F. apply orb_prop in F as [F|F]; apply win3_eqb_eq in F; subst x.
          +
            rewrite WNd1. split; [unfold aw_tied, K_STACK, K_GHOST, HeapOp.K_BLOCK; cbn [w_kind]; clear; lia|]. intros _ _.
            apply (block_keep_evidence LB _ Nz (2 * L) _ (wden E1 wNT) NLB).
            * cbn [w_lo]. alia.
            * apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
            * rewrite WNTd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
            * rewrite WNTd. cbn [w_len]. clear. lia.
            * rewrite WNTd. cbn [w_lo]. subst NT. alia.
          +
            rewrite WTd1. split; [unfold aw_tied, K_STACK, K_GHOST; cbn [w_kind]; clear; lia|]. intros _ _.
            apply (block_keep_evidence LB _ Bz L _ (wden E1 wB') (proj1 O _ VOWN)).
            * cbn [w_lo]. alia.
            * apply in_map. subst ws'. apply in_app_iff. right. left. reflexivity.
            * rewrite WB'd. unfold heap_kind, HeapOp.K_BLOCK, K_GHOST. cbn [w_kind]. clear. lia.
            * rewrite WB'd. cbn [w_len]. alia.
            * rewrite WB'd. cbn [w_lo]. alia. }
      split.
      +
        unfold windows_wf in *. apply Forall_forall. intros w Hw. apply in_map_iff in Hw as (x & <- & Hx).
        destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]].
        * exact (proj1 (Forall_forall _ _) WF _ (in_map _ _ _ Hx')).
        * rewrite WB'd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. split; [alia|]. split; [alia|]. split; [alia|].
          right; left. split; [reflexivity|]. unfold w_iv. cbn [w_lo w_len]. rewrite LCAP, <- VBY. exact VLB.
        * rewrite WNTd. unfold window_wf. cbn [w_lo w_len w_kind w_iv]. subst NT. split; [alia|]. split; [alia|]. split; [alia|].
          right; right. split; [unfold HeapOp.K_SUB; alia|].
          exists (Nz, 2 * L). split; [exact NLB|]. intros a Ha. unfold in_iv, w_iv in Ha |- *. cbn [w_lo w_len fst snd] in Ha |- *. clear - Ha L24. lia.
      +
        apply CW3'. unfold cw_pk_holds. subst ca'. cbn [map decode_pk].
        assert (VNV : vec_valid VN).
        { unfold vec_valid. rewrite VN1, VN2, VN3, VN4, SZC. split; [alia|]. split; [alia|]. split; [exact NZ0| exact NZ8]. }

        assert (RDJ2 : forall b, In b (owned g) -> rdisj Nz (2 * L) (fst b) (snd b) /\ rdisj (fst b) (snd b) Nz (2 * L)).
        { intros b0 Hb0. pose proof (PK.owned_pos g ls P b0 Hb0) as PO. unfold rdisj.
          destruct (Z_lt_le_dec (fst b0) (Nz + 2 * L)) as [A1|A1]; [| split; [left| right]; exact A1].
          destruct (Z_lt_le_dec Nz (fst b0 + snd b0)) as [A2|A2]; [| split; [right| left]; exact A2].
          exfalso. destruct (Z_lt_le_dec (fst b0) Nz) as [A3|A3].
          - apply (DISJN b0 Hb0 Nz ltac:(alia)). unfold in_iv. alia.
          - apply (DISJN b0 Hb0 (fst b0) ltac:(alia)). unfold in_iv. alia. }
        assert (OWNo : owned g = (Bz, L) :: map chunk_block (z_chunks (k_zone g))).
        { unfold owned, evec_blocks. fold V. rewrite Leb. replace (Bz =? 0) with false by (symmetry; apply Z.eqb_neq; rewrite <- Leb; exact VV3). rewrite VBY, <- LCAP. reflexivity. }
        assert (OWN' : owned g' = (Nz, 2 * L) :: map chunk_block (z_chunks (k_zone g))).
        { subst g'. unfold owned, evec_blocks. cbn [k_evec k_zone]. rewrite VN1, VN5. replace (Nz =? 0) with false by (symmetry; apply Z.eqb_neq; exact NZ0). reflexivity. }
        exists g', ls. split; [| split; [| split; [| split]]].
        *
          unfold link_pk. subst g'. cbn [k_tree k_evec k_zone a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
          rewrite Db', De', Dcap', VN1, VN6, VN7.
          split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|].
          split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [exact LTOP| exact LCF].
        *
          unfold pure_pk. subst g'. cbn [k_tree k_evec k_zone]. rewrite VN1, VN2, VN3, VN4, VN7.
          split; [exact LV|]. split; [reflexivity|]. split; [exact SZ|]. split; [right; split; [exact VNV| split; [alia| split; [apply pow2_b_double; [exact (proj1 CPOW)| alia]| clear - CAP2; alia]]]|]. split; [alia| exact ZV].
        *
          unfold own_pk. rewrite OWN'. destruct O as [OL OF]. rewrite OWNo in OL, OF, RDJ2. split.
          -- intros b0 [<-|Hb0]; [exact NLB| apply OL; right; exact Hb0].
          -- destruct (FOP_cons _ _ _ OF) as [F1 F2]. constructor; [| exact F2].
             apply Forall_forall. intros cb Hcb. apply (proj1 (RDJ2 _ ltac:(right; exact Hcb))).
        *
          unfold wins_pk. apply Forall_forall. intros w Hw NS. apply in_map_iff in Hw as (x & <- & Hx). rewrite OWN'.
          destruct (KEPTW x Hx) as [(Hx' & NxN & NxT)|[->| ->]].
          --
             destruct (proj1 (Forall_forall _ _) Wk (wden E1 x) (in_map _ _ _ Hx') NS) as [[KDx DJ]|[_ ET]];
               [| exfalso; pose proof (only_kind_sound E1 6 _ ws OKT x Hx' (proj1 ET)) as X; injection X as <-; exact (NxT eq_refl)].
             left. split; [exact KDx|]. intros b0 [<-|Hb0] a Ha Hb.
             ++ unfold in_iv in Hb. cbn [fst snd] in Hb.
                pose proof (new_block_apart segs IMGX AW E1 fs (s_regs stS) _ LB M' mo' kN rN (2 * L) ws wN wT x Pfacts1 Pdisj1 FN KN0 LON HIN' ltac:(alia) WN HA
                         ltac:(rewrite EVN1; exact NLB) WF KL OBK NOA SWO EXN ltac:(rewrite EVN1; exact WNd1) Hx' NxN NxT NS a Ha) as NBA. rewrite EVN1 in NBA. exact (NBA Hb).
             ++ exact (DJ b0 ltac:(rewrite OWNo; right; exact Hb0) a Ha Hb).
          --
             left. rewrite WB'd. split; [left; reflexivity|]. intros b0 [<-|Hb0] a Ha Hb; unfold in_iv, w_iv in Ha; cbn [w_lo w_len fst snd] in Ha; unfold in_iv in Hb; cbn [fst snd] in Hb.
             ++ exact (DISJ_BN a Hb Ha).
             ++ destruct O as [OL OF]. rewrite OWNo in OF. destruct (FOP_cons _ _ _ OF) as [F1 _].
                pose proof (proj1 (Forall_forall _ _) F1 b0 Hb0) as D. unfold rdisj in D. cbn [fst snd] in D. clear - D Ha Hb. lia.
          --
             right. rewrite WNTd. cbn [w_kind w_lo w_len]. split; [unfold HeapOp.K_BLOCK; clear; lia|].
             unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
             split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia.
        *
          split.
          2: { split; [destruct GH as [SE EP]; split|].
               3: { eapply cost_pk_args; [eapply cost_pk_ws; [exact CO|]| reflexivity| reflexivity].
                    intros w Hw NV. apply in_map_iff in Hw as (x & <- & Hx).
                    destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [apply in_map; exact Hx'| |].
                    - exfalso. apply NV. apply pku_val_none_kind. rewrite WB'd. cbn [w_kind]. unfold HeapOp.K_BLOCK. clear. lia.
                    - exfalso. apply NV. apply pku_val_none_kind. rewrite WNTd. cbn [w_kind]. unfold K_ETOP. clear. lia. }
               - subst g'. cbn [k_zone]. apply (Seal.seal_ok_ws (map (wden E1) ws)); [exact SE|]. intros w Hw K9. apply in_map_iff in Hw as (x & <- & Hx).
                 destruct (KEPTW x Hx) as [(Hx' & _ & _)|[->| ->]]; [apply in_map; exact Hx'| |].
                 + exfalso. rewrite WB'd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN, HeapOp.K_BLOCK in K9. clear - K9. lia.
                 + exfalso. rewrite WNTd in K9. cbn [w_kind] in K9. unfold Seal.K_TWIN in K9. clear - K9. lia.
               - intros _. exists (wden E1 wNT). split.
                 + apply in_map. subst ws'. apply in_app_iff. right. right. left. reflexivity.
                 + rewrite WNTd. unfold etop_ok. subst g'. cbn [w_kind w_lo w_len k_evec]. rewrite VN1, VN6, VN7.
                   split; [| clear; lia]. split; [reflexivity|]. split; [exact NZ0|]. unfold ELEM_SIZE. subst NT. clear - L24. lia. }
          unfold mem_pk. subst g'. cbn [k_tree k_evec k_zone a_root]. rewrite VN1. fold bm'.
          split; [exact TW2|]. split; [exact KA2|]. split; [exact ICB2|]. split; [exact CH2|].
          intros _. pose proof (PE2 ltac:(fold V; rewrite Leb; rewrite <- Leb; exact VV3)) as X. fold V in X. rewrite Leb in X.
          apply (pelems_at_shift _ bm' bm' Bz Nz); [| exact X].
          intros i Hi. apply COPY. rewrite length_map, RLEN in Hi. unfold ELEM_SIZE in Hi. clear - Hi SZC LCAP CPOS. lia.
    -
      intros a FPa. unfold FP in FPa. rewrite (ho_fp _ _ _ _ _ HOPS) in FPa.
      apply (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws') _ a (mk_args_sound E1 3%uint63 aw _ _ LENws'))) in FPa as (RA0 & NI & NW).
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
             unfold inR. rewrite EVT1, LOT'. unfold hiZ. rewrite HIT. cbn [den]. rewrite wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24. fold Tz. clear - Hin. lia.
          -- exfalso. apply (NWi w); [subst ws'; apply in_app_iff; left; apply filter_In; split; [exact Hw| rewrite QN, QT; reflexivity]|].
             exact Hin.
        * left. unfold FP. rewrite (ho_fp _ _ _ _ _ HOPS). apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E1) ws) _ a (DECf E1))). auto.
      + intros k rr [H1|[H1|[]]] IR; injection H1 as <- <-.
        * apply (NWi wNT); [subst ws'; apply in_app_iff; right; right; left; reflexivity|]. rewrite WNTd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
          unfold inR in IR. rewrite NTV in IR. change (loZ (region48 t0 t1 t2 e0 e1 e2)) with 0 in IR. unfold hiZ in IR. cbn [region48 rg_hi den] in IR.
          rewrite wbv_unsigned, wlit_ok in IR. change (to_Z 48%uint63) with 48 in IR. alia.
        * apply (NWi wB'); [subst ws'; apply in_app_iff; right; left; reflexivity|]. rewrite WB'd. unfold in_iv, w_iv. cbn [w_lo w_len fst snd].
          unfold inR in IR. rewrite EVB1, LOBe, HIBe in IR. fold Bz in IR. alia.
    -
      assert (DnT0 : bv_unsigned (den E1 (VP nT wzero)) = NT) by (rewrite (den_VP0 E1 nT wzero (weqb_refl _)); exact NTV).
      assert (DkNL : bv_unsigned (den E1 (VP kN (wlit (Uint63.of_Z (L - 24))))) = Nz + (L - 24)).
      { rewrite (den_VP_nowrap E1 kN _); rewrite wlit_ok, Uint63.of_Z_spec, EVN1; fold Nz; rewrite Z.mod_small by (rewrite wB_two63, two63_eq; alia); [reflexivity| alia]. }
      constructor.
      { cbn [fact_holds]. apply bv_eq. rewrite DnT0, DkNL. subst NT. alia. }
      constructor.
      { cbn [fact_holds]. rewrite Db', DnT0. subst NT. alia. }
      constructor.
      { cbn [fact_holds]. rewrite De', Dcap'. subst NT. alia. }
      apply Forall_app. split.
      + apply (top_facts_sound E1 fs b' nT Pfacts1); rewrite Db', NTV; [subst NT; alia|].
        subst NT. replace (Nz + L - 24 - Nz) with (L - 24) by alia. apply Z.mod_divide; [lia|]. apply Z.mod_divide in L8; [|lia]. destruct L8 as [q Hq]. exists (q - 3). lia.
      + apply (anchor_facts_sound E1 fs kN (L - 24) (L - 24) nT Pfacts1). rewrite NTV, EVN1. fold Nz. subst NT. alia.
    }
Qed.

Theorem pkregrow_sound : contract_sound segs OPS MP PB (pkregrow_contract SRCPAT MEMCPY_PC).
Proof.
  intros st sts Hpc HAP K E ms model HS0 HMP HPB Hk. cbn [pkregrow_contract c_apply c_pc] in HAP, Hpc.
  unfold pkregrow_apply in HAP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (ActrA.acall_pre ActrA.ASTACK None st) as [[[[r hargs] wnl] st1]|] eqn:AP; [|discriminate].
  destruct (PrimInt63.eqb mdi 3 && fresh_ok (sink st st1 r)) eqn:MDF; [|discriminate].
  apply andb_prop in MDF as [MD FRS]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct (PkStack.parse_ca ca) as [c|] eqn:PCA; [|discriminate].
  destruct (PkStack.c_eb c) as [b0|kB ob| | | | | | | | |] eqn:EB; try discriminate.
  - destruct (weqb b0 wzero) eqn:B00; [|discriminate].
    exact (regrow0_sound st r hargs wnl st1 aw ws ca c sts K E ms model Hpc TO AP FRS PCA (ex_intro _ b0 (conj EB B00)) HAP HS0 HMP HPB Hk).
  - destruct (PkStack.c_ee c) as [|kT oe| | | | | | | | |] eqn:EE; try discriminate.
    destruct (PkStack.c_ecap c) as [|kB' oc| | | | | | | | |] eqn:EC; try discriminate.
    destruct (PrimInt63.eqb kB kB' && weqb ob wzero && weqb oe (wlit 24%uint63)) eqn:Q; [|discriminate].
    apply andb_prop in Q as [Q OE]. apply andb_prop in Q as [KBB OB]. apply Uint63.eqb_correct in KBB. subst kB'.
    apply (proj1 (weqb_ok _ _)) in OB. apply (proj1 (weqb_ok _ _)) in OE. subst ob oe.
    exact (regrow1_sound st r hargs wnl st1 aw ws ca c kB kT oc sts K E ms model Hpc TO AP FRS PCA EB EE EC HAP HS0 HMP HPB Hk).
Qed.
End Sound.
End PkRegrowA.
End TwinB.
