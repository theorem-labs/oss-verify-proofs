(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv OpsBridge Seal Ops GLib PkPeek PkStep PkStepA OpShLoad.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS UB HeapOp UO UG.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module OpShLoadU.

Definition slot_win (kS : int) : sv * sv * sv := (VP kS wzero, VL (wlit 24%uint63), VL (wlit 4%uint63)).

Section WithSegs.
Variable segs : list Segment.

Definition opshloadu_apply (st : sstate) : option (list sstate) :=
  match PkPeek.load_at segs (s_pc st), the_op st with
  | Some (SZ1, sx, rd, rs, off), Some (md, aw, ws, ca) =>
      match OpShLoad.shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off)) with
      | Some p =>
          let ok :=
            if PrimInt63.eqb md 1%uint63 then
              match ca with
              | [root; cb; ce; ccap; vb; ve; vcap; zptr; zfree; c0; slot; tD; restD; rootT; n1; P1; zh] =>
                  match slot with
                  | VP kS os => if weqb os wzero then if existsb (win3_eqb (slot_win kS)) ws then OpShLoad.within (s_facts st) p slot 0%uint63 24 else false else false
                  | _ => false
                  end
              | _ => false
              end
            else false in
          if ok && negb (r5_eqb rd X0) && PrimInt63.ltb (s_pc st) bit62i
          then Some [setpc (setr st rd (VL wzero)) (PrimInt63.add (s_pc st) 4%uint63)]
          else None
      | None => None
      end
  | _, _ => None
  end.
Definition opshloadu_c (pc : int) : contract := Contract pc opshloadu_apply.
End WithSegs.

Section Sound.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable XW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW (unp_cw segs XW) OPS.

Variable CHS : list oinst -> (word -> option byte) -> Model -> Z -> Prop.
Hypothesis LAWS : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  op_minv OPS mo -> Forall (fun o => op_holds OPS (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> CHS os m mo (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv OPS mo' /\
              Forall (fun o => op_holds OPS (fst o) (snd o) m mo') os.
Hypothesis SHLAW : forall os args md aw ws ca LB m mo cs c p,
  In (OPID, args) os -> decode args = Some (md, aw, ws, ca) ->
  aw_holds segs IMGX AW aw LB ws m mo -> windows_wf ws LB (aw_ceiling segs IMGX AW mo) ->
  Seal.seal_ok ws cs -> In c cs -> In (chunk_block c) LB ->
  (forall w, In w ws -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a) ->
  in_iv (chunk_block c) p ->
  m (Z_to_bv 64 (Seal.shadZ p)) = Some (Z_to_bv 8 0) /\ CHS os m mo (Seal.shadZ p).
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma existsb_win_In : forall w ws, existsb (win3_eqb w) ws = true -> In w ws.
Proof.
  intros w ws H. apply existsb_exists in H as (x & Hx & Q). apply win3_eqb_eq in Q. subst x. exact Hx.
Qed.
Lemma slot_win_den : forall E kS, wden E (slot_win kS) = Win (bv_unsigned (ev E kS)) 24 K_SLOT.
Proof.
  intros E kS. unfold slot_win, wden. rewrite (den_VP0 E kS wzero (weqb_refl _)), !den_VL, !wlit_ok. reflexivity.
Qed.

Lemma opshloadu_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> opshloadu_apply segs st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP. unfold opshloadu_apply in AP.
  destruct (PkPeek.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (OpShLoad.shadow_ptr (sv_alu ALU_ADD (getr st rs) (VL off))) as [p|] eqn:SP; [|discriminate].
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [OKC RDX].
  destruct (PrimInt63.eqb mdi 1) eqn:MD1; [|discriminate]. apply Uint63.eqb_correct in MD1. subst mdi.
  destruct ca as [|root [|cb [|ce [|ccap [|vb [|ve [|vcap [|zptr [|zfree [|c0 [|slot [|tD [|restD [|rootT [|n1 [|P1 [|zh [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct slot as [|kS os| | | | | | | | |]; try discriminate.
  destruct (weqb os wzero) eqn:OS; [|discriminate]. apply (proj1 (weqb_ok _ _)) in OS. subst os.
  destruct (existsb (win3_eqb (slot_win kS)) ws) eqn:EXS; [|discriminate]. apply existsb_win_In in EXS.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 1%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  pose proof (DECf E) as DECE. rewrite DECE in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 1%uint63) with 1 in HC.
  cbn [cw_holds unp_cw] in HC. unfold cw_unp_holds in HC. cbn [CM_NONE CM_UNP CM_CONS Z.eqb orb Pos.eqb] in HC. cbn [map decode_uc] in HC.
  destruct HC as (g & L & P & O & Wk & M & _ & _ & SE).
  set (PP := bv_unsigned (den E p)) in *.
  pose proof (bv_unsigned_in_range 64 (den E p)) as RP. rewrite bv_modulus_64 in RP. fold PP in RP.

  pose proof (proj1 (Forall_forall _ _) Wk _ (in_map (wden E) _ _ EXS)) as WS. rewrite slot_win_den in WS.
  specialize (WS ltac:(cbn [w_kind]; unfold K_SLOT, K_STACK; lia)).
  destruct WS as [[[KB|KG] _]|[_ SO]]; [cbn [w_kind] in KB; unfold K_SLOT, K_BLOCK in KB; lia| cbn [w_kind] in KG; unfold K_SLOT, K_GHOST in KG; lia|].
  unfold sub_ok in SO. cbv zeta in SO. cbn [w_kind w_lo w_len] in SO.
  destruct SO as [(K & _)|[(K & _)|[(_ & lD & HlD & LO & HI)|(K & _)]]]; try (exfalso; unfold K_SLOT, K_CTOP, K_VTOP, K_ZONE in K; lia).
  cbn [CM_CONS Z.eqb Pos.eqb] in LO.
  destruct (top_level g lD HlD) as (ls0 & EL & _ & HinD). destruct (level_array g P lD HinD) as (V & A & G1 & G2 & G4 & c & Hc & IC).
  pose proof (owned_chunk g c Hc) as OWNc.
  destruct (OpShLoad.within_sound E _ Pfacts p (VP kS wzero) 24 0%uint63 ltac:(change (to_Z 0%uint63) with 0; cbn; lia) OKC) as (j & J & EQ).
  change (to_Z 0%uint63) with 0 in J. change (Z.of_nat 24) with 24 in J. fold PP in EQ. rewrite (den_VP0 E kS wzero (weqb_refl _)) in EQ.
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block c) HA (proj1 O _ OWNc)) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  assert (INP : in_iv (chunk_block c) PP).
  { unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, lv_unfilled in *.
    rewrite Z.mod_small in EQ by lia. lia. }
  assert (APART : forall w, In w (map (wden E) ws) -> (w_kind w = K_BLOCK \/ K_GHOST <= w_kind w) -> forall a, in_iv (w_iv w) a -> ~ in_iv (chunk_block c) a).
  { intros w Hw K a Ha. destruct (proj1 (Forall_forall _ _) Wk w Hw ltac:(unfold K_BLOCK, K_GHOST, K_STACK in *; lia)) as [[_ D]|[NB SOw]].
    - exact (D _ OWNc a Ha).
    - exfalso. unfold sub_ok in SOw. cbv zeta in SOw. unfold K_CTOP, K_VTOP, K_SLOT, K_ZONE, K_BLOCK, K_GHOST in *.
      destruct SOw as [(K2 & _)|[(K2 & _)|[(K2 & _)|(K2 & _)]]]; lia. }
  destruct (OpShLoad.opsh_tail segs IMGX AW OPS CHS LAWS SHLAW MP HMPA E st ms model sx rd rs off p o _ _ _ _ LB (z_chunks (u_zone g)) c
              HS HMP LA SP PCB (op_in_In st o OPS1) OID DECE HA WF SE Hc (proj1 O _ OWNc) APART INP) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  exists (setpc (setr st rd (VL wzero)) (pc4 st)), ms', mo'. split; [reflexivity|]. auto.
Qed.

Theorem opshloadu_sound : forall pc, contract_sound segs OPS MP PB (opshloadu_c segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [opshloadu_c c_apply] in HAP.
  destruct (opshloadu_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.

End OpShLoadU.
