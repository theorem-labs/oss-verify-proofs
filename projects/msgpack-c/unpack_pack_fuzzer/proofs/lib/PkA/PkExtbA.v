(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From Stdlib Require Import PrimInt63 Uint63.
From stdpp Require Import base decidable list gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg ShapeAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Instr Plan ValProofs MemProofs StepSoundBase StepSoundMem StepSound PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc StepAcc AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkPeek PkStep PkStepA PkBody.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Mem State Step.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr Require Import Lib DefsA LdPart.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Br Require MemFX LdPartSound.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkExtbA.
Section OPS.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : St.optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma body_of_focus : forall bm z fo t (p n : Z),
  tree_wf bm z fo -> obj_type fo = t -> (t = T_STR \/ t = T_BIN \/ t = T_EXT) -> obj_ptr fo = p -> (PK.obj_via fo = n \/ obj_cnt fo = n) ->
  let N := (if t =? T_EXT then n + 1 else n) in
  0 <= n /\ N <= LIMIT /\ (p = 0 -> N = 0) /\ (p <> 0 -> in_zone z p N /\ readable bm p (Z.to_nat N)).
Proof.
  intros bm z fo t p n TW TY HT HP HN. cbv zeta.
  destruct fo; cbn [obj_type] in TY; subst t; unfT; try (exfalso; lia); cbn [obj_ptr PK.obj_via obj_cnt] in HP, HN;
    (assert (HN' : n0 = n) by (destruct HN; assumption)); clear HN; subst;
    cbn [tree_wf] in TW; cbn [Z.eqb Pos.eqb].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C & D & E). unfold LIMIT in *. split; [lia|]. split; [lia|].
    split; [intros P0; exfalso; exact (C P0)| intros _; split; assumption].
Qed.

Lemma dec_true_inv : forall x, dec_true x = true -> x = Some true.
Proof. intros [[|]|]; cbn; congruence. Qed.

Lemma st_ok_facts_next : forall E st ms mo fs' nx,
  St.st_ok segs OPS E st ms mo -> Forall (fact_holds E) fs' ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo fs' nx HS HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  apply Forall_app. split; [exact HF| exact Pfacts].
Qed.

Theorem pkextb_sound : forall pc, contract_sound segs OPS MP PB (PkBody.pkextb_c segs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkextb_c] in Happ. unfold PkBody.pkextb_apply in Happ.
  destruct (LdPart.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate. destruct sx; [|discriminate].
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi. cbn [negb] in Happ.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 PCB]. apply andb_prop in C2 as [C2 NLT]. apply andb_prop in C2 as [C2 NPOS].
  apply andb_prop in C2 as [C2 VB]. apply andb_prop in C2 as [C2 RD0]. apply andb_prop in C2 as [TY DEQP].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  set (n := s_next st) in *.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).
  assert (FO : exists fo, tree_wf (bmem_of segs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
            /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
  { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
    - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
      assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
      destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
      exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
    - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
      pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
      assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
      destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
      pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
      destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
      assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
  clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
  unfold PkBody.T_EXTw in TY. apply (proj1 (weqb_ok _ _)) in TY. subst t.
  assert (FT' : obj_type fo = T_EXT) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
  set (p := obj_ptr fo) in *. set (nb := bv_unsigned (den E fNv)) in *.
  pose proof (body_of_focus (bmem_of segs (ms_mem ms)) (PK.k_zone g) fo T_EXT p nb TWF FT' ltac:(unfT; lia) eq_refl FVIA) as BODY.
  cbv zeta in BODY. unfT. replace (9 =? 9) with true in BODY by reflexivity.
  destruct BODY as (N0 & NL & PZ & PNZ).
  assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
  destruct (PNZ PN0) as [IZ [v RD]].
  pose proof IZ as (c & Hc & ICc).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
              (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  pose proof two64_eq as T64.
  assert (PB8 : 0 <= p /\ p + (nb + 1) <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).

  pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD 0 ltac:(lia)) as X0. rewrite Z.add_0_r in X0.
  assert (RD1 : rdZ (bmem_of segs (ms_mem ms)) p (Z.to_nat (to_Z (msize_bytes SZ1))) = Some (zbyte v 0)).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ]. rewrite X0. cbn [rdZ]. f_equal. pose proof (zbyte_range v 0). lia. }
  pose proof (zbyte_range v 0) as ZB. change (bv_modulus 8) with 256 in ZB.
  set (z := zbyte v 0) in *.

  pose proof (dec_true_inv _ DEQP) as DQP.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.

  set (W := Z_to_bv 64 z).
  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : St.st_ok segs OPS E' st ms mo) by exact (st_ok_reval segs OPS n E E' HX st ms mo NPOS VB HS).
  set (rv := VExt true 0%uint63 1%uint63 (VP n wzero)).
  assert (Dv : den E' rv = ext_word true 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 z)).
  { subst rv. cbn [den]. rewrite EVn. subst W. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
    change (to_Z (msize_bytes SZ1)) with 1. f_equal. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wzero) with 0.
    rewrite Z.add_0_r. apply bv_wrap_bv_unsigned. }
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (FRange n wzero (wlit 255%uint63) :: s_facts st)
                 (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)).
  assert (HS1 : St.st_ok segs OPS E' st1 ms mo).
  { apply (st_ok_facts_next E' st ms mo [FRange n wzero (wlit 255%uint63)] (PrimInt63.add n 1%uint63) HS').
    constructor; [| constructor]. cbn [fact_holds]. rewrite EVn. subst W. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia).
    rewrite wlit_ok || rewrite w2Z_wlit. change (w2Z wzero) with 0. change (to_Z 255%uint63) with 255. lia. }

  destruct (LdPartSound.LdPartSound.load_at_spec segs _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (VBa : sv_vars_below n (sv_alu ALU_ADD (getr st rs) (VL off)) = true).
  { destruct (MemFX.MemFX.st_vars_below_parts n st VB) as (P1r & _). apply (MemFX.MemFX.sv_vars_below_alu n ALU_ADD _ (VL off) (or_introl eq_refl) (rf_allb_get _ _ _ P1r rs)). reflexivity. }
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 p).
  { change (getr st1 rs) with (getr st rs). rewrite (den_reval n E E' HX _ VBa), EQP. apply bv_eq. rewrite Z_to_bv_unsigned, <- FPTR.
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. pose proof (bv_unsigned_in_range 64 (den E fPv)). rewrite bv_modulus_64 in H. lia. }
  assert (ARGE : map (den E') (op_args o) = map (den E) (op_args o)).
  { apply map_ext_in. intros a0 Ha0. exact (den_reval n E E' HX a0 (ops_vars_below n st o VB (op_in_In st o OPS1) a0 Ha0)). }
  destruct (PkStepA.oracle_ILoad_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E' st1 ms mo wi ins SZ1 true rd rs off p z rv HS1 HMP PCB Hf' He Hd Hof DA ltac:(lia)
              ltac:(change (to_Z (msize_bytes SZ1)) with 1; unfold W64.two64; lia) RD1 Dv) as (ms' & mo' & STEP & MEM & HS2 & MP2).
  {
    intros j Hj. change (to_Z (msize_bytes SZ1)) with 1 in Hj. right. unfold userb. exists (map (den E') (op_args o)). do 5 eexists.
    split; [| split; [rewrite ARGE; exact (DECf E)| split; [exact HA|]]].
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact (op_in_In st o OPS1)].
    - unfold in_user, in_ivs. apply Exists_exists. exists (chunk_block c).
      split; [exact (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc. unfold CHUNK_HDR. lia. }
  apply (rz_astep segs ms mo ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo' HX MP2 HS2).
Qed.

End OPS.
End PkExtbA.

Module TwinB.
Import stdpp.base stdpp.decidable stdpp.list stdpp.gmap.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Specs LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAlg OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.ShapeAcc.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64 OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.W64Proofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Val OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.IMap OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Instr OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Plan OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.ValProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.MemProofs OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundBase OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSoundMem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepSound OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.PlanSound.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Acc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.StepAcc OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.AccStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap.Op.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Model OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Layout OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Inv OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Steps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.OpsBridge OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.Tree OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkOps OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.GLib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkPeek OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStep OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkStepA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp.PkBody.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Mem OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.State OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.Lib OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.DefsA OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Ctr.LdPart.

Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val FI St OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX.Step.Step Plan ValP MemP StepB StepM StepS PlanS CtrLib CtrA HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkExtbA.
Section OPS.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : St.optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma body_of_focus : forall bm z fo t (p n : Z),
  tree_wf bm z fo -> obj_type fo = t -> (t = T_STR \/ t = T_BIN \/ t = T_EXT) -> obj_ptr fo = p -> (PK.obj_via fo = n \/ obj_cnt fo = n) ->
  let N := (if t =? T_EXT then n + 1 else n) in
  0 <= n /\ N <= LIMIT /\ (p = 0 -> N = 0) /\ (p <> 0 -> in_zone z p N /\ readable bm p (Z.to_nat N)).
Proof.
  intros bm z fo t p n TW TY HT HP HN. cbv zeta.
  destruct fo; cbn [obj_type] in TY; subst t; unfT; try (exfalso; lia); cbn [obj_ptr PK.obj_via obj_cnt] in HP, HN;
    (assert (HN' : n0 = n) by (destruct HN; assumption)); clear HN; subst;
    cbn [tree_wf] in TW; cbn [Z.eqb Pos.eqb].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C). unfold LIMIT in *. split; [lia|]. split; [lia|]. split; [exact B| exact C].
  - destruct TW as (A & B & C & D & E). unfold LIMIT in *. split; [lia|]. split; [lia|].
    split; [intros P0; exfalso; exact (C P0)| intros _; split; assumption].
Qed.

Lemma dec_true_inv : forall x, dec_true x = true -> x = Some true.
Proof. intros [[|]|]; cbn; congruence. Qed.

Lemma st_ok_facts_next : forall E st ms mo fs' nx,
  St.st_ok segs OPS E st ms mo -> Forall (fact_holds E) fs' ->
  St.st_ok segs OPS E (SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (fs' ++ s_facts st) (s_ops st) (s_priv st) nx) ms mo.
Proof.
  intros E st ms mo fs' nx HS HF.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  constructor; cbn [s_pc s_rf s_ff s_resv s_regs s_facts s_ops s_priv s_next]; try assumption.
  apply Forall_app. split; [exact HF| exact Pfacts].
Qed.

Theorem pkextb_sound : forall pc, contract_sound segs OPS MP PB (PkBody.pkextb_c segs pc).
Proof.
  intros pc st sts Hspc Happ K E ms mo HS HMP HPB HK.
  cbn [c_apply PkBody.pkextb_c] in Happ. unfold PkBody.pkextb_apply in Happ.
  destruct (LdPart.load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate. destruct sx; [|discriminate].
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi. cbn [negb] in Happ.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (PkBody.body_src (s_facts st) eb rootT n1 P1 cf fT fN fP) as [[[fTv fNv] fPv]|] eqn:SRCB; [|discriminate].
  destruct fTv as [t| | | | | | | | | |]; try discriminate.
  cbv zeta in Happ.
  match type of Happ with (if ?c then _ else _) = _ => destruct c eqn:C2; [|discriminate] end.
  apply Some_inj in Happ. subst sts.
  apply andb_prop in C2 as [C2 PCB]. apply andb_prop in C2 as [C2 NLT]. apply andb_prop in C2 as [C2 NPOS].
  apply andb_prop in C2 as [C2 VB]. apply andb_prop in C2 as [C2 RD0]. apply andb_prop in C2 as [TY DEQP].
  apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  set (n := s_next st) in *.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].

  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN').
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold PK.cw_pk_holds in HC. cbn [map PK.decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb PK.a_ee PK.a_ecap PK.a_tptr PK.a_trest PK.a_tmap PK.a_tkey PK.a_cf PK.a_fT PK.a_fN PK.a_fP] in LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).
  assert (FO : exists fo, tree_wf (bmem_of segs (ms_mem ms)) (PK.k_zone g) fo /\ obj_type fo = bv_unsigned (den E (VL t))
            /\ obj_ptr fo = bv_unsigned (den E fPv) /\ (PK.obj_via fo = bv_unsigned (den E fNv) \/ obj_cnt fo = bv_unsigned (den E fNv))).
  { unfold PkBody.body_src in SRCB. destruct (sv_eqb eb (VL wzero)) eqn:EB0.
    - apply sv_eqb_eq in EB0. subst eb. injection SRCB as <- <- <-.
      cbn [PK.a_root PK.a_rootT PK.a_n1 PK.a_P1 PK.a_c0 PK.a_eb] in LT, LN, LP, Leb.
      assert (VB0 : v_begin (PK.k_evec g) = 0) by (rewrite Leb; cbn [den]; rewrite wbv_unsigned; reflexivity).
      destruct VE as [(_ & _ & ->)|[(_ & _ & VNZ & _) _]]; [| exfalso; exact (VNZ VB0)].
      exists (PK.k_tree g). split; [exact TW|]. split; [exact LT|]. split; [exact LP|]. right. exact LN.
    - unfold dec_false in SRCB. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate. injection SRCB as <- <- <-.
      pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
      assert (CF0 : bv_unsigned (den E cf) <> 0) by (intros X; apply CNZ; apply bv_eq; rewrite X; reflexivity).
      destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
      pose proof (last_opt_spec ls) as LS. unfold PK.focus_node in FN.
      destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
      assert (HLV : PK.levels_ok (PK.k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
      exists fo. split; [exact (focus_tree_wf _ _ _ _ _ _ TW HLV FN)|]. auto. }
  clear LCF SRCB. destruct FO as (fo & TWF & FT & FPTR & FVIA).
  unfold PkBody.T_EXTw in TY. apply (proj1 (weqb_ok _ _)) in TY. subst t.
  assert (FT' : obj_type fo = T_EXT) by (rewrite FT; cbn [den]; rewrite wbv_unsigned; reflexivity).
  set (p := obj_ptr fo) in *. set (nb := bv_unsigned (den E fNv)) in *.
  pose proof (body_of_focus (bmem_of segs (ms_mem ms)) (PK.k_zone g) fo T_EXT p nb TWF FT' ltac:(unfT; lia) eq_refl FVIA) as BODY.
  cbv zeta in BODY. unfT. replace (9 =? 9) with true in BODY by reflexivity.
  destruct BODY as (N0 & NL & PZ & PNZ).
  assert (PN0 : p <> 0) by (intros P0; pose proof (PZ P0); lia).
  destruct (PNZ PN0) as [IZ [v RD]].
  pose proof IZ as (c & Hc & ICc).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) mo (chunk_block c) HA
              (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  pose proof two64_eq as T64.
  assert (PB8 : 0 <= p /\ p + (nb + 1) <= 2 ^ 64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc; unfold CHUNK_HDR in *; lia).

  pose proof (rdZ_bytes _ _ _ _ (bmem_of_bytes_range segs (ms_mem ms)) RD 0 ltac:(lia)) as X0. rewrite Z.add_0_r in X0.
  assert (RD1 : rdZ (bmem_of segs (ms_mem ms)) p (Z.to_nat (to_Z (msize_bytes SZ1))) = Some (zbyte v 0)).
  { change (Z.to_nat (to_Z (msize_bytes SZ1))) with 1%nat. cbn [rdZ]. rewrite X0. cbn [rdZ]. f_equal. pose proof (zbyte_range v 0). lia. }
  pose proof (zbyte_range v 0) as ZB. change (bv_modulus 8) with 256 in ZB.
  set (z := zbyte v 0) in *.

  pose proof (dec_true_inv _ DEQP) as DQP.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQP) as EQP. apply (proj1 (eqb_iff _ _ true)) in EQP.

  set (W := Z_to_bv 64 z).
  set (E' := env_upd E n W).
  assert (HX : env_ext n E E') by (subst E'; apply env_upd_ext).
  assert (EVn : ev E' n = W) by (subst E'; apply env_upd_same).
  assert (HS' : St.st_ok segs OPS E' st ms mo) by exact (st_ok_reval segs OPS n E E' HX st ms mo NPOS VB HS).
  set (rv := VExt true 0%uint63 1%uint63 (VP n wzero)).
  assert (Dv : den E' rv = ext_word true 0 (to_Z (msize_bytes SZ1)) (Z_to_bv 64 z)).
  { subst rv. cbn [den]. rewrite EVn. subst W. change (to_Z 0%uint63) with 0. change (to_Z 1%uint63) with 1.
    change (to_Z (msize_bytes SZ1)) with 1. f_equal. apply bv_eq. rewrite bv_add_unsigned, wbv_unsigned. change (w2Z wzero) with 0.
    rewrite Z.add_0_r. apply bv_wrap_bv_unsigned. }
  set (st1 := SS (s_pc st) (s_rf st) (s_ff st) (s_resv st) (s_regs st) (FRange n wzero (wlit 255%uint63) :: s_facts st)
                 (s_ops st) (s_priv st) (PrimInt63.add n 1%uint63)).
  assert (HS1 : St.st_ok segs OPS E' st1 ms mo).
  { apply (st_ok_facts_next E' st ms mo [FRange n wzero (wlit 255%uint63)] (PrimInt63.add n 1%uint63) HS').
    constructor; [| constructor]. cbn [fact_holds]. rewrite EVn. subst W. rewrite Z_to_bv_unsigned, bv_wrap_small by (rewrite bv_modulus_64; lia).
    rewrite wlit_ok || rewrite w2Z_wlit. change (w2Z wzero) with 0. change (to_Z 255%uint63) with 255. lia. }

  destruct (LdPartSound.LdPartSound.load_at_spec segs _ _ _ _ _ _ LA) as (wi & ins & Hf & He & Hd & Hof).
  assert (Hf' : fetch_word segs (ms_pc_val ms) = Some wi) by (rewrite (so_pc _ _ _ _ _ _ HS); exact Hf).
  assert (VBa : sv_vars_below n (sv_alu ALU_ADD (getr st rs) (VL off)) = true).
  { destruct (MemFX.MemFX.st_vars_below_parts n st VB) as (P1r & _). apply (MemFX.MemFX.sv_vars_below_alu n ALU_ADD _ (VL off) (or_introl eq_refl) (rf_allb_get _ _ _ P1r rs)). reflexivity. }
  assert (DA : den E' (sv_alu ALU_ADD (getr st1 rs) (VL off)) = Z_to_bv 64 p).
  { change (getr st1 rs) with (getr st rs). rewrite (den_reval n E E' HX _ VBa), EQP. apply bv_eq. rewrite Z_to_bv_unsigned, <- FPTR.
    symmetry. apply bv_wrap_small. rewrite bv_modulus_64. pose proof (bv_unsigned_in_range 64 (den E fPv)). rewrite bv_modulus_64 in H. lia. }
  assert (ARGE : map (den E') (op_args o) = map (den E) (op_args o)).
  { apply map_ext_in. intros a0 Ha0. exact (den_reval n E E' HX a0 (ops_vars_below n st o VB (op_in_In st o OPS1) a0 Ha0)). }
  destruct (PkStepA.oracle_ILoad_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E' st1 ms mo wi ins SZ1 true rd rs off p z rv HS1 HMP PCB Hf' He Hd Hof DA ltac:(lia)
              ltac:(change (to_Z (msize_bytes SZ1)) with 1; unfold W64.two64; lia) RD1 Dv) as (ms' & mo' & STEP & MEM & HS2 & MP2).
  {
    intros j Hj. change (to_Z (msize_bytes SZ1)) with 1 in Hj. right. unfold userb. exists (map (den E') (op_args o)). do 5 eexists.
    split; [| split; [rewrite ARGE; exact (DECf E)| split; [exact HA|]]].
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact (op_in_In st o OPS1)].
    - unfold in_user, in_ivs. apply Exists_exists. exists (chunk_block c).
      split; [exact (proj1 O _ ltac:(unfold PK.owned; apply in_app_iff; right; apply in_map; exact Hc))|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICc. unfold CHUNK_HDR. lia. }
  apply (rz_astep segs ms mo ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (HK _ (or_introl eq_refl) E' ms' mo' HX MP2 HS2).
Qed.

End OPS.
End PkExtbA.
End TwinB.
