(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg LiaFast.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree PkOps PkLib GLib PkStep PkPeek.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import Acc StepAcc.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.
Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).
Local Ltac Stdlib.micromega.Lia.lia ::= flia2.

Module PkFld.
Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Section WithSegs.
Variable segs : list Segment.

Definition fload_at (pc : int) : option (r5 * r5 * w64) :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (i, z) => if Z.eqb z 4 then match of_instr i with Some (IFLoad FMT_D rd rs off) => Some (rd, rs, off) | _ => None end else None
      | None => None
      end
  | None => None
  end.

Lemma fload_at_spec : forall pc rd rs off, fload_at pc = Some (rd, rs, off) ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\
              of_instr i = Some (IFLoad FMT_D rd rs off).
Proof.
  intros pc rd rs off H. unfold fload_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z.
  destruct (of_instr i) as [fi|] eqn:OI; [|discriminate]. destruct fi; try discriminate. destruct fmt; try discriminate.
  injection H as <- <- <-. exists w, i. auto.
Qed.

Lemma oracle_FLoad : forall OPS E st ms model (w : bv 32) (i : instr) rd rs1 off A z (v : sv),
  st_ok segs OPS E st ms model -> PrimInt63.ltb (s_pc st) bit62i = true ->
  fetch_word segs (ms_pc_val ms) = Some w -> is_ecall w = false -> decode_any w = Some (i, 4%Z) ->
  of_instr i = Some (IFLoad FMT_D rd rs1 off) ->
  den E (sv_alu ALU_ADD (getr st rs1) (VL off)) = Z_to_bv 64 A -> 0 <= A -> A + 8 <= two64 ->
  rdZ (bmem_of segs (ms_mem ms)) A 8 = Some z ->
  den E v = Z_to_bv 64 z ->
  exists ms', RiscvSemantics.step segs ms = MachineOk ms' /\ ms_mem ms' = ms_mem ms /\
              st_ok segs OPS E (setpc (setf st rd v) (pc4 st)) ms' model.
Proof.
  intros OPS E st ms model w i rd rs1 off A z v HS Hpc Hf He Hd Hof HA A0 A1 RD Hv.
  destruct (of_instr_IFLoad i FMT_D rd rs1 off Hof) as (rd' & rs1' & imm & -> & Hrd & Hrs1 & ->).
  destruct (PkStep.rdZ_ov_read segs (ms_mem ms) 8 A z A0 ltac:(cbn [Z.of_nat]; lia) RD) as (bs & OV & LEN & VAL).
  rewrite <- HA, <- (ea_den segs OPS E st ms model rs1 rs1' _ imm HS Hrs1) in OV.
  rewrite (step_exec segs ms w _ Hf He Hd).
  cbn [Sem.exec]. rewrite <- (reg_of_r5_of_reg rd' rd Hrd). rewrite (npc_eq segs OPS E st ms model HS Hpc).
  assert (LW : le_bytes_to_word bs = Z_to_bv 64 z) by (unfold le_bytes_to_word; rewrite VAL; reflexivity).
  change 8%nat with (width_bytes 64) in OV.
  erewrite interp_ELoad by exact OV. rewrite interp_EDone. eexists. split; [reflexivity|]. split; [reflexivity|].
  apply (st_ok_freg_pc segs OPS E st ms model rd v _ (pc4 st) HS). rewrite Hv, LW. apply bv_extract_64 || (rewrite bv_extract_64; reflexivity).
Qed.

Section WithPc.
Variable THE_PC : int.

Definition pkfld_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match fload_at (s_pc st), fT with
          | Some (rd, rs, off), VL t =>
              let fs := s_facts st in
              if weqb off (wlit 8%uint63) && (weqb t (wlit 10%uint63) || weqb t (wlit 4%uint63)) && PrimInt63.ltb (s_pc st) bit62i
                 && dec_false (decide_eq0 fs cf) && dec_true (decide_eq fs (getr st rs) cf)
              then Some [setpc (setf st rd fN) (PrimInt63.add (s_pc st) 4%uint63)]
              else None
          | _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition pkfld_contract : contract := Contract THE_PC pkfld_apply.
End WithPc.

Section Sound.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma u64_of_Z : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. exact Hz. Qed.

Lemma pkfld_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> pkfld_apply st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP.
  unfold pkfld_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (fload_at (s_pc st)) as [[[rd rs] off]|] eqn:LA; [|discriminate].
  destruct fT as [t| | | | | | | | | |]; try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND DEQ]. apply andb_prop in COND as [COND DNZ]. apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [O8 T104].
  apply (proj1 (weqb_ok _ _)) in O8. subst off.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof (ops_hold_in OPS _ _ _ _ o Pops (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).

  unfold PkStack_dec_false in DNZ || idtac.
  destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate.
  pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
  assert (CF0 : bv_unsigned (den E cf) <> 0).
  { intros X. apply CNZ. apply bv_eq. rewrite X. reflexivity. }
  destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
  pose proof (last_opt_spec ls) as LS. unfold focus_node in FN. unfold focus_addr in CFA.
  destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
  assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
  pose proof (focus_obj_at _ _ _ _ _ KA HLV FN) as OAT.
  set (A := lev_addr l) in *.
  assert (AZ : in_zone (k_zone g) A OBJ_SIZE).
  { apply IC. apply (focus_cells _ _ _ _ _ A HLV FN). destruct fo; cbn; left; reflexivity. }
  destruct AZ as (ch & Hch & ICH).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA
              (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  assert (ABND : 0 <= A /\ A + OBJ_SIZE <= two64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH; unfold CHUNK_HDR in *; lia).

  destruct (decide_eq (s_facts st) (getr st rs) cf) as [[|]|] eqn:DQ; try discriminate.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQ) as RSEQ. apply (proj1 (eqb_iff _ _ true)) in RSEQ.
  destruct (PkPeek.obj_at_fields segs (ms_mem ms) A fo OAT) as (TY & VIA & PTR & U32T & FLD).
  destruct (fload_at_spec (s_pc st) _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.

  assert (T10 : obj_type fo = 10 \/ obj_type fo = 4).
  { rewrite FT. cbn [den]. rewrite wbv_unsigned. apply orb_prop in T104 as [Q|Q]; apply (proj1 (weqb_ok _ _)) in Q; subst t; rewrite wlit_ok; [left| right]; reflexivity. }
  assert (RD : rdZ (bmem_of segs (ms_mem ms)) (A + 8) 8 = Some (obj_via fo)).
  { destruct fo; cbn [obj_type] in T10; unfT; try lia; exact FLD. }
  assert (DFN : den E fN = Z_to_bv 64 (obj_via fo)) by (apply bv_eq; rewrite <- FVIA, u64_of_Z by exact VIA; reflexivity).
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL (wlit 8%uint63))) = Z_to_bv 64 (A + 8)).
  { apply bv_eq. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, RSEQ, CFA.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. unfold OBJ_SIZE in ABND.
    change (to_Z 8%uint63) with 8. rewrite !Z.mod_small by lia. reflexivity. }
  destruct (oracle_FLoad OPS E st ms model w i rd rs (wlit 8%uint63) (A + 8) (obj_via fo) fN HS PCB FW EC DA OI HAD
              ltac:(lia) ltac:(unfold OBJ_SIZE in ABND; lia) RD DFN) as (ms' & STEP & MEM & ST2).

  destruct (of_instr_IFLoad i FMT_D rd rs (wlit 8%uint63) OI) as (rd' & rs1' & imm & EQI & Hrd & Hrs1 & EQO).
  destruct (AccStep.st_ok_account_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E (setpc (setf st rd fN) (pc4 st)) ms ms' model w i FW EC DA STEP ST2 HMP) as (mo' & AS & ST3 & MP3).
  { intros a nn j MA Hj. rewrite EQI in MA. cbn [Acc.mem_acc] in MA. destruct MA as [-> ->]. cbn [Acc.fmt_nat] in Hj.
    change (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) with (core_of ms).
    rewrite (ea_den segs OPS E st ms model rs rs1' _ imm HS Hrs1), <- EQO, HAD.
    rewrite Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64.
    rewrite Z.mod_small by (unfold OBJ_SIZE in ABND; lia).
    rewrite MEM. right. unfold userb. exists (map (den E) (op_args o)). do 5 eexists.
    split; [| split; [exact (DECf E)| split; [exact HA|]]].
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity|].
      cbn [setpc s_ops]. destruct rd; exact (op_in_In st o OPS1).
    - unfold in_user, in_ivs. apply Exists_exists. exists (chunk_block ch).
      split; [exact (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in ICH. unfold CHUNK_HDR. lia. }
  exists (setpc (setf st rd fN) (pc4 st)), ms', mo'. split; [reflexivity|]. split; [exact AS|]. split; [exact MEM|]. split; [exact ST3| exact MP3].
Qed.

Theorem pkfld_sound : forall pc, contract_sound segs OPS MP PB (pkfld_contract pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pkfld_contract c_apply] in HAP.
  destruct (pkfld_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound.
End WithSegs.
End PkFld.
