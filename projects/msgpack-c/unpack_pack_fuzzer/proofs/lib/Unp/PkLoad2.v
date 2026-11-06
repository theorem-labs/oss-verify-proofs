(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAlg.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 W64Proofs Val IMap Mem Instr State Step Plan Notation ValProofs MemProofs StepSoundBase StepSoundMem PlanSound.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Heap Require Import Op.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree KidsFacts PkOps PkLib GLib PkStep PkStepA PkPeek.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Import PkPeek.

Module PkLoad2.
Section WithSegs.
Variable segs : list Segment.

Definition base_disp (fs : list fact) (b cf : sv) : option w64 :=
  if dec_true (decide_eq fs b cf) then Some wzero
  else if dec_true (decide_eq fs b (sv_alu ALU_ADD cf (VL (wlit 8%uint63)))) then Some (wlit 8%uint63)
  else if dec_true (decide_eq fs b (sv_alu ALU_ADD cf (VL (wlit 16%uint63)))) then Some (wlit 16%uint63)
  else None.

Definition pkload_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match load_at segs (s_pc st) with
          | Some (sz, sx, rd, rs, off0) =>
              let fs := s_facts st in
              match base_disp fs (getr st rs) cf with
              | Some d =>
              let off := wadd off0 d in
              let v := if weqb off (wlit 8%uint63) then Some fN else if weqb off (wlit 16%uint63) then Some fP else None in
              let isT (l : list Z) := match fT with VL t => existsb (fun x => weqb t (wlit (Uint63.of_Z x))) l | _ => false end in
              let okw := match sz with
                         | SZ8 => (weqb off (wlit 8%uint63) && isT [T_POSINT; T_NEGINT; T_FLOAT64; T_FLOAT32])
                                  || (weqb off (wlit 16%uint63) && isT [T_STR; T_BIN; T_ARRAY; T_MAP; T_EXT])
                         | SZ4 => weqb off (wlit 8%uint63) && isT [T_STR; T_BIN; T_ARRAY; T_MAP; T_EXT]
                         | SZ1 => weqb off (wlit 8%uint63) && negb sx && isT [T_BOOLEAN]
                         | SZ2 => false
                         end in
              match v with
              | Some v =>
                  if okw && negb (r5_eqb rd X0) && PrimInt63.ltb (s_pc st) bit62i
                     && dec_false (decide_eq0 fs cf)
                  then Some [setpc (setr st rd v) (PrimInt63.add (s_pc st) 4%uint63)]
                  else None
              | None => None
              end
              | None => None
              end
          | None => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Section WithPc.
Variable THE_PC : int.
Definition pkload2_contract : contract := Contract THE_PC pkload_apply.
End WithPc.
End WithSegs.

Section Sound2.
Variable segs : list Segment.
Variable IMGX : list iv.
Variable AW : alloc_world segs IMGX.
Variable CW : client_world.
Variable OPS : optable.
Hypothesis HOPS : heap_ops segs IMGX AW CW OPS.
Hypothesis CW3 : forall ca LB ws m, cw_holds CW 3 ca LB ws m -> PK.cw_pk_holds segs ca LB ws m.
Variable MP : Model -> Prop.
Variable PB : (int -> list byte) -> Prop.
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma isT_sound : forall E fT l,
  match fT with VL ty => existsb (fun x => weqb ty (wlit (Uint63.of_Z x))) l | _ => false end = true ->
  Forall (fun x => 0 <= x <= 10) l ->
  In (bv_unsigned (den E fT)) l.
Proof.
  intros E fT l H HL. destruct fT as [ty| | | | | | | | | |]; try discriminate.
  apply existsb_exists in H as (x & Hx & EQ). apply (proj1 (weqb_ok _ _)) in EQ. subst ty.
  pose proof (proj1 (Forall_forall _ _) HL x Hx) as R. cbn beta in R.
  cbn [den]. rewrite wbv_unsigned, wlit_ok, Uint63.of_Z_spec, Z.mod_small; [exact Hx|]. rewrite wB_two63. unfold two63. lia.
Qed.

Lemma ea_arith : forall A d o z, z = (o + d) mod two64 -> ((A + d) mod two64 + o) mod two64 = (A + z) mod two64.
Proof.
  intros A d o z ->. pose proof two64_eq as T64.
  rewrite Z.add_mod_idemp_l by lia. rewrite Z.add_mod_idemp_r by lia. f_equal. lia.
Qed.

Lemma base_disp_sound : forall E fs b cf d, facts_hold E fs -> base_disp fs b cf = Some d ->
  bv_unsigned (den E b) = (bv_unsigned (den E cf) + w2Z d) mod two64 /\ (d = wzero \/ d = wlit 8%uint63 \/ d = wlit 16%uint63).
Proof.
  intros E fs b cf d HF BD. unfold base_disp in BD.
  pose proof (bv_unsigned_in_range _ (den E cf)) as RC. rewrite bv_modulus_64 in RC.
  assert (STEP : forall x, dec_true (decide_eq fs b x) = true -> den E b = den E x).
  { intros x D. unfold dec_true in D. destruct (decide_eq fs b x) as [[|]|] eqn:DQ; try discriminate.
    pose proof (decide_eq_sound E fs HF _ _ _ DQ) as X. exact (proj1 (eqb_iff _ _ true) X). }
  assert (ADDL : forall c, bv_unsigned (den E (sv_alu ALU_ADD cf (VL (wlit c)))) = (bv_unsigned (den E cf) + w2Z (wlit c)) mod two64).
  { intros c. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned. unfold bv_wrap. rewrite bv_modulus_64. reflexivity. }
  destruct (dec_true (decide_eq fs b cf)) eqn:D0.
  - injection BD as <-. rewrite (STEP _ D0). split; [|left; reflexivity].
    replace (w2Z wzero) with 0 by reflexivity. rewrite Z.add_0_r, Z.mod_small by lia. reflexivity.
  - destruct (dec_true (decide_eq fs b (sv_alu ALU_ADD cf (VL (wlit 8%uint63))))) eqn:D8.
    + injection BD as <-. rewrite (STEP _ D8). split; [apply ADDL| right; left; reflexivity].
    + destruct (dec_true (decide_eq fs b (sv_alu ALU_ADD cf (VL (wlit 16%uint63))))) eqn:D16; [|discriminate].
      injection BD as <-. rewrite (STEP _ D16). split; [apply ADDL| right; right; reflexivity].
Qed.

Lemma pkload_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> pkload_apply segs st = Some sts ->
  exists st' ms' mo', sts = [st'] /\ mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\
                      st_ok segs OPS E st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS HMP AP.
  unfold pkload_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off0]|] eqn:LA; [|discriminate].
  cbv zeta in AP.
  destruct (base_disp (s_facts st) (getr st rs) cf) as [d|] eqn:BD; [|discriminate].
  remember (wadd off0 d) as off eqn:OFFD in AP.
  match type of AP with (match ?vv with Some _ => _ | None => None end) = _ => destruct vv as [v|] eqn:HV; [|discriminate] end.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND DNZ]. apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [OKW RDX].
  apply negb_true_iff in RDX.
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

  unfold dec_false in DNZ. destruct (decide_eq0 (s_facts st) cf) as [[|]|] eqn:DZ; try discriminate.
  pose proof (decide_eq0_sound E (s_facts st) Pfacts _ _ DZ) as CNZ. apply (proj1 (eqb_iff _ _ false)) in CNZ.
  assert (CF0 : bv_unsigned (den E cf) <> 0).
  { intros X. apply CNZ. apply bv_eq. rewrite X. reflexivity. }
  destruct (LCF CF0) as (LSNE & CFA & fo & FN & FT & FVIA & FPTR).
  pose proof (last_opt_spec ls) as LS. unfold focus_node in FN. unfold focus_addr in CFA.
  destruct (last_opt ls) as [l|] eqn:LAST; [| contradiction]. destruct LS as [ls0 ELS].
  assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
  pose proof (focus_obj_at _ _ _ _ _ KA HLV FN) as OAT.
  pose proof (focus_tree_wf _ _ _ _ _ _ TW HLV FN) as TWF.
  set (A := lev_addr l) in *.
  assert (AZ : in_zone (k_zone g) A OBJ_SIZE).
  { apply IC. apply (focus_cells _ _ _ _ _ A HLV FN). destruct fo; cbn; left; reflexivity. }
  destruct AZ as (ch & Hch & ICH).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA
              (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  assert (ABND : 0 <= A /\ A + OBJ_SIZE <= two64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH; unfold CHUNK_HDR in *; lia).

  destruct (base_disp_sound E (s_facts st) (getr st rs) cf d Pfacts BD) as [RSEQ DCASE].
  destruct (obj_at_fields segs (ms_mem ms) A fo OAT) as (TY & VIA & PTR & U32T & FLD).
  destruct (load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.

  assert (TL : Forall (fun x => 0 <= x <= 10) [T_POSINT; T_NEGINT; T_FLOAT64; T_FLOAT32] /\ Forall (fun x => 0 <= x <= 10) [T_STR; T_BIN; T_ARRAY; T_MAP; T_EXT]
               /\ Forall (fun x => 0 <= x <= 10) [T_BOOLEAN]) by (unfT; repeat constructor; lia).
  destruct TL as (TL1 & TL2 & TL3).
  assert (GOAL : exists offz z, off = wlit offz /\ (to_Z offz = 8 \/ to_Z offz = 16) /\
            rdZ (bmem_of segs (ms_mem ms)) (A + to_Z offz) (Z.to_nat (to_Z (msize_bytes sz))) = Some z /\
            den E v = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 z)).
  { clear OFFD. assert (DFN : den E fN = Z_to_bv 64 (obj_via fo)) by (apply bv_eq; rewrite <- FVIA, u64_of_Z by exact VIA; reflexivity).
    assert (DFP : den E fP = Z_to_bv 64 (obj_ptr fo)) by (apply bv_eq; rewrite <- FPTR, u64_of_Z by exact PTR; reflexivity).
    assert (INT : forall tl, Forall (fun x => 0 <= x <= 10) tl ->
              match fT with VL ty => existsb (fun x => weqb ty (wlit (Uint63.of_Z x))) tl | _ => false end = true -> In (obj_type fo) tl).
    { intros tl HL X. rewrite FT. exact (isT_sound E fT tl X HL). }
    destruct (weqb off (wlit 8%uint63)) eqn:O8.
    - apply (proj1 (weqb_ok _ _)) in O8. subst off. injection HV as <-. exists 8%uint63. rewrite DFN.
      change (to_Z 8%uint63) with 8.
      destruct sz; cbn [msize_bytes] in OKW |- *.
      +   apply andb_prop in OKW as [OKW IT]. apply andb_prop in OKW as [_ SX]. apply negb_true_iff in SX. subst sx.
        pose proof (INT _ TL3 IT) as IN. exists (obj_via fo). split; [reflexivity|]. split; [left; reflexivity|].
        destruct fo; cbn in IN; unfT; try lia; cbn [obj_via] in *.
        split; [change (Z.to_nat (to_Z 1%uint63)) with 1%nat; exact FLD|].
        change (to_Z 1%uint63) with 1. symmetry. apply PkStep.ext_word_small; [lia| destruct b; cbn; lia].
      + discriminate OKW.
      +   apply andb_prop in OKW as [_ IT]. pose proof (INT _ TL2 IT) as IN.
        exists (obj_via fo). split; [reflexivity|]. split; [left; reflexivity|].
        change (Z.to_nat (to_Z 4%uint63)) with 4%nat. change (to_Z 4%uint63) with 4.
        destruct fo; cbn in IN; unfT; try lia; cbn [obj_via] in *; destruct FLD as [F1 F2]; (split; [exact F1|]);
          symmetry; apply PkStep.ext_word_small; try lia; change (2 ^ (8 * 4 - 1)) with 2147483648.
        * cbn [tree_wf] in TWF. unfold LIMIT in TWF. lia.
        * cbn [tree_wf] in TWF. unfold LIMIT in TWF. lia.
        * cbn [tree_wf] in TWF. unfold LIMIT in TWF. lia.
        * apply tree_wf_arr in TWF. destruct TWF as (T1 & _). unfold LIMIT in T1. lia.
        * apply tree_wf_map in TWF. destruct TWF as (_ & T1 & _). unfold LIMIT in T1.
          pose proof (Z.div_pos (Z.of_nat (length kids)) 2 ltac:(lia) ltac:(lia)). lia.
      +   rewrite andb_false_l, orb_false_r in OKW. apply andb_prop in OKW as [_ IT]. pose proof (INT _ TL1 IT) as IN.
        exists (obj_via fo). split; [reflexivity|]. split; [left; reflexivity|].
        change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
        destruct fo; cbn in IN; unfT; try lia; cbn [obj_via] in *; (split; [exact FLD|]); rewrite ext_word_8, bv_extract_64; reflexivity.
    - destruct (weqb off (wlit 16%uint63)) eqn:O16; [|discriminate HV].
      apply (proj1 (weqb_ok _ _)) in O16. subst off. injection HV as <-. exists 16%uint63. rewrite DFP.
      change (to_Z 16%uint63) with 16.
      destruct sz; cbn [msize_bytes] in OKW |- *; rewrite ?O8 in OKW; cbn [andb orb] in OKW; try discriminate OKW.
      pose proof (INT _ TL2 OKW) as IN.
      exists (obj_ptr fo). split; [reflexivity|]. split; [right; reflexivity|].
      change (Z.to_nat (to_Z 8%uint63)) with 8%nat. change (to_Z 8%uint63) with 8.
      destruct fo; cbn in IN; unfT; try lia; cbn [obj_ptr] in *; destruct FLD as [F1 F2]; (split; [exact F2|]); rewrite ext_word_8, bv_extract_64; reflexivity. }
  destruct GOAL as (offz & z & OFFD0 & OFFZ & RD & DV). rewrite OFFD in OFFD0.
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL off0)) = Z_to_bv 64 (A + to_Z offz)).
  { apply bv_eq. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, RSEQ, CFA.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. unfold OBJ_SIZE in ABND.
    apply ea_arith. rewrite <- wlit_ok, <- OFFD0. apply wadd_ok. }
  assert (W8 : to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  destruct (PkStepA.oracle_ILoad_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E st ms model w i sz sx rd rs off0 (A + to_Z offz) z v HS HMP PCB FW EC DA OI HAD
              ltac:(lia) ltac:(unfold OBJ_SIZE in ABND; lia) RD DV) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  {
    intros j Hj. right. unfold userb. exists (map (den E) (op_args o)). do 5 eexists.
    split; [| split; [exact (DECf E)| split; [exact HA|]]].
    - unfold insts. apply in_map_iff. exists o. split; [rewrite OID; reflexivity| exact (op_in_In st o OPS1)].
    - unfold in_user, in_ivs. apply Exists_exists. exists (chunk_block ch).
      split; [exact (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in ICH.
      assert (W8' : to_Z (msize_bytes sz) <= 8) by exact W8. unfold CHUNK_HDR. lia. }
  exists (setpc (setr st rd v) (pc4 st)), ms', mo'. split; [reflexivity|]. split; [exact STEP|]. split; [exact MEM|]. split; [exact ST2| exact MP2].
Qed.

Theorem pkload2_sound : forall pc, contract_sound segs OPS MP PB (pkload2_contract segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pkload2_contract c_apply] in HAP.
  destruct (pkload_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound2.
End PkLoad2.
