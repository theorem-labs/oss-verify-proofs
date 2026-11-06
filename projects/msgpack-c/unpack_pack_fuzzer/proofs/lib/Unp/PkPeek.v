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
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import Model Layout Inv Steps OpsBridge Tree KidsFacts PkOps PkLib GLib PkStep PkStepA.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import AccStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Unp Require Import PkU PkUSem PkCost.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require Import ShapeAcc.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI St Step Plan ValP MemP StepB StepM PlanS HeapOp UB UG TR PK PKL.
Open Scope Z_scope.
Unset Lia Cache.
Arguments Uint63.to_Z : simpl never.
Arguments Z_to_bv : simpl never.

Module PkPeek.

Definition dec_true (o : option bool) : bool := match o with Some true => true | _ => false end.
Definition dec_false (o : option bool) : bool := match o with Some false => true | _ => false end.

Section WithSegs.
Variable segs : list Segment.

Definition load_at (pc : int) : option (msize * bool * r5 * r5 * w64) :=
  match fetch_word segs (Z_to_bv 64 (to_Z pc)) with
  | Some w =>
      if is_ecall w then None else
      match decode_any w with
      | Some (i, z) =>
          if Z.eqb z 4 then
            match of_instr i with Some (ILoad sz sx rd rs1 off) => Some (sz, sx, rd, rs1, off) | _ => None end
          else None
      | None => None
      end
  | None => None
  end.

Definition HMAX62 : w64 := wlit 4611686018427387904%uint63.

Definition peek_ty (c : Z) : Z := if c =? 15 then T_STR else if c =? 16 then T_BIN else c.
Definition peek_fields (t : Z) (n : int) : sv * sv * list fact :=
  let vN := VP n wzero in let vP := VP (PrimInt63.add n 1%uint63) wzero in
  if (t =? 15) || (t =? 16) then (VL wzero, VL wzero, [])
  else if t =? T_NIL then (VL wzero, VL wzero, [])
  else if t =? T_BOOLEAN then (vN, VL wzero, [FRange n wzero (wlit 1%uint63)])
  else if (t =? T_POSINT) || (t =? T_NEGINT) || (t =? T_FLOAT64) || (t =? T_FLOAT32) then (vN, VL wzero, [])
  else if (t =? T_STR) || (t =? T_BIN) then (vN, vP, [FRange n wzero (wlit 1000%uint63); FRange (PrimInt63.add n 1%uint63) (wlit 8%uint63) HMAX62])
  else if t =? T_EXT then (vN, vP, [FRange n wzero (wlit 999%uint63); FRange (PrimInt63.add n 1%uint63) (wlit 8%uint63) HMAX62])
  else   (vN, vP, [FRange n wzero (wlit 1000%uint63); FAlign (PrimInt63.add n 1%uint63) 3%uint63] ++ KF.kids_facts vN vP).

Definition TYPES : list Z := [0; 1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 15; 16].

Section WithPc.
Variable THE_PC : int.

Definition own_term (t : Z) (vN : sv) (u' : int) : sv :=
  if (t =? T_STR) || (t =? T_BIN) then VAlu ALU_ADD (VP u' (wlit 10%uint63)) vN
  else if t =? T_EXT then VAlu ALU_ADD (VP u' (wlit 11%uint63)) vN
  else VP u' (wlit 10%uint63).
Definition peek_cost (uo : option int) (n : int) (t : Z) (vN : sv) : list fact * int :=
  match uo with
  | Some u => ([FEq (own_term t vN (PrimInt63.add n 2%uint63)) (VP u wzero); FRange (PrimInt63.add n 2%uint63) wzero PkU.UMAX], PrimInt63.add n 3%uint63)
  | None => ([], PrimInt63.add n 2%uint63)
  end.
Definition peek_out (st : sstate) (aw : sv) (ws : list (sv * sv * sv)) (uo : option int) (pre : list sv) (cur : sv) (rd : r5) (t : Z) : sstate :=
  let n := s_next st in
  let '(vN, vP, nf) := peek_fields t n in
  setpc (setr (surg st [] [] (mk_args 3%uint63 aw ws (pre ++ [cur; VL (wlit (Uint63.of_Z (peek_ty t))); vN; vP])) (nf ++ fst (peek_cost uo n t vN)) (snd (peek_cost uo n t vN)))
              rd (VL (wlit (Uint63.of_Z (peek_ty t)))))
        (PrimInt63.add (s_pc st) 4%uint63).

Definition peek_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match load_at (s_pc st), tmap, tkey with
          | Some (SZ4, true, rd, rs, off), VL m, VL k =>
              let fs := s_facts st in let n := s_next st in
              let cur := getr st rs in
              let expect := if weqb m (wlit 1%uint63) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24%uint63)) else tptr in
              if weqb off wzero && negb (r5_eqb rd X0) && st_vars_below n st
                 && PrimInt63.ltb 0%uint63 n && PrimInt63.ltb n (PrimInt63.sub bit62i 8%uint63) && PrimInt63.ltb (s_pc st) bit62i
                 && Z.ltb (Z.of_nat (length ws)) 4095
                 && (weqb m wzero || weqb m (wlit 1%uint63)) && (weqb k wzero || weqb k (wlit 1%uint63))
                 && dec_true (decide_ltu fs (VL wzero) trest)
                 && dec_true (decide_eq fs cur expect)
              then match PkU.pku_move fs (fun fr => fr) false (PrimInt63.add n 2%uint63) ws with
                   | Some (uo, ws1) => Some (map (peek_out st aw ws1 uo [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey] cur rd) TYPES)
                   | None => None
                   end
              else None
          | _, _, _ => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition peek_contract : contract := Contract THE_PC peek_apply.

Definition pkload_apply (st : sstate) : option (list sstate) :=
  match the_op st with
  | Some (md, aw, ws, ca) =>
      if PrimInt63.eqb md 3%uint63 then
      match ca with
      | [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; tmap; tkey; cf; fT; fN; fP] =>
          match load_at (s_pc st) with
          | Some (sz, sx, rd, rs, off) =>
              let fs := s_facts st in
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
                     && dec_false (decide_eq0 fs cf) && dec_true (decide_eq fs (getr st rs) cf)
                  then Some [setpc (setr st rd v) (PrimInt63.add (s_pc st) 4%uint63)]
                  else None
              | None => None
              end
          | None => None
          end
      | _ => None
      end
      else None
  | None => None
  end.

Definition pkload_contract : contract := Contract THE_PC pkload_apply.

End WithPc.
End WithSegs.

Ltac unfT := unfold T_NIL, T_BOOLEAN, T_POSINT, T_NEGINT, T_FLOAT64, T_STR, T_BIN, T_ARRAY, T_MAP, T_EXT, T_FLOAT32 in *.

Lemma rdZ_word : forall segs m a n v, rdZ (bmem_of segs m) a n = Some v -> (n <= 8)%nat -> 0 <= v < two64.
Proof.
  intros segs m a n v H Hn. pose proof (UG.rdZ_nonneg _ _ _ _ (UG.bmem_of_bytes_range segs m) H) as R.
  assert (2 ^ (8 * Z.of_nat n) <= 2 ^ 64) by (apply Z.pow_le_mono_r; lia). unfold two64. lia.
Qed.

Lemma obj_at_fields : forall segs m a o, obj_at (bmem_of segs m) a o ->
  0 <= obj_type o <= 10 /\ 0 <= obj_via o < two64 /\ 0 <= obj_ptr o < two64 /\
  u32_at (bmem_of segs m) a (obj_type o) /\
  match o with
  | ONil => True
  | OBool _ => u8_at (bmem_of segs m) (a + 8) (obj_via o)
  | OPos _ | ONeg _ | OF32 _ | OF64 _ => u64_at (bmem_of segs m) (a + 8) (obj_via o)
  | _ => u32_at (bmem_of segs m) (a + 8) (obj_via o) /\ u64_at (bmem_of segs m) (a + 16) (obj_ptr o)
  end.
Proof.
  intros segs m a o H.
  assert (T : 0 <= obj_type o <= 10) by (destruct o; cbn; unfT; lia).
  assert (TWO : 0 <= 0 < two64 /\ 0 <= 1 < two64) by (unfold two64; lia).
  destruct o; try (apply obj_at_arr in H); try (apply obj_at_map in H); cbn [obj_at obj_via obj_ptr] in H |- *;
    unfold u64_at, u32_at, u8_at in *;
    repeat match goal with
    | [ H : _ /\ _ |- _ ] => destruct H
    | [ H : rdZ _ _ _ = Some _ |- _ ] => pose proof (rdZ_word segs m _ _ _ H ltac:(lia)); revert H
    end; intros; repeat split; try assumption; try lia; destruct b; lia.
Qed.

Lemma mem_pk_root : forall bm u u' g ls, a_root u' = a_root u -> mem_pk bm u g ls -> mem_pk bm u' g ls.
Proof. intros bm u u' g ls E M. unfold mem_pk in *. rewrite E. exact M. Qed.

Lemma load_at_spec : forall segs pc sz sx rd rs off, load_at segs pc = Some (sz, sx, rd, rs, off) ->
  exists w i, fetch_word segs (Z_to_bv 64 (to_Z pc)) = Some w /\ is_ecall w = false /\ decode_any w = Some (i, 4%Z) /\
              of_instr i = Some (ILoad sz sx rd rs off).
Proof.
  intros segs pc sz sx rd rs off H. unfold load_at in H.
  destruct (fetch_word segs (Z_to_bv 64 (to_Z pc))) as [w|] eqn:F; [|discriminate].
  destruct (is_ecall w) eqn:EC; [discriminate|].
  destruct (decode_any w) as [[i z]|] eqn:D; [|discriminate].
  destruct (Z.eqb_spec z 4); [|discriminate]. subst z.
  destruct (of_instr i) as [fi|] eqn:OI; [|discriminate]. destruct fi; try discriminate. injection H as <- <- <- <- <-.
  exists w, i. auto.
Qed.

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
Hypothesis HMPA : forall mo acc mo', MP mo -> materialize_model_accesses mo acc = Some mo' -> MP mo'.

Lemma env_upd_other : forall E n w k, k <> n -> ev (env_upd E n w) k = ev E k.
Proof. intros E n w k NE. cbn [env_upd ev]. destruct (PrimInt63.eqb k n) eqn:Q; [|reflexivity]. apply Uint63.eqb_correct in Q. contradiction. Qed.
Lemma u64_of_Z : forall z, 0 <= z < two64 -> bv_unsigned (Z_to_bv 64 z) = z.
Proof. intros z Hz. rewrite Z_to_bv_unsigned. apply bv_wrap_small. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. exact Hz. Qed.

Definition code (o : obj) : Z :=
  match o with
  | OStr p _ => if p =? 0 then 15 else T_STR
  | OBin p _ => if p =? 0 then 16 else T_BIN
  | _ => obj_type o
  end.
Lemma code_cases : forall o, In (code o) TYPES.
Proof. intros o. destruct o; cbn [code obj_type]; try (destruct (p =? 0)); unfT; cbn; tauto. Qed.
Lemma code_ty : forall o, peek_ty (code o) = obj_type o.
Proof. intros o. destruct o; cbn [code obj_type]; try (destruct (p =? 0)); unfT; reflexivity. Qed.
Lemma HMAX62_val : w2Z HMAX62 = two62Z.
Proof. vm_compute. reflexivity. Qed.

#[local] Opaque KF.kids_facts.
Lemma peek_sound_main : forall E st ms model sts,
  st_ok segs OPS E st ms model -> MP model -> peek_apply segs st = Some sts ->
  exists st' E' ms' mo', In st' sts /\ env_ext (s_next st) E E' /\
    mi_account_step segs ms model = MachineOk (ms', mo') /\ ms_mem ms' = ms_mem ms /\ st_ok segs OPS E' st' ms' mo' /\ MP mo'.
Proof.
  intros E st ms model sts HS0 HMP AP.
  unfold peek_apply in AP.
  destruct (the_op st) as [[[[mdi aw] ws] ca]|] eqn:TO; [|discriminate].
  destruct (PrimInt63.eqb mdi 3) eqn:MD; [|discriminate]. apply Uint63.eqb_correct in MD. subst mdi.
  destruct ca as [|root [|rootT [|n1 [|P1 [|zh [|c0 [|eb [|ee [|ecap [|tptr [|trest [|tmap [|tkey [|cf [|fT [|fN [|fP [|? ?]]]]]]]]]]]]]]]]]];
    try discriminate.
  destruct (load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  destruct sz; try discriminate. destruct sx; try discriminate.
  destruct tmap as [m| | | | | | | | | |]; try discriminate. destruct tkey as [k| | | | | | | | | |]; try discriminate.
  cbv zeta in AP.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  apply andb_prop in COND as [COND DEQ]. apply andb_prop in COND as [COND DREST]. apply andb_prop in COND as [COND KB]. apply andb_prop in COND as [COND MB].
  apply andb_prop in COND as [COND WLEN]. apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [COND NLT]. apply andb_prop in COND as [COND NPOS].
  apply andb_prop in COND as [COND VB]. apply andb_prop in COND as [OFF RDX].
  apply (proj1 (weqb_ok _ _)) in OFF. subst off. apply negb_true_iff in RDX.
  apply Z.ltb_lt in WLEN. apply Uint63.ltb_spec in NPOS. change (to_Z 0%uint63) with 0 in NPOS. apply Uint63.ltb_spec in NLT.
  change (to_Z (PrimInt63.sub bit62i 8%uint63)) with (4611686018427387904 - 8) in NLT.
  destruct (PkU.pku_move (s_facts st) (fun fr => fr) false (PrimInt63.add (s_next st) 2) ws) as [[uo ws1]|] eqn:MV; [|discriminate AP].
  injection AP as <-.
  set (n := s_next st) in *. set (cur := getr st rs) in *.
  assert (NZ : PrimInt63.eqb n 0%uint63 = false) by (apply (proj2 (Uint63.eqb_false_spec _ _)); intros X; rewrite X in NPOS; change (to_Z 0%uint63) with 0 in NPOS; lia).
  pose proof HS0 as [Ppc0 Px00 Pregs0 _ _ _ _ _ _ Pbst0 _ _ _ Pfacts0 Pops0 _ _ _].
  destruct (the_op_full st 3%uint63 aw ws _ TO) as (o & mdv & nwv & OPS1 & OID & ARGS & DECf & LEN).
  pose proof OPS1 as (opre & opost & OPSEQ & OPOTH).
  pose proof (ops_vars_below n st o VB (op_in_In st o OPS1)) as VBo.
  assert (VBrf : rf_allb (sv_vars_below n) (s_rf st) = true).
  { pose proof VB as VB'. unfold st_vars_below in VB'. do 4 (apply andb_prop in VB' as [VB' _]). apply andb_prop in VB' as [VB' _]. exact VB'. }
  assert (VBcur : sv_vars_below n cur = true) by (subst cur; unfold getr; exact (rf_allb_get _ _ _ VBrf rs)).
  assert (INCA : forall v, In v [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; VL m; VL k; cf; fT; fN; fP] -> In v (op_args o)).
  { intros v Hv. rewrite ARGS. right; right; right. apply in_app_iff. right. exact Hv. }

  pose proof (ops_hold_in OPS _ _ _ _ o Pops0 (op_in_In st o OPS1)) as OH. rewrite OID, (ho_holds _ _ _ _ _ HOPS) in OH.
  destruct OH as (md & awZ & wsZ & caZ & LB & DEC0 & HA & WF & HC).
  rewrite (DECf E) in DEC0. injection DEC0 as <- <- <- <-. change (to_Z 3%uint63) with 3 in HC.
  apply CW3 in HC. unfold cw_pk_holds in HC. cbn [map decode_pk] in HC.
  destruct HC as (g & ls & L & P & O & Wk & M & GH & CO).
  pose proof L as (LT & LN & LP & Lc0 & Leb & Lee & Lecap & LTOP & LCF).
  cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP] in LT, LN, LP, Lc0, Leb, Lee, Lecap, LTOP, LCF.
  pose proof P as (LV & EL & SZ & VE & CE & ZV).
  pose proof M as (TW & KA & [IC IB] & CH & PE).

  unfold dec_true in DREST. destruct (decide_ltu (s_facts st) (VL wzero) trest) as [[|]|] eqn:DRE; try discriminate.
  pose proof (decide_ltu_sound E (s_facts st) Pfacts0 _ _ _ DRE) as REST. apply (proj1 (ltu_iff _ _ true)) in REST.
  cbn [den] in REST. rewrite wbv_unsigned, wzero_ok in REST.
  destruct (last_opt ls) as [l|] eqn:LAST.
  2: { exfalso. destruct LTOP as (_ & T0 & _). lia. }
  destruct LTOP as (Ltp & Ltr & Ltm & Ltk).
  pose proof (last_opt_spec ls) as LS. rewrite LAST in LS. destruct LS as [ls0 ELS].

  assert (HLV : levels_ok (k_tree g) (ls0 ++ [l])) by (rewrite <- ELS; exact LV).
  assert (RPOS : 0 < pe_rest (elem_of l)) by lia.
  destruct (rest_pos_node _ _ _ HLV RPOS) as [fo HFO].
  pose proof (proj1 (Forall_forall _ _) (levels_forall _ _ HLV) l ltac:(apply in_app_iff; right; left; reflexivity)) as [LC LS0].
  pose proof (focus_obj_at _ _ _ _ _ KA HLV HFO) as OAT.
  pose proof (focus_tree_wf _ _ _ _ _ _ TW HLV HFO) as TWF.
  set (A := lev_addr l) in *.

  assert (AZ : in_zone (k_zone g) A OBJ_SIZE).
  { apply IC. apply (focus_cells _ _ _ _ _ A HLV HFO). destruct fo; cbn; left; reflexivity. }
  destruct AZ as (ch & Hch & ICH).
  destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch) HA
              (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))) as (Bc1 & Bc2 & Bc3 & Bc4 & Bc5).
  unfold chunk_block in Bc1, Bc2, Bc3. cbn [fst snd] in Bc1, Bc2, Bc3.
  assert (ABND : 0 <= A /\ A + OBJ_SIZE <= two64) by (unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH; unfold CHUNK_HDR in *; lia).

  unfold dec_true in DEQ.
  destruct (decide_eq (s_facts st) cur (if weqb m (wlit 1) && weqb k wzero then sv_alu ALU_ADD tptr (VL (wlit 24)) else tptr)) as [[|]|] eqn:DQ; try discriminate.
  pose proof (decide_eq_sound E (s_facts st) Pfacts0 _ _ _ DQ) as CUREQ. apply (proj1 (eqb_iff _ _ true)) in CUREQ.
  assert (PMAP : pe_map (elem_of l) = weqb m (wlit 1%uint63)).
  { cbn [den] in Ltm. rewrite wbv_unsigned in Ltm. apply orb_prop in MB as [MB|MB]; apply (proj1 (weqb_ok _ _)) in MB; subst m;
    [rewrite wzero_ok in Ltm | rewrite wlit_ok in Ltm; change (to_Z 1%uint63) with 1 in Ltm];
    destruct (pe_map (elem_of l)); cbn [b2Z] in Ltm; try lia; reflexivity. }
  assert (PKEY : pe_key (elem_of l) = weqb k (wlit 1%uint63)).
  { cbn [den] in Ltk. rewrite wbv_unsigned in Ltk. apply orb_prop in KB as [KB|KB]; apply (proj1 (weqb_ok _ _)) in KB; subst k;
    [rewrite wzero_ok in Ltk | rewrite wlit_ok in Ltk; change (to_Z 1%uint63) with 1 in Ltk];
    destruct (pe_key (elem_of l)); cbn [b2Z] in Ltk; try lia; reflexivity. }
  assert (PM : pe_map (elem_of l) && negb (pe_key (elem_of l)) = (weqb m (wlit 1%uint63) && weqb k wzero)).
  { rewrite PMAP, PKEY. apply orb_prop in KB as [KB|KB]; apply (proj1 (weqb_ok _ _)) in KB; subst k; reflexivity. }
  pose proof (elem_of_obj l LS0) as POBJ. unfold pe_obj in POBJ. fold A in POBJ. rewrite PM in POBJ.
  pose proof (bv_unsigned_in_range _ (den E tptr)) as TPR. unfold bv_modulus in TPR. change (2 ^ Z.of_N 64) with two64 in TPR.
  assert (CURA : bv_unsigned (den E cur) = A).
  { rewrite CUREQ. destruct (weqb m (wlit 1%uint63) && weqb k wzero).
    - rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok. change (to_Z 24%uint63) with 24.
      unfold OBJ_SIZE in *. rewrite bv_wrap_small; [lia|]. unfold bv_modulus. change (2 ^ Z.of_N 64) with two64. lia.
    - unfold OBJ_SIZE in *. lia. }

  destruct (obj_at_fields segs (ms_mem ms) A fo OAT) as (TY & VIA & PTR & U32T & FLD).
  set (t := obj_type fo) in *.

  assert (N1 : to_Z (PrimInt63.add n 1) = to_Z n + 1) by (rewrite Uint63.add_spec; change (to_Z 1%uint63) with 1; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (N2 : to_Z (PrimInt63.add n 2) = to_Z n + 2) by (rewrite Uint63.add_spec; change (to_Z 2%uint63) with 2; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (NE1 : n <> PrimInt63.add n 1) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE2 : n <> PrimInt63.add n 2) by (intros X; apply (f_equal to_Z) in X; lia).
  assert (NE12 : PrimInt63.add n 1 <> PrimInt63.add n 2) by (intros X; apply (f_equal to_Z) in X; lia).
  set (E1 := env_upd E n (Z_to_bv 64 (obj_via fo))).
  set (E2 := env_upd E1 (PrimInt63.add n 1) (Z_to_bv 64 (obj_ptr fo))).

  set (UV := match uo with Some uold => bv_unsigned (ev E uold) - own10 fo | None => 0 end).
  set (E' := env_upd E2 (PrimInt63.add n 2) (Z_to_bv 64 UV)).
  assert (HX : env_ext n E E').
  { apply (env_ext_trans n (PrimInt63.add n 2) E E2); [lia| | apply env_upd_ext].
    apply (env_ext_trans n (PrimInt63.add n 1) E E1); [lia| apply env_upd_ext| apply env_upd_ext]. }
  assert (EVn : ev E' n = Z_to_bv 64 (obj_via fo)).
  { subst E' E2 E1. rewrite (env_upd_other _ _ _ _ NE2), (env_upd_other _ _ _ _ NE1). apply env_upd_same. }
  assert (EVn1 : ev E' (PrimInt63.add n 1) = Z_to_bv 64 (obj_ptr fo)) by (subst E' E2 E1; rewrite (env_upd_other _ _ _ _ NE12); apply env_upd_same).
  assert (EVn2 : ev E' (PrimInt63.add n 2) = Z_to_bv 64 UV) by (subst E'; apply env_upd_same).
  assert (DR : forall v, In v (op_args o) -> den E' v = den E v) by (intros v Hv; exact (den_reval n E E' HX v (VBo v Hv))).
  assert (Dcur : den E' cur = den E cur) by exact (den_reval n E E' HX cur VBcur).
  clearbody E'. clear E1 E2.
  assert (HS : st_ok segs OPS E' st ms model) by exact (st_ok_reval segs OPS n E E' HX st ms model NPOS VB HS0).
  clear Ppc0 Px00 Pregs0 Pbst0.
  pose proof HS as [Ppc Px0 Pregs Pfregs Psvc Presv Pfcsr Prom Pz Pbst Preg Pdisj Ppub Pfacts Pops Papart Pmf Pcov Pminv].
  assert (WSEw : forall w, In w ws -> wden E' w = wden E w).
  { intros [[wa wb] wc] Hw. unfold wden. destruct (in_flat_windows ws wa wb wc Hw) as (Ia & Ib & Ic).
    rewrite !DR; [reflexivity| | |]; rewrite ARGS; right; right; right; apply in_app_iff; left; assumption. }
  assert (WSE : map (wden E') ws = map (wden E) ws) by (apply map_ext_in; exact WSEw).

  assert (FAL : Forall (fun l0 => tree_wf (bmem_of segs (ms_mem ms)) (k_zone g) (fst l0)) (ls0 ++ [l])) by exact (levels_wf _ _ _ _ TW HLV).
  assert (UVB : 0 <= UV <= 2 ^ 41 /\ (forall uold, uo = Some uold -> bv_unsigned (ev E' uold) = bv_unsigned (ev E uold) /\ 0 <= own10 fo <= bv_unsigned (ev E uold)) /\
                (uo <> None -> forall cz', np (k_tree g) ls false cz' <= UV)).
  { subst UV. destruct uo as [uold|]; [| split; [lia| split; [discriminate| intros X; contradiction]]].
    destruct (PkUSem.move_old E (s_facts st) Pfacts0 _ _ _ ws uold ws1 MV) as (wpre & fr & wpost & OKfr & EWS & EWS1 & UB & PV).
    cbn beta in OKfr. subst fr.
    assert (INW : In (PkU.mk_pku true uold) ws) by (rewrite EWS; apply in_app_iff; right; left; reflexivity).
    pose proof (CO (wden E (PkU.mk_pku true uold)) true _ (in_map _ _ _ INW) PV) as LE0. rewrite ELS in LE0.
    assert (BND : forall cz', 0 <= own10 fo <= bv_unsigned (ev E uold) /\ 0 <= np (k_tree g) (ls0 ++ [l]) false cz' <= bv_unsigned (ev E uold) - own10 fo).
    { intros cz'. exact (PkCost.np_peek_bound _ _ (k_tree g) ls0 l fo _ cz' _ HFO TWF FAL LE0). }
    destruct (BND true) as [B1 B2].
    split; [lia|]. split.
    - intros u0 [= <-]. split; [| exact B1]. f_equal. exact (PkUSem.mk_pku_ev E E' true uold (WSEw _ INW)).
    - intros _ cz'. rewrite ELS. exact (proj2 (proj2 (BND cz'))). }
  destruct UVB as (UVR & UOLD & UNP).
  assert (UB2 : bv_unsigned (ev E' (PrimInt63.add n 2)) <= 2 ^ 41) by (rewrite EVn2, u64_of_Z; [lia| unfold two64; lia]).
  destruct (PkUSem.move_sound E' (s_facts st) Pfacts _ _ _ ws uo ws1 MV UB2) as (LENmv & INWS1 & KEEP1 & WF1 & WK1 & GH1 & CO1 & MVN & MVS).
  assert (LEN1 : Z.of_nat (length ws1) < two63) by (rewrite LENmv; exact LEN).
  pose proof (DECf E') as DEC.

  assert (ALN : forall p ks, fo = OArr p ks \/ fo = OMap p ks -> p mod 8 = 0).
  { intros p ks [-> | ->]; [apply tree_wf_arr in TWF; destruct TWF as (_ & E0 & NE & _) | apply tree_wf_map in TWF; destruct TWF as (_ & _ & E0 & NE & _)];
      (destruct ks as [|k0 ks0]; [rewrite (proj1 E0 eq_refl); reflexivity | exact (proj1 (NE ltac:(discriminate)))]). }

  assert (ZB : forall p sz, in_zone (k_zone g) p sz -> 0 <= sz -> 4104 <= p /\ p + sz <= 4611686018427387904).
  { intros p sz (ch' & Hch' & ICH') Hsz.
    pose proof (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch')) as INB.
    destruct (aw_blocks_ok segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch') HA INB) as (Bd1 & Bd2 & Bd3 & Bd4 & Bd5).
    pose proof (aw_blocks_lo segs IMGX AW _ LB _ (ms_mem ms) model (chunk_block ch') HA INB) as BLO.
    pose proof (aw_ceiling_small segs IMGX AW model) as CS. unfold Mem.two62Z in CS.
    unfold chunk_block in Bd1, Bd2, Bd3, BLO. cbn [fst snd] in Bd1, Bd2, Bd3, BLO.
    unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR in ICH'. unfold CHUNK_HDR in *. lia. }
  pose proof (KF.kids_pure _ _ _ TWF ZB) as (KP1 & KP2 & KP3 & KP4).
  set (c := code fo) in *.
  assert (CTY : peek_ty c = t) by (subst c t; apply code_ty).
  destruct (peek_fields c n) as [[vN vP] nf] eqn:PF.
  assert (DVN : bv_unsigned (den E' vN) = obj_via fo /\ bv_unsigned (den E' vP) = obj_ptr fo /\ Forall (fact_holds E') nf).
  { unfold peek_fields in PF. subst c t.
    assert (DN : bv_unsigned (den E' (VP n wzero)) = obj_via fo) by (rewrite (den_VP0 E' n wzero (weqb_refl _)), EVn; apply u64_of_Z; exact VIA).
    assert (DP : bv_unsigned (den E' (VP (PrimInt63.add n 1) wzero)) = obj_ptr fo) by (rewrite (den_VP0 E' _ wzero (weqb_refl _)), EVn1; apply u64_of_Z; exact PTR).
    assert (D0 : bv_unsigned (den E' (VL wzero)) = 0) by (cbn [den]; rewrite wbv_unsigned, wzero_ok; reflexivity).
    destruct fo; cbn [code obj_type] in PF;
      try (match type of PF with context [?q =? 0] => destruct (Z.eqb_spec q 0) as [PZ|PNZ] end);
      unfT; cbn in PF; injection PF as <- <- <-; cbn [obj_via obj_ptr] in *; cbn [tree_wf] in TWF; unfold LIMIT in *;
      try (pose proof PZ as _; destruct TWF as (TWn & TWz & TWnz); pose proof (TWz PZ));
      try (pose proof PNZ as _; destruct TWF as (TWn & TWz & TWnz); destruct (TWnz PNZ) as [TWin _]; pose proof (ZB _ _ TWin ltac:(lia)));
      try (destruct TWF as (TWn & TWn1 & TWp & TWin & _); pose proof (ZB _ _ TWin ltac:(lia)));
      (split; [first [exact DN | rewrite D0; lia] | split; [first [exact DP | rewrite D0; lia] |]]);
      repeat constructor; cbn [fact_holds]; rewrite ?HMAX62_val, ?EVn, ?EVn1, ?u64_of_Z, ?wlit_ok, ?wzero_ok by lia;
      try (change (to_Z 1%uint63) with 1); try (change (to_Z 8%uint63) with 8); try (change (to_Z 1000%uint63) with 1000); try (change (to_Z 999%uint63) with 999);
      try (change (2 ^ to_Z 3%uint63) with 8); try (unfold two62Z in *; lia).
    - destruct b; lia.
    - exact (ALN p kids (or_introl eq_refl)).
    - exact (KF.kids_facts_sound E' _ _ _ _ DN DP KP1 KP2 KP3 KP4).
    - exact (ALN p kids (or_intror eq_refl)).
    - exact (KF.kids_facts_sound E' _ _ _ _ DN DP KP1 KP2 KP3 KP4). }
  destruct DVN as (DVN & DVP & HNF).

  set (cfx := fst (peek_cost uo n c vN)). set (nx := snd (peek_cost uo n c vN)).
  assert (HCF : Forall (fact_holds E') cfx).
  { subst cfx. unfold peek_cost. destruct uo as [uold|]; cbn [fst]; [| constructor].
    destruct (UOLD uold eq_refl) as [EVold OWB].
    assert (VN2 : bv_unsigned (ev E' (PrimInt63.add n 2)) = UV) by (rewrite EVn2; apply u64_of_Z; unfold two64; lia).
    assert (UVE : UV = bv_unsigned (ev E uold) - own10 fo) by reflexivity.
    pose proof (bv_unsigned_in_range _ (ev E uold)) as RU. rewrite bv_modulus_64 in RU.
    constructor; [| constructor; [| constructor]].
    - cbn [fact_holds]. apply bv_eq. rewrite (den_VP0 E' uold wzero (weqb_refl _)), EVold.
      assert (LITV : forall d, 0 <= d <= 11 -> w2Zs (wlit (Uint63.of_Z d)) = d).
      { intros d Hd. unfold w2Zs. cbn [wlit wt]. rewrite wlit_ok, Uint63.of_Z_spec. apply Z.mod_small. rewrite wB_two63. unfold two63. lia. }
      assert (BASE : forall d, 0 <= d <= 11 -> bv_unsigned (den E' (VP (PrimInt63.add n 2) (wlit (Uint63.of_Z d)))) = UV + d).
      { intros d Hd. rewrite den_VP, VN2, (LITV d Hd). apply Z.mod_small. unfold two64. lia. }
      unfold own_term. subst c.
      destruct fo; cbn [code obj_type own10] in *; try (match goal with |- context [?q =? 0] => destruct (Z.eqb_spec q 0) as [PZ|PNZ] end);
        unfT; cbn [Z.eqb orb Pos.eqb]; cbn [tree_wf] in TWF; cbn [obj_via] in DVN;
        try (change (wlit 10%uint63) with (wlit (Uint63.of_Z 10))); try (change (wlit 11%uint63) with (wlit (Uint63.of_Z 11)));
        try (rewrite (BASE 10) by lia; lia);
        try (cbn [den alu64 alu]; rewrite bv_add_unsigned; fold (den E' (VP (PrimInt63.add n 2) (wlit (Uint63.of_Z 10)))); fold (den E' (VP (PrimInt63.add n 2) (wlit (Uint63.of_Z 11))));
             rewrite ?(BASE 10), ?(BASE 11), DVN by lia; unfold bv_wrap; rewrite bv_modulus_64, Z.mod_small by (unfold LIMIT, two64 in *; lia); lia).
      all: try (destruct TWF as (TWn & TWz & _); pose proof (TWz PZ); rewrite (BASE 10) by lia; lia).
    - cbn [fact_holds]. rewrite VN2. change (w2Z wzero) with 0. change (w2Z PkU.UMAX) with (2 ^ 41). lia. }

  set (pre := [root; rootT; n1; P1; zh; c0; eb; ee; ecap; tptr; trest; VL m; VL k]) in *.
  set (ca' := pre ++ [cur; VL (wlit (Uint63.of_Z t)); vN; vP]).
  assert (TLT : to_Z (Uint63.of_Z t) = t) by (rewrite Uint63.of_Z_spec; apply Z.mod_small; rewrite wB_two63; unfold two63; lia).
  assert (HA1 : forall awv, awv = den E' aw -> aw_holds segs IMGX AW awv LB (map (wden E') ws1) (ms_mem ms) model).
  { intros awv ->. rewrite (DR aw ltac:(rewrite ARGS; right; left; reflexivity)). refine (aw_keep segs IMGX AW _ _ _ _ _ _ _ (KEEP1 LB)). rewrite WSE. exact HA. }
  assert (ST1 : st_ok segs OPS E' (surg st [] [] (mk_args 3%uint63 aw ws1 ca') (nf ++ cfx) nx) ms model).
  { apply (surgery_sound segs OPS E' (ho_other _ _ _ _ _ HOPS) (ho_cover _ _ _ _ _ HOPS) st ms model o HS opre opost OPSEQ OID OPOTH [] [] _ _ nx).
    - intros kk [].
    - constructor.
    - intros kk r [].
    - intros kk r [].
    - intros kk r a [].
    - intros k1 r1 k2 r2 a [].
    - rewrite (ho_holds _ _ _ _ _ HOPS).
      exists 3, (den E' aw), (map (wden E') ws1), (map (den E') ca'), LB.
      split; [apply (mk_args_sound E' 3%uint63 aw ws1 _ LEN1)|].
      split; [exact (HA1 _ eq_refl)|]. split; [apply (WF1 segs IMGX AW LB _ (aw_ceiling_small segs IMGX AW model)); rewrite WSE; exact WF|].
      apply CW3'. unfold cw_pk_holds. subst ca' pre. cbn [map app decode_pk].
      exists g, ls. split; [| split; [exact P| split; [exact O| split; [apply (WK1 g); rewrite WSE; exact Wk|]]]].
      2: { split; [| split; [apply (GH1 g); rewrite WSE; exact GH|]].
           { refine (mem_pk_root _ _ _ g ls _ M). cbn [a_root]. rewrite (DR root ltac:(apply INCA; left; reflexivity)). reflexivity. }

           eapply (CO1 _ g ls); [rewrite WSE; exact CO|]. intros fr uold UO _ _. rewrite EVn2, u64_of_Z by (unfold two64; lia).
           apply UNP. rewrite UO. discriminate. }
      unfold link_pk. cbn [a_root a_rootT a_n1 a_P1 a_c0 a_eb a_ee a_ecap a_tptr a_trest a_tmap a_tkey a_cf a_fT a_fN a_fP].
      rewrite (DR rootT) by (apply INCA; right; left; reflexivity).
      rewrite (DR n1) by (apply INCA; do 2 right; left; reflexivity).
      rewrite (DR P1) by (apply INCA; do 3 right; left; reflexivity).
      rewrite (DR c0) by (apply INCA; do 5 right; left; reflexivity).
      rewrite (DR eb) by (apply INCA; do 6 right; left; reflexivity).
      rewrite (DR ee) by (apply INCA; do 7 right; left; reflexivity).
      rewrite (DR ecap) by (apply INCA; do 8 right; left; reflexivity).
      rewrite (DR tptr) by (apply INCA; do 9 right; left; reflexivity).
      rewrite (DR trest) by (apply INCA; do 10 right; left; reflexivity).
      split; [exact LT|]. split; [exact LN|]. split; [exact LP|]. split; [exact Lc0|]. split; [exact Leb|]. split; [exact Lee|]. split; [exact Lecap|].
      split; [rewrite LAST; repeat split; assumption|].
      intros _. split; [rewrite ELS; destruct ls0; discriminate|]. split.
      + rewrite Dcur, CURA. unfold focus_addr. rewrite LAST. reflexivity.
      + exists fo. unfold focus_node. rewrite LAST. split; [exact HFO|]. split; [| split; [symmetry; exact DVN| symmetry; exact DVP]].
        cbn [den]. rewrite wbv_unsigned, wlit_ok, TLT. reflexivity.
    - intros a FPa. split; [| intros kk r []]. left. unfold FP in *. rewrite (ho_fp _ _ _ _ _ HOPS) in *.
      apply (proj2 (heap_fp_iff IMGX _ 3 _ (map (wden E') ws) _ a DEC)).
      destruct (proj1 (heap_fp_iff IMGX _ 3 _ (map (wden E') ws1) _ a (mk_args_sound E' 3%uint63 aw ws1 _ LEN1)) FPa) as (F1 & F2 & F3).
      split; [exact F1|]. split; [exact F2|]. intros X. apply F3. apply INWS1. exact X.
    - apply Forall_app. split; [exact HNF| exact HCF]. }

  destruct (load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI).
  assert (PCV : ms_pc_val ms = Z_to_bv 64 (to_Z (s_pc st))) by exact Ppc.
  rewrite <- PCV in FW.
  assert (HAD : den E' (sv_alu ALU_ADD (getr (surg st [] [] (mk_args 3%uint63 aw ws1 ca') (nf ++ cfx) nx) rs) (VL wzero)) = Z_to_bv 64 A).
  { change (getr (surg st [] [] (mk_args 3%uint63 aw ws1 ca') (nf ++ cfx) nx) rs) with cur.
    apply bv_eq. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, wzero_ok, Z.add_0_r, Dcur, CURA.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. unfold OBJ_SIZE in ABND.
    rewrite !Z.mod_small by lia. reflexivity. }
  assert (DVT : den E' (VL (wlit (Uint63.of_Z t))) = ext_word true 0 (to_Z (msize_bytes SZ4)) (Z_to_bv 64 t)).
  { change (to_Z (msize_bytes SZ4)) with 4. rewrite PkStep.ext_word_small by lia. cbn [den]. apply bv_eq. rewrite wbv_unsigned, wlit_ok, TLT.
    rewrite u64_of_Z by (unfold two64; lia). reflexivity. }
  destruct (PkStepA.oracle_ILoad_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E' _ ms model w i SZ4 true rd rs wzero A t (VL (wlit (Uint63.of_Z t))) ST1 HMP PCB FW EC DA OI HAD
              (proj1 ABND) ltac:(change (to_Z (msize_bytes SZ4)) with 4; unfold OBJ_SIZE in ABND; lia)
              ltac:(change (Z.to_nat (to_Z (msize_bytes SZ4))) with 4%nat; exact U32T) DVT) as (ms' & mo' & STEP & MEM & ST2 & MP2).
  {
    intros j Hj. change (to_Z (msize_bytes SZ4)) with 4 in Hj. right.
    exists (map (den E') (mk_args 3%uint63 aw ws1 ca')), 3, (den E' aw), (map (wden E') ws1), (map (den E') ca'), LB.
    split; [| split; [apply (mk_args_sound E' 3%uint63 aw ws1 _ LEN1)| split]].
    - unfold insts. apply in_map_iff. exists (OpI OPID (mk_args 3%uint63 aw ws1 ca')). split; [reflexivity|].
      cbn [surg s_ops]. rewrite OPSEQ. rewrite (set_op_split _ opre o opost OID OPOTH). apply in_elt.
    - exact (HA1 _ eq_refl).
    - unfold in_user, in_ivs. apply Exists_exists. exists (chunk_block ch).
      split; [exact (proj1 O _ ltac:(unfold owned; apply in_app_iff; right; apply in_map; exact Hch))|].
      unfold in_iv, chunk_block. cbn [fst snd]. unfold in_chunk, chunk_lo, chunk_hi, CHUNK_HDR, OBJ_SIZE in ICH. unfold CHUNK_HDR. lia. }
  exists (peek_out st aw ws1 uo pre cur rd c), E', ms', mo'.
  split; [exact (in_map (peek_out st aw ws1 uo pre cur rd) TYPES c (code_cases fo))|].
  split; [exact HX|]. split; [exact STEP|]. split; [exact MEM|]. split; [| exact MP2].
  unfold peek_out. fold n. rewrite PF, CTY. exact ST2.
Qed.

Theorem peek_sound : forall pc, contract_sound segs OPS MP PB (peek_contract segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [peek_contract c_apply] in HAP.
  destruct (peek_sound_main E st ms model sts HS HMP HAP) as (st' & E' & ms' & mo' & IN & HX & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  exact (Hk st' IN E' ms' mo' HX HMP' HS').
Qed.
End Sound.

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
  destruct (load_at segs (s_pc st)) as [[[[[sz sx] rd] rs] off]|] eqn:LA; [|discriminate].
  cbv zeta in AP.
  match type of AP with (match ?vv with Some _ => _ | None => None end) = _ => destruct vv as [v|] eqn:HV; [|discriminate] end.
  match type of AP with (if ?c then _ else _) = _ => destruct c eqn:COND; [|discriminate] end.
  injection AP as <-.
  apply andb_prop in COND as [COND DEQ]. apply andb_prop in COND as [COND DNZ]. apply andb_prop in COND as [COND PCB]. apply andb_prop in COND as [OKW RDX].
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

  unfold dec_true in DEQ. destruct (decide_eq (s_facts st) (getr st rs) cf) as [[|]|] eqn:DQ; try discriminate.
  pose proof (decide_eq_sound E (s_facts st) Pfacts _ _ _ DQ) as RSEQ. apply (proj1 (eqb_iff _ _ true)) in RSEQ.
  destruct (obj_at_fields segs (ms_mem ms) A fo OAT) as (TY & VIA & PTR & U32T & FLD).
  destruct (load_at_spec segs (s_pc st) _ _ _ _ _ LA) as (w & i & FW & EC & DA & OI). rewrite <- Ppc in FW.

  assert (TL : Forall (fun x => 0 <= x <= 10) [T_POSINT; T_NEGINT; T_FLOAT64; T_FLOAT32] /\ Forall (fun x => 0 <= x <= 10) [T_STR; T_BIN; T_ARRAY; T_MAP; T_EXT]
               /\ Forall (fun x => 0 <= x <= 10) [T_BOOLEAN]) by (unfT; repeat constructor; lia).
  destruct TL as (TL1 & TL2 & TL3).
  assert (GOAL : exists offz z, off = wlit offz /\ (to_Z offz = 8 \/ to_Z offz = 16) /\
            rdZ (bmem_of segs (ms_mem ms)) (A + to_Z offz) (Z.to_nat (to_Z (msize_bytes sz))) = Some z /\
            den E v = ext_word sx 0 (to_Z (msize_bytes sz)) (Z_to_bv 64 z)).
  { assert (DFN : den E fN = Z_to_bv 64 (obj_via fo)) by (apply bv_eq; rewrite <- FVIA, u64_of_Z by exact VIA; reflexivity).
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
  destruct GOAL as (offz & z & -> & OFFZ & RD & DV).
  assert (HAD : den E (sv_alu ALU_ADD (getr st rs) (VL (wlit offz))) = Z_to_bv 64 (A + to_Z offz)).
  { apply bv_eq. rewrite den_sv_alu. cbn [den alu64 alu]. rewrite bv_add_unsigned, wbv_unsigned, wlit_ok, RSEQ, CFA.
    rewrite !Z_to_bv_unsigned. unfold bv_wrap, bv_modulus. change (2 ^ Z.of_N 64) with two64. unfold OBJ_SIZE in ABND.
    rewrite !Z.mod_small by lia. reflexivity. }
  assert (W8 : to_Z (msize_bytes sz) <= 8) by (destruct sz; cbn [msize_bytes]; [change (to_Z 1%uint63) with 1| change (to_Z 2%uint63) with 2| change (to_Z 4%uint63) with 4| change (to_Z 8%uint63) with 8]; lia).
  destruct (PkStepA.oracle_ILoad_mp segs OPS (chg_user segs IMGX AW OPS) (ho_acc_user _ _ _ _ _ HOPS) MP HMPA
              E st ms model w i sz sx rd rs (wlit offz) (A + to_Z offz) z v HS HMP PCB FW EC DA OI HAD
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

Theorem pkload_sound : forall pc, contract_sound segs OPS MP PB (pkload_contract segs pc).
Proof.
  intros pc st sts Hpc HAP K E ms model HS HMP HPB Hk. cbn [pkload_contract c_apply] in HAP.
  destruct (pkload_sound_main E st ms model sts HS HMP HAP) as (st' & ms' & mo' & -> & STEP & MEM & HS' & HMP').
  apply (rz_astep segs ms model ms' mo' K (op_minv_halted OPS _ (so_mf _ _ _ _ _ _ HS)) (so_svc _ _ _ _ _ _ HS) STEP).
  apply (Hk st' (or_introl eq_refl) E ms' mo'); [| exact HMP'| exact HS'].
  split; [reflexivity|]. intros k Hk'. split; reflexivity.
Qed.
End Sound2.

End PkPeek.
