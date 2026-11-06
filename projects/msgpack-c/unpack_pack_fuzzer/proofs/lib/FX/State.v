(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith Bool List Lia.
From Stdlib Require Import PrimInt63 Uint63.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase MemImageType RiscvSemantics State Run.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.FX Require Import W64 Val IMap Mem Instr.
Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import W64 Val Mem FI.
Open Scope Z_scope.
Unset Lia Cache.

Module St.

Inductive fact : Type :=
| FRange (k : int) (lo hi : w64)
| FAlign (k : int) (m : int)
| FULt (a b : sv)
| FULe (a b : sv)
| FEq (a b : sv)
| FNe (a b : sv)
| FSLt (a b : sv)
| FSLe (a b : sv).

Definition fact_holds (E : env) (f : fact) : Prop :=
  match f with
  | FRange k lo hi => w2Z lo <= bv_unsigned (ev E k) <= w2Z hi
  | FAlign k m => bv_unsigned (ev E k) mod 2 ^ (to_Z m) = 0
  | FULt a b => bv_unsigned (den E a) < bv_unsigned (den E b)
  | FULe a b => bv_unsigned (den E a) <= bv_unsigned (den E b)
  | FEq a b => den E a = den E b
  | FNe a b => den E a <> den E b
  | FSLt a b => bv_signed (den E a) < bv_signed (den E b)
  | FSLe a b => bv_signed (den E a) <= bv_signed (den E b)
  end.

Definition facts_hold (E : env) (fs : list fact) : Prop := Forall (fact_holds E) fs.

Inductive sresv : Type := RNone | RAddr (a : sv) | RUnk.

Definition resv_ok (E : env) (r : sresv) (mr : option word) : Prop :=
  match r with
  | RNone => mr = None
  | RAddr a => mr = Some (den E a)
  | RUnk => True
  end.

Record opinst := OpI { op_id : int; op_args : list sv }.

Definition oinst : Type := (int * list word)%type.

Definition cov_of (c0 : Z -> Prop) (c1 : int -> list word -> Z -> Prop) (os : list oinst) (a : Z) : Prop :=
  c0 a \/ Exists (fun o => c1 (fst o) (snd o) a) os.

Record optable := OpTable {
  op_holds : int -> list word -> (word -> option byte) -> Model -> Prop;
  op_fp : int -> list word -> list (Z * Z);
  op_frame : forall id args m m' model,
      (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (op_fp id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
      op_holds id args m model -> op_holds id args m' model;
  op_minv : Model -> Prop;
  op_cov0 : Z -> Prop;
  op_cov1 : int -> list word -> Z -> Prop;
  op_minv_halted : forall mo, op_minv mo -> m_halted mo = None;
  op_acc : forall (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
      op_minv mo ->
      Forall (fun o => op_holds (fst o) (snd o) m mo) os ->
      (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> cov_of op_cov0 op_cov1 os (bv_unsigned a + j)) ->
      exists mo', materialize_model_accesses mo acc = Some mo' /\ op_minv mo' /\
                  Forall (fun o => op_holds (fst o) (snd o) m mo') os
}.

Definition op_cov (OPS : optable) : list oinst -> Z -> Prop := cov_of (op_cov0 OPS) (op_cov1 OPS).

Lemma op_cov_mono : forall OPS os os' a, (forall o, In o os -> In o os') -> op_cov OPS os a -> op_cov OPS os' a.
Proof.
  intros OPS os os' a Sub [H|H]; [left; exact H| right].
  apply Exists_exists in H as (o & Ho & Hc). apply Exists_exists. exists o. split; [apply Sub; exact Ho| exact Hc].
Qed.

Record sstate := SS {
  s_pc : int;
  s_rf : rf sv;
  s_ff : rf sv;
  s_resv : sresv;
  s_regs : IMap.t region;
  s_facts : list fact;
  s_ops : list opinst;
  s_priv : list (int * int);
  s_next : int
}.

Definition in_priv (priv : list (int * int)) (a : Z) : Prop :=
  Exists (fun iv => to_Z (fst iv) <= a < to_Z (snd iv)) priv.
Definition in_priv_b (priv : list (int * int)) (a n : int) : bool :=

  existsb (fun iv => PrimInt63.ltb a (snd iv) && PrimInt63.ltb (fst iv) (PrimInt63.add a n)) priv.

Section WithSegs.
Variable segs : list Segment.

Definition rom_of : word -> option byte :=
  fun addr => match memory_read segs addr 1 with Some (b :: _) => Some b | _ => None end.

Definition rb (m : word -> option byte) (a : Z) : option byte :=
  match m (Z_to_bv 64 a) with
  | Some b => Some b
  | None => rom_of (Z_to_bv 64 a)
  end.

Definition wb (m : word -> option byte) (a : Z) : bool :=
  match wview segs m (Z_to_bv 64 a) with Some _ => true | None => false end.

Definition byte_of (w : word) (i : Z) : byte := Z_to_bv 8 (Z.shiftr (bv_unsigned w) (8 * i)).

Definition keyZ (i : int) : Z := Mem.keyZ i.

Definition cell_ok (E : env) (m : word -> option byte) (base : Z) (c : cell) : Prop :=
  0 <= to_Z (c_idx c) /\ 0 < to_Z (c_w c) /\ to_Z (c_idx c) + to_Z (c_w c) <= 8 /\
  forall i, 0 <= i < to_Z (c_w c) ->
    rb m (base + to_Z (c_idx c) + i) = Some (byte_of (den E (c_v c)) i).

Fixpoint slot_sorted (s : slot) : Prop :=
  match s with
  | [] => True
  | c :: s' => match s' with
               | [] => True
               | c' :: _ => to_Z (c_idx c) + to_Z (c_w c) <= to_Z (c_idx c')
               end /\ slot_sorted s'
  end.

Definition slot_ok (E : env) (m : word -> option byte) (base : Z) (s : slot) : Prop :=
  slot_sorted s /\ Forall (cell_ok E m base) s.

Definition covers (c : cell) (i : Z) : Prop := to_Z (c_idx c) <= i < to_Z (c_idx c) + to_Z (c_w c).

Definition uncovered (r : region) (o : Z) : Prop :=
  forall g gr, keyZ g = Z.div o 8 -> IMap.find g (rg_cells r) = Some gr ->
  g_dirty gr = false /\ Forall (fun c => ~ covers c (o mod 8)) (g_cells gr).

Definition img_byte (a : Z) : option byte := rom_of (Z_to_bv 64 a).

Definition bg_byte (E : env) (k : int) (r : region) (o : Z) : option byte :=
  match rg_bg r with
  | BGNone => None
  | BGZero => Some (Z_to_bv 8 0)
  | BGImage => img_byte o
  | BGUnk => Some (eg E k o)
  | BGBlob j shift => Some (nth (Z.to_nat (o - to_Z shift)) (eb E j) (Z_to_bv 8 0))
  end.

Definition hiZ (E : env) (r : region) : Z := bv_unsigned (den E (rg_hi r)).
Definition loZ (r : region) : Z := keyZ (rg_lo r).

Record region_ok (priv : list (int * int)) (E : env) (m : word -> option byte) (k : int) (r : region) : Prop := RegionOk {
  ro_bst : IMap.bst (rg_cells r);
  ro_range : PrimInt63.eqb k 0%uint63 = false ->
     0 <= bv_unsigned (ev E k) + loZ r /\ bv_unsigned (ev E k) + hiZ E r < two64;
  ro_valid : PrimInt63.eqb k 0%uint63 = false ->
     forall a, bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r ->
        rb m a <> None /\ (rg_w r = true -> wb m a = true) /\ find_segment segs a 1 = None;
  ro_cells : forall g gr, IMap.find g (rg_cells r) = Some gr ->
     slot_ok E m (bv_unsigned (ev E k) + 8 * keyZ g) (g_cells gr);
  ro_cells_in : forall g gr c i, IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) -> 0 <= i < to_Z (c_w c) ->
     let o := 8 * keyZ g + to_Z (c_idx c) + i in
     (PrimInt63.eqb k 0%uint63 = false -> loZ r <= o < hiZ E r) /\
     (PrimInt63.eqb k 0%uint63 = true ->
        0 <= o < two63 / 2 /\ (exists seg, find_segment segs o 1 = Some seg) /\ ~ in_priv priv o);
  ro_bg : forall o,
     (PrimInt63.eqb k 0%uint63 = false -> loZ r <= o < hiZ E r) ->
     (PrimInt63.eqb k 0%uint63 = true ->
        0 <= o < two63 / 2 /\ (exists bs, memory_read segs (Z_to_bv 64 o) 1 = Some bs) /\ ~ in_priv priv o) ->
     uncovered r o ->
     match bg_byte E k r o with
     | Some b => rb m (bv_unsigned (ev E k) + o) = Some b
     | None => True
     end
}.

Definition regions_disjoint (E : env) (R : IMap.t region) : Prop :=
  forall k1 r1 k2 r2, IMap.find k1 R = Some r1 -> IMap.find k2 R = Some r2 -> k1 <> k2 ->
  PrimInt63.eqb k1 0%uint63 = false -> PrimInt63.eqb k2 0%uint63 = false ->
  (rg_w r1 = true \/ rg_w r2 = true) ->
  forall a, ~ (bv_unsigned (ev E k1) + loZ r1 <= a < bv_unsigned (ev E k1) + hiZ E r1 /\
             bv_unsigned (ev E k2) + loZ r2 <= a < bv_unsigned (ev E k2) + hiZ E r2).

Definition in_based (E : env) (R : IMap.t region) (a : Z) : Prop :=
  exists k r, IMap.find k R = Some r /\ PrimInt63.eqb k 0%uint63 = false /\
    bv_unsigned (ev E k) + loZ r <= a < bv_unsigned (ev E k) + hiZ E r.

Definition abs_cells_public (priv : list (int * int)) (R : IMap.t region) : Prop :=
  forall r g gr c, IMap.find 0%uint63 R = Some r -> IMap.find g (rg_cells r) = Some gr -> In c (g_cells gr) ->
  forall i, 0 <= i < to_Z (c_w c) -> ~ in_priv priv (8 * keyZ g + to_Z (c_idx c) + i).

Definition ops_hold (OPS : optable) (E : env) (os : list opinst) (m : word -> option byte) (model : Model) : Prop :=
  Forall (fun o => op_holds OPS (op_id o) (map (den E) (op_args o)) m model) os.

Definition insts (E : env) (os : list opinst) : list oinst := map (fun o => (op_id o, map (den E) (op_args o))) os.

Lemma ops_hold_insts : forall OPS E os m model,
  ops_hold OPS E os m model <-> Forall (fun o => op_holds OPS (fst o) (snd o) m model) (insts E os).
Proof. intros. unfold ops_hold, insts. rewrite Forall_map. reflexivity. Qed.

Definition fx_acc (E : env) (R : IMap.t region) (a : Z) : Prop :=
  in_based E R a \/ (exists seg, find_segment segs a 1 = Some seg).

Lemma cover_transfer : forall OPS E E' R R' os os',
  (forall a, fx_acc E' R' a -> fx_acc E R a) ->
  (forall o, In o (insts E os) -> In o (insts E' os')) ->
  (forall a, fx_acc E R a -> op_cov OPS (insts E os) a) ->
  forall a, fx_acc E' R' a -> op_cov OPS (insts E' os') a.
Proof. intros OPS E E' R R' os os' HR HO HC a Ha. exact (op_cov_mono OPS _ _ a HO (HC a (HR a Ha))). Qed.

Lemma fx_acc_based : forall E E' R R',
  (forall a, in_based E' R' a -> in_based E R a) -> forall a, fx_acc E' R' a -> fx_acc E R a.
Proof. intros E E' R R' H a [B|S]; [left; exact (H a B)| right; exact S]. Qed.

Definition ops_apart (OPS : optable) (E : env) (os : list opinst) (R : IMap.t region) (priv : list (int * int)) : Prop :=
  Forall (fun o => forall a, Exists (fun iv => fst iv <= a < snd iv) (op_fp OPS (op_id o) (map (den E) (op_args o))) ->
                             ~ in_based E R a /\
                             ((exists seg, find_segment segs a 1 = Some seg) -> in_priv priv a)) os.

Record mfacts (model : Model) : Prop := MF {
  mf_halted : m_halted model = None;
  mf_lazy : m_vm_lazy model = []
}.

Lemma mfacts_acc : forall mo acc, mfacts mo -> materialize_model_accesses mo acc = Some mo.
Proof. intros mo acc H. apply materialize_model_accesses_no_lazy. exact (mf_lazy _ H). Qed.

Lemma plain_acc : forall (holds : int -> list word -> (word -> option byte) -> Model -> Prop)
    (os : list oinst) (m : word -> option byte) (mo : Model) (acc : list (word * nat)),
  mfacts mo -> Forall (fun o => holds (fst o) (snd o) m mo) os ->
  (forall a n j, In (a, n) acc -> 0 <= j < Z.of_nat n -> cov_of (fun _ => True) (fun _ _ _ => False) os (bv_unsigned a + j)) ->
  exists mo', materialize_model_accesses mo acc = Some mo' /\ mfacts mo' /\ Forall (fun o => holds (fst o) (snd o) m mo') os.
Proof. intros holds os m mo acc HM HO _. exists mo. split; [exact (mfacts_acc mo acc HM)|]. split; assumption. Qed.

Definition plain_optable (holds : int -> list word -> (word -> option byte) -> Model -> Prop)
    (fp : int -> list word -> list (Z * Z))
    (frame : forall id args m m' model,
      (forall a, 0 <= a < two64 -> Exists (fun iv => fst iv <= a < snd iv) (fp id args) -> m (Z_to_bv 64 a) = m' (Z_to_bv 64 a)) ->
      (forall a, 0 <= a < two64 -> m (Z_to_bv 64 a) <> None -> m' (Z_to_bv 64 a) <> None) ->
      holds id args m model -> holds id args m' model) : optable :=
  OpTable holds fp frame mfacts (fun _ => True) (fun _ _ _ => False) mf_halted (plain_acc holds).

Definition plain_table (OPS : optable) : Prop :=
  (forall mo, op_minv OPS mo <-> mfacts mo) /\ (forall a, op_cov0 OPS a).

Lemma plain_table_plain : forall holds fp frame, plain_table (plain_optable holds fp frame).
Proof. intros. split; [intros mo; reflexivity| intros a; exact I]. Qed.

Lemma plain_mf : forall OPS mo, plain_table OPS -> op_minv OPS mo -> mfacts mo.
Proof. intros OPS mo [H _] M. exact (proj1 (H mo) M). Qed.
Lemma plain_minv : forall OPS mo, plain_table OPS -> mfacts mo -> op_minv OPS mo.
Proof. intros OPS mo [H _] M. exact (proj2 (H mo) M). Qed.
Lemma plain_cover : forall OPS os a, plain_table OPS -> op_cov OPS os a.
Proof. intros OPS os a [_ H]. left. exact (H a). Qed.

Definition reg_of_r5 (r : r5) : reg := Z_to_bv 5 (r5_to_Z r).

Record st_ok (OPS : optable) (E : env) (st : sstate) (ms : machine_state) (model : Model) : Prop := StOk {
  so_pc : ms_pc_val ms = Z_to_bv 64 (to_Z (s_pc st));
  so_x0 : rf_get (s_rf st) X0 = VL wzero;
  so_regs : forall r, rget (Core (ms_regs ms) (ms_fregs ms) (ms_pc_val ms) (ms_fcsr ms) (ms_resv ms)) (reg_of_r5 r)
                      = den E (rf_get (s_rf st) r);
  so_fregs : forall r, reg_get (ms_fregs ms) (reg_of_r5 r) = den E (rf_get (s_ff st) r);
  so_svc : ms_svc_pending ms = None;
  so_resv : resv_ok E (s_resv st) (ms_resv ms);
  so_fcsr : bv_unsigned (ms_fcsr ms) < 32;
  so_rom : ms_rom ms = rom_of;
  so_zero : ev E 0%uint63 = Z_to_bv 64 0;
  so_bst : IMap.bst (s_regs st);
  so_reg : forall k r, IMap.find k (s_regs st) = Some r -> region_ok (s_priv st) E (ms_mem ms) k r;
  so_disj : regions_disjoint E (s_regs st);
  so_pub : abs_cells_public (s_priv st) (s_regs st);
  so_facts : facts_hold E (s_facts st);
  so_ops : ops_hold OPS E (s_ops st) (ms_mem ms) model;
  so_apart : ops_apart OPS E (s_ops st) (s_regs st) (s_priv st);
  so_mf : op_minv OPS model;
  so_cover : forall a, fx_acc E (s_regs st) a -> op_cov OPS (insts E (s_ops st)) a;

  so_minv : forall a b, ms_mem ms a = Some b -> forall seg, find_segment segs (bv_unsigned a) 1 = Some seg -> seg_writable seg = true
}.

End WithSegs.
End St.
