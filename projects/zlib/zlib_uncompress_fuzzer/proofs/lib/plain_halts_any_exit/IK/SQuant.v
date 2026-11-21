(* THE QUANTITY NAMES AND THE MEANING FUNCTIONS (shared: the same bytes on
   every image; edition 1 of the list form).
   A layout text of an image holds LISTS: a register map is a list of (register, quantity's NAME); the frame is
   a list of (slot name, offset from the entry stack pointer, width, quantity's NAME). THIS text gives the names
   and what a list MEANS: `rholds` ("each register of the list holds its quantity") and `fholds` ("each slot of
   the list holds its quantity"). It holds no image fact: no register, no offset, no label.
   THE NUMERAL -1 below is the value `absent` of a label that an image never reaches. *)
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import RunCtx.
From Stdlib Require Import ZArith NArith List Lia Bool String.
From LinuxProcessSemantics.EquivalenceDefinition Require Import Equivalence.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.zspec.zmodel Require Import ZIface InflateState InflateInv.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit Require Import PropExec CatExec CatSim SeqExec StoreOk ShapeAlg.
From OSSVerify.Proofs.zlib.zlib_uncompress_fuzzer.lib.plain_halts_any_exit.IK Require Import TSet ZStep ZMem ZArr ZArr4 ZRd IDefs IMem ITac ISpecs IGlue.
Import ListNotations.
Open Scope Z_scope.

(* a label that an image never reaches *)
Definition absent : Z := -1.

(* ---- THE QUANTITY NAMES: what a register or a frame slot can hold at a join point ---- *)
Inductive quant : Type :=
| Q_lit (z : Z)            (* a constant that the compiled code keeps there *)
| Q_entry (k : positive)   (* the value that register k held at the function's entry *)
| Q_u                      (* the stream's address *)
| Q_u_at (off : Z)         (* the stream's address plus a distance (the stack pointer inside the function) *)
| Q_p                      (* the state's address *)
| Q_p_at (off : Z)         (* the address of a field of the state *)
| Q_avail_in0              (* the input left at the function's entry *)
| Q_avail_in               (* the input left *)
| Q_next_in                (* the next input address *)
| Q_next_out               (* the next output address *)
| Q_avail_out              (* the output room left *)
| Q_hold                   (* the bit accumulator *)
| Q_bits                   (* the count of bits in it *)
| Q_mode                   (* the state machine's mode *)
| Q_ret                    (* the return value so far *)
| Q_out                    (* the output count at the entry of the pass *)
| Q_par                    (* the value that the join point's own statement binds *)
| Q_arg (i : nat)          (* EDITION 4: value number i (from 0) of the LIST of values that the statement binds *)
| Q_arg_at (i : nat) (off : Z).  (* EDITION 4: that value plus a distance *)

(* the value of a quantity in the model. `ost` is None at a join point whose statement has no state. *)
Definition qval (cx : ictx) (ost : option ist) (par : Z) (q : quant) : Z :=
  match q with
  | Q_lit z => z
  | Q_entry k => c_K cx k
  | Q_u => c_u cx
  | Q_u_at off => c_u cx + off
  | Q_p => c_p cx
  | Q_p_at off => c_p cx + off
  | Q_avail_in0 => c_n cx - c_cin0 cx
  | Q_avail_in => match ost with Some st => c_n cx - t_cin st | None => 0 end
  | Q_next_in => match ost with Some st => c_q cx + t_cin st | None => 0 end
  | Q_next_out => match ost with Some st => c_ob cx + t_cout st | None => 0 end
  | Q_avail_out => match ost with Some st => c_osz cx - t_cout st | None => 0 end
  | Q_hold => match ost with Some st => t_hold st | None => 0 end
  | Q_bits => match ost with Some st => t_bits st | None => 0 end
  | Q_mode => match ost with Some st => t_mode st | None => 0 end
  | Q_ret => match ost with Some st => t_ret st | None => 0 end
  | Q_out => match ost with Some st => t_out st | None => 0 end
  | Q_par => par
  | Q_arg _ => 0
  | Q_arg_at _ _ => 0
  end.

(* ---- EDITION 4: SEVERAL VALUES THAT A STATEMENT BINDS. A statement whose function has NO context record and
   no model state (it binds plain values: an address, saved register values, counts) hands its values over as
   a LIST and reads them by `qargs`: only `Q_lit`, `Q_arg` and `Q_arg_at` have a meaning there (every other
   name is 0: a layout list for such a statement holds those three only). A statement that HAS a context
   record and binds several values of its own reads everything by `qvalv`: the context's and the state's
   quantities as `qval` gives them, `Q_arg i` and `Q_arg_at i off` from the list, `Q_par` as value number 0.
   `qval` itself is unchanged for every name it had (the two new names are 0 in it). ---- *)
Definition qargs (vs : list Z) (q : quant) : Z :=
  match q with
  | Q_lit z => z
  | Q_arg i => nth i vs 0
  | Q_arg_at i off => nth i vs 0 + off
  | _ => 0
  end.

Definition qvalv (cx : ictx) (ost : option ist) (vs : list Z) (q : quant) : Z :=
  match q with
  | Q_arg i => nth i vs 0
  | Q_arg_at i off => nth i vs 0 + off
  | Q_par => nth 0 vs 0
  | _ => qval cx ost 0 q
  end.

(* ---- THE MEANING OF A REGISTER MAP: each register of the list holds its quantity ---- *)
Fixpoint rholds (ev : quant -> Z) (Rb : tree Z) (l : list (positive * Z)) (m : list (positive * quant)) : Prop :=
  match m with
  | [] => True
  | e :: m' =>
      match m' with
      | [] => zget_l Rb l (fst e) = ev (snd e)
      | _ :: _ => zget_l Rb l (fst e) = ev (snd e) /\ rholds ev Rb l m'
      end
  end.

(* ---- EDITION 2: THE MEANING OF A KEEP LIST (a list of registers, no quantities): each register of the list
   holds in the state R' what it held in the start state (Rb with its updates l). A loop lemma says with it
   which registers its body leaves alone. ---- *)
Fixpoint rkeeps (R' : tree Z) (Rb : tree Z) (l : list (positive * Z)) (ks : list positive) : Prop :=
  match ks with
  | [] => True
  | k :: ks' =>
      match ks' with
      | [] => zget R' k = zget_l Rb l k
      | _ :: _ => zget R' k = zget_l Rb l k /\ rkeeps R' Rb l ks'
      end
  end.

(* ---- THE MEANING OF A FRAME LIST: each slot of the list holds its quantity ---- *)
Inductive width : Type := W8 | W4.

(* a slot: its name, its distance from the entry stack pointer, its width, the quantity it holds *)
Definition fslot : Type := (string * Z * width * quant)%type.
Definition fs_off (s : fslot) : Z := snd (fst (fst s)).
Definition fs_width (s : fslot) : width := snd (fst s).
Definition fs_quant (s : fslot) : quant := snd s.

(* `segs` is the run's segment list: this text names no image, the base text hands its own in *)
Definition fhold1 segs (ev : quant -> Z) (M : mem) (base : Z) (s : fslot) : Prop :=
  match fs_width s with
  | W8 => mem_u64 segs M (base + fs_off s) (ev (fs_quant s))
  | W4 => mem_u32 segs M (base + fs_off s) (ev (fs_quant s))
  end.

Fixpoint fholds segs (ev : quant -> Z) (M : mem) (base : Z) (f : list fslot) : Prop :=
  match f with
  | [] => True
  | s :: f' =>
      match f' with
      | [] => fhold1 segs ev M base s
      | _ :: _ => fhold1 segs ev M base s /\ fholds segs ev M base f'
      end
  end.

(* ---- EDITION 5: THREE WORDS THAT READ A LIST BY ITS ORDER (two converters' asks). Nothing above is changed.
   `rkeys m` and `rvals ev m`: the registers and the values of a register map, each in the map's order (for a
   definition that says its register values BY POSITION). `rholdsv Rb l ks vs`: THE POSITIONAL FORM of a register
   list: a layout field that is a plain list of registers (a row of the keep kind) is read with the list of
   values that a statement binds: each register of the list holds the value at the same place; lists of
   different lengths mean False. Where one of these words reads a layout field, the ORDER of that field's rows
   is part of the field's meaning. ---- *)
Definition rkeys (m : list (positive * quant)) : list positive := map fst m.

Definition rvals (ev : quant -> Z) (m : list (positive * quant)) : list Z := map (fun e => ev (snd e)) m.

Fixpoint rholdsv (Rb : tree Z) (l : list (positive * Z)) (ks : list positive) (vs : list Z) : Prop :=
  match ks, vs with
  | [], [] => True
  | k :: ks', v :: vs' =>
      match ks' with
      | [] => match vs' with [] => zget_l Rb l k = v | _ :: _ => False end
      | _ :: _ => zget_l Rb l k = v /\ rholdsv Rb l ks' vs'
      end
  | _, _ => False
  end.
