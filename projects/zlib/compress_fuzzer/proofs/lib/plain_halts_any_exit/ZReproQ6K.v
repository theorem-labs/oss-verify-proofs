(** * ZReproQ6K — Q6 stage 3: the dynamic-table keystone, STATED.

    OWNER: model-rt lane (zlib z-repro campaign, 2026-08-19/20).  The
    per-entry table-semantics statement negotiated consumer-first over
    three rounds (an earlier development run: producibility + the it_entry form + the
    child-replication correction; an earlier development run: the op-64 fixup falsifier and
    coverage compatibility; final three-class form confirmed both sides —
    the record is DESIGN.md).  This file
    is the TEMPLATE the DISTS-variant and raw-sibling lanes queue behind:
    the statements, the one reflexivity bridge to the builder, and a
    concrete coherence control.  The PROOFS are stage 4.

    Scope notes, load-bearing:
    - Stated at [PreGo] acceptances.  The accepted-EMPTY build
      ([PreEmpty], o_ret 0 with two op-64 markers) is excluded by the
      [it_pre] hypothesis; the walk absorbs it through the op&64 dispatch
      like every other excluded entry.
    - Root-level classes are disjoint by op: POINTER [1,15], SYMBOL
      (0 or [16..] with bit 64 clear), EOB (exactly 96 = 32+64),
      EXCLUDED (bit 64 set, not 96: the it_finish fixup, PreEmpty
      markers, and the reserved-symbol lext markers 203/77).  Level-2
      entries have no pointers, so bit-64-clear suffices there.
    - Codewords are in stream order: [write_bits w (idx mod 2^w)] — the
      farm-precedent orientation (HuffIface.lb_lc_stream_bits);
      replication is quotiented by the mod, sub-tables replicate by the
      CHILD width (the round-2 correction).
    - The (op,bits,val) side is routed once through [it_entry] at the
      build's own [ItCtx] — never per-class (op,val) pairs.
    - The lens view is the LIST the declarative side owns, tied by
      [zlens]; the TABLE-chain walk supplies [lens = zlens L] when it
      instantiates this.

    TRUST BOUNDARY: pure Gallina, image-independent. *)

From Stdlib Require Import ZArith List Lia Bool.
Import ListNotations.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit.Spec.PngModel Require Import
  Base Chunk Bits BwStream ZBitsIn Huff DeflateSpec Inftrees
  InflateFast Inflate.
From OSSVerify.Proofs.zlib.compress_fuzzer.lib.plain_halts_any_exit Require Import ZReproQ6F.
Unset Lia Cache.
Unset Nia Cache.
Unset Nra Cache.
Local Open Scope Z_scope.

(* ==========================================================================
   1.  The builder's entry, as a pure function (the agreed vocabulary).
       Inftrees.v stays untouched — md5-locked to the farm.
   ========================================================================== *)

Definition it_entry (c : ItCtx) (w b : Z) : Code :=
  if Z.ltb (w + 1) (x_match c) then mkCodeT 0 b w
  else if Z.leb (x_match c) w
       then mkCodeT (x_extra c (w - x_match c)) b (x_base c (w - x_match c))
       else mkCodeT (32 + 64) b 0.

Lemma it_here_entry : forall c st,
  it_here c st = it_entry c (x_work c (s_sym st)) (s_len st - s_drop st).
Proof. reflexivity. Qed.

(* ==========================================================================
   2.  The keystone, per class.
   ========================================================================== *)

Section ZrKeystone.
  Variables (ty : Z) (L : list nat) (codes root0 : Z) (t0 : ztbl).
  Variables (c : ItCtx) (st0 : ItSt) (out : ItOut).
  Hypothesis Hpre : it_pre ty (zlens L) codes root0 t0 = PreGo c st0.
  Hypothesis Hacc : it_model ty (zlens L) codes root0 t0 = Some out.
  Hypothesis Hret : o_ret out = 0.

  (** SYMBOL: every non-pointer, non-64 root entry is the canonical
      answer for its whole fill class. *)
  Definition zrk_symbol_class : Prop :=
    forall idx, 0 <= idx < 2 ^ o_bits out ->
      let E := o_tbl out idx in
      (c_op E = 0 \/ (16 <= c_op E /\ Z.land (c_op E) 64 = 0)) ->
      1 <= c_bits E <= o_bits out
      /\ exists sym : nat,
           In (write_bits (Z.to_nat (c_bits E)) (idx mod 2 ^ c_bits E), sym)
              (code_table L 15%nat)
           /\ E = it_entry c (Z.of_nat sym) (c_bits E).

  (** EOB: op 96 uniquely identifies [it_entry]'s third arm (builder-side
      confirmed: no x_extra value is 96, the fixup is 64 exactly, pointer
      widths stop at 15), and its symbol is [x_match - 1] — 256 at LENS,
      unreachable at CODES/DISTS. *)
  Definition zrk_eob_class : Prop :=
    forall idx, 0 <= idx < 2 ^ o_bits out ->
      let E := o_tbl out idx in
      c_op E = 96 ->
      c_val E = 0
      /\ 1 <= c_bits E <= o_bits out
      /\ In (write_bits (Z.to_nat (c_bits E)) (idx mod 2 ^ c_bits E),
             Z.to_nat (x_match c - 1)) (code_table L 15%nat).

  (** POINTER: root-only; the hop window sits in the written level-2
      region ([2^root, o_used)), and every non-64 child answers with the
      combined codeword — the sub-index quotiented by the CHILD's own
      replication (round-2 correction). *)
  Definition zrk_pointer_class : Prop :=
    forall idx, 0 <= idx < 2 ^ o_bits out ->
      let E := o_tbl out idx in
      1 <= c_op E <= 15 ->
      c_bits E = o_bits out
      /\ (forall j, 0 <= j < 2 ^ c_op E ->
            let child := c_val E + j in
            2 ^ o_bits out <= child < o_used out
            /\ (let CE := o_tbl out child in
                Z.land (c_op CE) 64 = 0 ->
                1 <= c_bits CE <= c_op E
                /\ exists sym : nat,
                     In (write_bits (Z.to_nat (o_bits out + c_bits CE))
                           ((idx mod 2 ^ o_bits out)
                            + (j mod 2 ^ c_bits CE) * 2 ^ o_bits out),
                         sym) (code_table L 15%nat)
                     /\ CE = it_entry c (Z.of_nat sym) (c_bits CE))).

  Definition zr_keystone : Prop :=
    zrk_symbol_class /\ zrk_eob_class /\ zrk_pointer_class.

End ZrKeystone.

(* ==========================================================================
   3.  Coherence control: one concrete CT_CODES acceptance, its symbol
       class decided by reflection with the SAME instruments the fixed
       tables used (ZReproQ6F).  CT_CODES has no pointers and no EOB
       (x_match = 20 keeps every symbol in the literal arm), so the
       symbol class is the whole content there.  The build: four 2-bit
       codes over symbols 0..3.
   ========================================================================== *)

Definition zrk_ctl_lens : list nat := [2; 2; 2; 2]%nat.

Definition zrk_ctl_out : option ItOut :=
  it_model CT_CODES (zlens zrk_ctl_lens) 4 7 tnone.

Example zrk_ctl_accepts :
  match zrk_ctl_out with
  | Some out => (o_ret out =? 0) && (o_bits out =? 2) && (o_used out =? 4)
  | None => false
  end = true.
Proof. vm_compute. reflexivity. Qed.

(** The symbol-class checker at this build, mirroring [zrk_symbol_class]
    boolean-ly via Q6F's find; [it_entry] at the build's ctx is checked
    by direct Code equality on (op,bits,val). *)
Definition zrk_ctl_ok_at (i : nat) : bool :=
  match zrk_ctl_out, it_pre CT_CODES (zlens zrk_ctl_lens) 4 7 tnone with
  | Some out, PreGo c _ =>
      let idx := Z.of_nat i in
      let E := o_tbl out idx in
      if (c_op E =? 0) || ((16 <=? c_op E) && (Z.land (c_op E) 64 =? 0))
      then (1 <=? c_bits E) && (c_bits E <=? o_bits out)
           && match zr_tbl_find
                      (write_bits (Z.to_nat (c_bits E))
                                  (idx mod 2 ^ c_bits E))
                      (code_table zrk_ctl_lens 15%nat) with
              | Some sym =>
                  let E' := it_entry c (Z.of_nat sym) (c_bits E) in
                  (c_op E =? c_op E') && (c_bits E =? c_bits E')
                  && (c_val E =? c_val E')
              | None => false
              end
      else true
  | _, _ => false
  end.

Example zrk_ctl_symbol_class :
  forallb zrk_ctl_ok_at (seq 0 4) = true.
Proof. vm_compute. reflexivity. Qed.

(** The negative direction (the instrument is not a rubber stamp): the
    same checker at a WRONG lens list rejects — symbol 0 remapped to a
    different width breaks the codeword membership. *)
Example zrk_ctl_negative :
  (match it_model CT_CODES (zlens [1; 2; 3; 3]%nat) 4 7 tnone,
         it_pre CT_CODES (zlens [1; 2; 3; 3]%nat) 4 7 tnone with
   | Some out, PreGo c _ =>
       let E := o_tbl out 0 in
       match zr_tbl_find
               (write_bits (Z.to_nat (c_bits E)) (0 mod 2 ^ c_bits E))
               (code_table zrk_ctl_lens 15%nat) with
       | Some sym =>
           let E' := it_entry c (Z.of_nat sym) (c_bits E) in
           (c_op E =? c_op E') && (c_bits E =? c_bits E')
           && (c_val E =? c_val E')
       | None => false
       end
   | _, _ => true
   end) = false.
Proof. vm_compute. reflexivity. Qed.

Print Assumptions it_here_entry.
