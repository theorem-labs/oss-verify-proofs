(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib Require Import PropExec MState Mem Cells Exec Step Frame RegFold.
From Ltac2 Require Ltac2 Printf.
Import ListNotations.
Local Open Scope bv_scope.
Unset Lia Cache.

(* [comment removed for export] *)
Module SFM.
  Definition marker_sig : {P : Prop | P}. Proof. exists True. exact I. Qed.
  Definition marker : Prop := proj1_sig marker_sig. Definition mark : marker := proj2_sig marker_sig.
  Definition marker2_sig : {P : Prop | P}. Proof. exists True. exact I. Qed.
  Definition marker2 : Prop := proj1_sig marker2_sig. Definition mark2 : marker2 := proj2_sig marker2_sig.
End SFM.

(* [comment removed for export] *)
Lemma sf_pc_add : forall (p k t : Z), (p + k)%Z = t -> (Z_to_bv 64 p + Z_to_bv 64 k : word) = Z_to_bv 64 t.
Proof. intros p k t <-. apply lit_add_lit. Qed.
Lemma sf_btgt : forall (p : Z) (n : N) (imm : bv n) (t : Z), (p + bv_signed imm)%Z = t -> (Z_to_bv 64 p + sext 64 imm : word) = Z_to_bv 64 t.
Proof. intros p n imm t <-. rewrite b_addsext. unfold v_addi. apply unsigned_Z_to_bv_add. Qed.

(* [comment removed for export] *)
Lemma sf_addr0 : forall (x : word) (n : N) (imm : bv n), bv_signed imm = 0%Z -> (x + sext 64 imm : word) = x.
Proof. intros x n imm H. rewrite b_addsext. unfold v_addi. rewrite H, Z.add_0_r. apply Z_to_bv_lit_self. Qed.
Lemma sf_addr_off : forall (E c : Z) (n : N) (imm : bv n) (t : Z), (c + bv_signed imm)%Z = t ->
  (Z_to_bv 64 (E + c) + sext 64 imm : word) = Z_to_bv 64 (E + t).
Proof. intros E c n imm t <-. rewrite b_addsext. unfold v_addi. rewrite unsigned_Z_to_bv_add, Z.add_assoc. reflexivity. Qed.
Lemma sf_addr_off0 : forall (y : word) (c : Z) (n : N) (imm : bv n), (c + bv_signed imm)%Z = 0%Z ->
  (Z_to_bv 64 (bv_unsigned y + c) + sext 64 imm : word) = y.
Proof. intros y c n imm H. rewrite (sf_addr_off (bv_unsigned y) c n imm 0 H), Z.add_0_r. apply Z_to_bv_lit_self. Qed.
Lemma sf_addi0 : forall (x : word) (n : N) (imm : bv n), bv_signed imm = 0%Z -> alu64 ALU_ADD x (sext 64 imm) = x.
Proof. intros. rewrite alu_addi, <- b_addsext. apply sf_addr0. assumption. Qed.
Lemma sf_addi_lit : forall (e : Z) (n : N) (imm : bv n) (t : Z), (e + bv_signed imm)%Z = t ->
  alu64 ALU_ADD (Z_to_bv 64 e) (sext 64 imm) = Z_to_bv 64 t.
Proof. intros. rewrite alu_addi, <- b_addsext. apply sf_btgt. assumption. Qed.
Lemma sf_addi_off : forall (E c : Z) (n : N) (imm : bv n) (t : Z), (c + bv_signed imm)%Z = t ->
  alu64 ALU_ADD (Z_to_bv 64 (E + c)) (sext 64 imm) = Z_to_bv 64 (E + t).
Proof. intros. rewrite alu_addi, <- b_addsext. apply sf_addr_off. assumption. Qed.
Lemma sf_addi_off0 : forall (y : word) (c : Z) (n : N) (imm : bv n), (c + bv_signed imm)%Z = 0%Z ->
  alu64 ALU_ADD (Z_to_bv 64 (bv_unsigned y + c)) (sext 64 imm) = y.
Proof. intros. rewrite alu_addi, <- b_addsext. apply sf_addr_off0. assumption. Qed.
Lemma sf_lui : forall (imm : bv 20) (t : Z), Z.shiftl (bv_signed imm) 12 = t -> sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) = Z_to_bv 64 t.
Proof. intros imm t <-. apply b_lui. Qed.
Lemma sf_auipc : forall (p : Z) (imm : bv 20) (t : Z), (Z.shiftl (bv_signed imm) 12 + p)%Z = t ->
  (Z_to_bv 64 p + sext 64 (bv_concat 32 imm (Z_to_bv 12 0)) : word) = Z_to_bv 64 t.
Proof. intros p imm t <-. rewrite b_auipc. unfold v_auipc. apply unsigned_Z_to_bv_add_r. Qed.

(* [comment removed for export] *)
Definition sf_load_lhs (segs : list Segment) (m : word -> option byte) (msz : msize) (sgn : bool) (a : word) : option word :=
  match msz with
  | SZ1 => match ov_read_bytes segs m a (width_bytes 8) with Some bs => Some (if sgn then sext 64 (bv_extract 0 8 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 8 (le_bytes_to_word bs))) | None => None end
  | SZ2 => match ov_read_bytes segs m a (width_bytes 16) with Some bs => Some (if sgn then sext 64 (bv_extract 0 16 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 16 (le_bytes_to_word bs))) | None => None end
  | SZ4 => match ov_read_bytes segs m a (width_bytes 32) with Some bs => Some (if sgn then sext 64 (bv_extract 0 32 (le_bytes_to_word bs)) else zext 64 (bv_extract 0 32 (le_bytes_to_word bs))) | None => None end
  | SZ8 => match ov_read_bytes segs m a (width_bytes 64) with Some bs => Some (bv_extract 0 64 (le_bytes_to_word bs)) | None => None end
  end.
Definition sf_store_lhs (msz : msize) (x : word) : list byte :=
  match msz with
  | SZ1 => Z_to_le_bytes (width_bytes 8) (bv_unsigned (bv_extract 0 8 x))
  | SZ2 => Z_to_le_bytes (width_bytes 16) (bv_unsigned (bv_extract 0 16 x))
  | SZ4 => Z_to_le_bytes (width_bytes 32) (bv_unsigned (low32 x))
  | SZ8 => Z_to_le_bytes (width_bytes 64) (bv_unsigned x)
  end.
Definition sf_store_n (msz : msize) : nat :=
  match msz with SZ1 => width_bytes 8 | SZ2 => width_bytes 16 | SZ4 => width_bytes 32 | SZ8 => width_bytes 64 end.

(* [comment removed for export] *)
Ltac step2_with_old rp rpm vh :=
  lazymatch goal with
  | |- evt ?segs ?Q (MS ?R ?F (Z_to_bv 64 ?pc) ?fc ?rv ?m ?ro) => step2_core segs Q R F pc fc rv m ro rp rpm vh
  | |- evt _ _ (MS _ _ ?pc _ _ _ _) => fail "pc is not a literal:" pc
  end.
Ltac step2_fast_old := step2_with_old ltac:(idtac) ltac:(vnorm_tail) ltac:(idtac).

(* [comment removed for export] *)
Module SF.
Import Ltac2.Ltac2 Ltac2.Printf.

Ltac2 Type exn ::= [ SF_Captured ((constr * (ident * constr option * constr) list) list) | SF_Mismatch ].

Ltac2 mutable sf_mode : int := 1.
Ltac2 mutable sf_debug : bool := false.
Ltac2 mutable sf_timing : bool := false.
Ltac2 mutable sf_fastpaths : bool := true.
(* [comment removed for export] *)
Ltac2 mutable sf_scan_depth : int := 1000.
Ltac2 mutable sf_scan_budget : int := 1000000.

Ltac2 sf_fail (s : string) := Control.zero (Tactic_failure (Some (Message.of_string s))).
Ltac2 tm (s : string) (f : unit -> 'a) : 'a := if sf_timing then Control.time (Some s) f else f ().

(* [comment removed for export] *)
Ltac2 mk_app (f : constr) (a : constr array) : constr := Constr.Unsafe.make (Constr.Unsafe.App f a).
Ltac2 gref (r : Std.reference) : constr := Env.instantiate r.
Ltac2 rec strip_cast (c : constr) : constr :=
  match Constr.Unsafe.kind c with Constr.Unsafe.Cast c' _ _ => strip_cast c' | _ => c end.

Ltac2 is_const (r : Std.reference) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constant k _ => match r with Std.ConstRef k' => Constant.equal k k' | _ => false end
  | _ => false
  end.
Ltac2 is_ctor (r : Std.reference) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Constructor k _ => match r with Std.ConstructRef k' => Constructor.equal k k' | _ => false end
  | _ => false
  end.

(* [comment removed for export] *)
Ltac2 rec pos_int (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        match pos_int (Array.get args 0) with
        | Some n =>
            if Int.gt n 1152921504606846976 then None
            else if is_ctor reference:(xO) f then Some (Int.mul 2 n)
            else if is_ctor reference:(xI) f then Some (Int.add (Int.mul 2 n) 1)
            else None
        | None => None
        end
      else None
  | _ => if is_ctor reference:(xH) c then Some 1 else None
  end.
Ltac2 z_int (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then
        match pos_int (Array.get args 0) with
        | Some n => if is_ctor reference:(Zpos) f then Some n else if is_ctor reference:(Zneg) f then Some (Int.sub 0 n) else None
        | None => None
        end
      else None
  | _ => if is_ctor reference:(Z0) c then Some 0 else None
  end.
Ltac2 rec int_pos (n : int) : constr :=
  if Int.le n 1 then gref reference:(xH)
  else if Int.equal (Int.mod n 2) 0 then mk_app (gref reference:(xO)) [| int_pos (Int.div n 2) |]
  else mk_app (gref reference:(xI)) [| int_pos (Int.div n 2) |].
Ltac2 int_z (n : int) : constr :=
  if Int.equal n 0 then gref reference:(Z0)
  else if Int.lt 0 n then mk_app (gref reference:(Zpos)) [| int_pos n |]
  else mk_app (gref reference:(Zneg)) [| int_pos (Int.sub 0 n) |].

(* [comment removed for export] *)
Ltac2 bv_lit (c : constr) : (constr * int) option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 3 then
        if is_ctor reference:(BV) f then
          match z_int (Array.get args 1) with Some z => Some (Array.get args 0, z) | None => None end
        else None
      else None
  | _ => None
  end.
Ltac2 n_int (c : constr) : int option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args =>
      if Int.equal (Array.length args) 1 then (if is_ctor reference:(Npos) f then pos_int (Array.get args 0) else None) else None
  | _ => if is_ctor reference:(N0) c then Some 0 else None
  end.
Ltac2 rec ipow2 (k : int) : int := if Int.le k 0 then 1 else Int.mul 2 (ipow2 (Int.sub k 1)).
(* [comment removed for export] *)
Ltac2 imm_signed (imm : constr) : int option :=
  match bv_lit imm with
  | Some (n, z) =>
      match n_int n with
      | Some w =>
          if Int.gt w 32 then None else if Int.lt w 1 then None
          else if Int.lt z 0 then None else if Int.ge z (ipow2 w) then None
          else if Int.ge z (ipow2 (Int.sub w 1)) then Some (Int.sub z (ipow2 w)) else Some z
      | None => None
      end
  | None => None
  end.
(* [comment removed for export] *)
Ltac2 reg_int (r : constr) : int :=
  match bv_lit r with
  | Some (_, z) => if Int.lt z 0 then sf_fail "reg" else if Int.gt z 31 then sf_fail "reg" else z
  | None => sf_fail "reg literal"
  end.

(* [comment removed for export] *)
Ltac2 bi_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := true; Std.rMatch := true; Std.rFix := true; Std.rCofix := true;
    Std.rZeta := false; Std.rDelta := false; Std.rConst := [] }.
Ltac2 no_flags () : Std.red_flags :=
  { Std.rStrength := Std.Norm; Std.rBeta := false; Std.rMatch := false; Std.rFix := false; Std.rCofix := false;
    Std.rZeta := false; Std.rDelta := false; Std.rConst := [] }.
Ltac2 bi (c : constr) : constr :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var _ => c
  | _ => Std.eval_cbv (bi_flags ()) c
  end.

(* [comment removed for export] *)
Ltac2 prove (gty : constr) (tac : unit -> unit) : constr :=
  strip_cast '(ltac2:(tac ()) : $gty).
Ltac2 goal_eq_lhs () : constr :=
  match Constr.Unsafe.kind (Control.goal ()) with
  | Constr.Unsafe.App _ args => if Int.equal (Array.length args) 3 then Array.get args 1 else sf_fail "small goal shape"
  | _ => sf_fail "small goal shape"
  end.
(* [comment removed for export] *)
Ltac2 small_eq_gen (ty : constr) (lhs : constr) (rhs : constr) (pass : unit -> unit) : constr * constr :=
  let gty := mk_app (gref reference:(eq)) [| ty; lhs; rhs |] in
  let cap := { contents := lhs } in
  let prf := prove gty (fun () => pass (); cap.(contents) := goal_eq_lhs (); Std.reflexivity ()) in
  (cap.(contents), prf).
Ltac2 small_eq (ty : constr) (lhs : constr) (pass : unit -> unit) : constr * constr :=
  let ev := strip_cast open_constr:(_ : $ty) in
  small_eq_gen ty lhs ev pass.


(* [comment removed for export] *)
Ltac2 kof (r : Std.reference) : constant :=
  match r with Std.ConstRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "kof"))) end.
Ltac2 kset (l : Std.reference list) : constant FSet.t :=
  List.fold_left (fun s r => FSet.add (kof r) s) (FSet.empty FSet.Tags.constant_tag) l.

Ltac2 Type det := {
  dv : bool ref; dz : bool ref; budget : int ref; hitd : int ref;
  trig : constant FSet.t;     (* [comment removed for export] *)
  un_v : constant FSet.t;     (* [comment removed for export] *)
  un_z : constant FSet.t;     (* [comment removed for export] *)
  cnd : constant FSet.t;      (* [comment removed for export] *)
  k_add : constant; k_sub : constant; k_mul : constant; k_shl : constant; k_shr : constant; k_land : constant; k_lor : constant;
  k_lxor : constant; k_mod : constant; k_pow : constant; k_unsigned : constant; k_signed : constant; k_swrap : constant;
  k_wrap : constant; k_ztobv : constant; k_bvadd : constant; k_bvand : constant; k_bvnot : constant; k_retpc : constant;
  k_concat : constant; c_zpos : constructor; c_zneg : constructor; c_z0 : constructor; n64 : constr;
  nums : constructor FSet.t;   (* [comment removed for export] *)
  k_bvset : constant; k_regget : constant; dr : bool ref }.

Ltac2 cof (r : Std.reference) : constructor :=
  match r with Std.ConstructRef k => k | _ => Control.throw (Tactic_failure (Some (Message.of_string "cof"))) end.
Ltac2 mk_det0 (n64 : constr) (b : int) (uv : constant FSet.t) (uz : constant FSet.t) (cn : constant FSet.t) : det := {
  dv := { contents := false }; dz := { contents := false }; budget := { contents := b }; hitd := { contents := 0 };
  trig := FSet.union uv (FSet.union uz cn);
  un_v := uv; un_z := uz; cnd := cn;
  k_add := kof reference:(Z.add); k_sub := kof reference:(Z.sub); k_mul := kof reference:(Z.mul); k_shl := kof reference:(Z.shiftl);
  k_shr := kof reference:(Z.shiftr); k_land := kof reference:(Z.land); k_lor := kof reference:(Z.lor); k_lxor := kof reference:(Z.lxor);
  k_mod := kof reference:(Z.modulo); k_pow := kof reference:(Z.pow); k_unsigned := kof reference:(bv_unsigned);
  k_signed := kof reference:(bv_signed); k_swrap := kof reference:(bv_swrap); k_wrap := kof reference:(bv_wrap);
  k_ztobv := kof reference:(Z_to_bv); k_bvadd := kof reference:(bv_add); k_bvand := kof reference:(bv_and);
  k_bvnot := kof reference:(bv_not); k_retpc := kof reference:(ret_pc); k_concat := kof reference:(bv_concat);
  c_zpos := cof reference:(Zpos); c_zneg := cof reference:(Zneg); c_z0 := cof reference:(Z0); n64 := n64;
  nums := List.fold_left (fun s r => FSet.add (cof r) s) (FSet.empty FSet.Tags.constructor_tag)
            [reference:(xO); reference:(xI); reference:(Zpos); reference:(Zneg); reference:(Npos); reference:(BV)];
  k_bvset := kof reference:(bvmap_set); k_regget := kof reference:(reg_get); dr := { contents := false } }.
Ltac2 mk_det (n64 : constr) (b : int) : det :=
  mk_det0 n64 b
    (kset [reference:(w0); reference:(w1); reference:(btgt);
     reference:(v_addi); reference:(v_add); reference:(v_sub); reference:(v_mul); reference:(v_andi); reference:(v_ori); reference:(v_xori);
     reference:(v_and); reference:(v_or); reference:(v_xor); reference:(v_slli); reference:(v_srli); reference:(v_srai); reference:(v_sll);
     reference:(v_srl); reference:(v_sra); reference:(v_lui); reference:(v_auipc); reference:(v_addiw); reference:(v_slliw);
     reference:(v_srliw); reference:(v_sraiw); reference:(v_addw); reference:(v_subw); reference:(v_sllw); reference:(v_srlw);
     reference:(v_sraw); reference:(v_mulh); reference:(v_mulhsu); reference:(v_mulhu); reference:(v_mulw)])
    (kset [reference:(v_sltu); reference:(v_slt); reference:(v_sltiu); reference:(v_slti); reference:(zxb)])
    (kset [reference:(Z.add); reference:(Z.sub); reference:(Z.mul); reference:(Z.shiftl); reference:(Z.shiftr); reference:(Z.land);
     reference:(Z.lor); reference:(Z.lxor); reference:(Z.modulo); reference:(Z.pow); reference:(bv_unsigned); reference:(bv_signed);
     reference:(bv_swrap); reference:(bv_wrap); reference:(Z_to_bv); reference:(bv_add); reference:(bv_and); reference:(ret_pc)]).


(* [comment removed for export] *)
Ltac2 head_is (k : constant) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constant k' _ => Constant.equal k k' | _ => false end)
  | Constr.Unsafe.Constant k' _ => Constant.equal k k'
  | _ => false
  end.
Ltac2 head_ctor (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constructor _ _ => true | _ => false end)
  | Constr.Unsafe.Constructor _ _ => true
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 zlit_head (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => if is_ctor reference:(Zpos) f then true else is_ctor reference:(Zneg) f
  | _ => is_ctor reference:(Z0) c
  end.
Ltac2 rec pos_depth_gt (n : int) (p : constr) : bool :=
  match Constr.Unsafe.kind p with
  | Constr.Unsafe.App _ args =>
      if Int.le n 0 then true
      else if Int.equal (Array.length args) 1 then pos_depth_gt (Int.sub n 1) (Array.get args 0) else false
  | _ => false
  end.
Ltac2 big_zlit (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f args => if is_ctor reference:(Zpos) f then pos_depth_gt 63 (Array.get args 0) else false
  | _ => false
  end.
Ltac2 is_64 (c : constr) : bool := match n_int c with Some w => Int.equal w 64 | None => false end.
Ltac2 arg_of (c : constr) (j : int) : constr option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App _ a => if Int.lt j (Array.length a) then Some (Array.get a j) else None
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 zl (x : det) (c : constr) : bool :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ =>
      (match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constructor k _ => if Constructor.equal k (x.(c_zpos)) then true else Constructor.equal k (x.(c_zneg))
       | _ => false
       end)
  | Constr.Unsafe.Constructor k _ => Constructor.equal k (x.(c_z0))
  | _ => false
  end.
(* [comment removed for export] *)
Ltac2 hk (c : constr) : constant option :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f _ => (match Constr.Unsafe.kind f with Constr.Unsafe.Constant k _ => Some k | _ => None end)
  | _ => None
  end.

(* [comment removed for export] *)
Ltac2 cond_hit (x : det) (k : constant) (a : constr array) : unit :=
  let n := Array.length a in
  let setv () := (x.(dv)).(contents) := true in
  let setz () := (x.(dz)).(contents) := true in
  let both () := setv (); setz () in
  let lit2 () := if Int.equal n 2 then (if zl x (Array.get a 1) then zl x (Array.get a 0) else false) else false in
  if Constant.equal k (x.(k_ztobv)) then
    (if Int.equal n 2 then
       match hk (Array.get a 1) with
       | Some ke =>
           if Constr.equal (Array.get a 0) (x.(n64)) then
             (if Constant.equal ke (x.(k_unsigned)) then setv ()
              else if Constant.equal ke (x.(k_mod)) then setz ()
              else if Constant.equal ke (x.(k_add)) then
                match arg_of (Array.get a 1) 1 with Some b => (if is_ctor reference:(Z0) b then setv () else ()) | None => () end
              else ())
           else ()
       | None => ()
       end
     else ())
  else if Constant.equal k (x.(k_add)) then
    (if Int.equal n 2 then
       (if zl x (Array.get a 1) then
          (if zl x (Array.get a 0) then setv ()
           else match hk (Array.get a 0) with
                | Some ka => if Constant.equal ka (x.(k_add)) then
                               (match arg_of (Array.get a 0) 1 with Some b => if zl x b then setv () else () | None => () end) else ()
                | None => ()
                end)
        else ())
     else ())
  else if Constant.equal k (x.(k_unsigned)) then
    (if Int.equal n 2 then
       (let b := Array.get a 1 in
        match Constr.Unsafe.kind b with
        | Constr.Unsafe.Var _ => ()
        | _ =>
          if head_ctor b then setv ()
          else if head_is (x.(k_concat)) b then setv ()
          else if head_is (x.(k_ztobv)) b then
            (* [comment removed for export] *)
            (match arg_of b 0, arg_of b 1 with
             | Some w, Some e => if Constr.equal w (x.(n64)) then both () else (if zl x e then setv () else ())
             | _, _ => ()
             end)
          else ()
        end)
     else ())
  else if Constant.equal k (x.(k_signed)) then
    (if Int.equal n 2 then
       (let b := Array.get a 1 in
        if head_ctor b then setv ()
        else if head_is (x.(k_concat)) b then setv ()
        else if head_is (x.(k_ztobv)) b then (match arg_of b 1 with Some e => if zl x e then setv () else () | None => () end)
        else ())
     else ())
  else if Constant.equal k (x.(k_sub)) then (if lit2 () then both () else ())
  else if Constant.equal k (x.(k_mul)) then (if lit2 () then setv () else ())
  else if Constant.equal k (x.(k_shl)) then (if lit2 () then both () else ())
  else if Constant.equal k (x.(k_shr)) then
    ((if lit2 () then both () else ());
     (* [comment removed for export] *)
     (if Int.equal n 2 then
        (let b := Array.get a 0 in
         if head_is (x.(k_mod)) b then setz () else if head_is (x.(k_land)) b then setz () else ())
      else ()))
  else if Constant.equal k (x.(k_land)) then (if lit2 () then both () else ())
  else if Constant.equal k (x.(k_lor)) then (if lit2 () then both () else ())
  else if Constant.equal k (x.(k_lxor)) then (if lit2 () then both () else ())
  else if Constant.equal k (x.(k_mod)) then
    (if Int.equal n 2 then (if zl x (Array.get a 1) then (if zl x (Array.get a 0) then setz () else
                               (* [comment removed for export] *)
                               match z_int (Array.get a 1) with Some v => if Int.equal v 64 then setz () else () | None => () end) else ()) else ())
  else if Constant.equal k (x.(k_pow)) then (if lit2 () then setz () else ())
  else if Constant.equal k (x.(k_swrap)) then (if Int.equal n 2 then (if zl x (Array.get a 1) then setv () else ()) else ())
  else if Constant.equal k (x.(k_wrap)) then (if Int.equal n 2 then (if zl x (Array.get a 1) then both () else ()) else ())
  else if Constant.equal k (x.(k_bvadd)) then
    (if Int.equal n 3 then (if head_is (x.(k_ztobv)) (Array.get a 1) then (if head_is (x.(k_ztobv)) (Array.get a 2) then setv () else ()) else ()) else ())
  else if Constant.equal k (x.(k_bvand)) then
    (if Int.equal n 3 then (if head_is (x.(k_bvnot)) (Array.get a 2) then setv () else ()) else ())
  else if Constant.equal k (x.(k_retpc)) then
    (if Int.equal n 1 then
       (let b := Array.get a 0 in
        if head_is (x.(k_ztobv)) b then (match arg_of b 1 with Some e => if zl x e then setv () else () | None => () end) else ())
     else ())
  else ().

(* [comment removed for export] *)
Ltac2 clean_shape (x : det) (t : constr) : bool :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var _ => true
  | Constr.Unsafe.App h a =>
      if Int.equal (Array.length a) 2 then
        match Constr.Unsafe.kind h with
        | Constr.Unsafe.Constant k _ =>
            if Constant.equal k (x.(k_ztobv)) then
              if Constr.equal (Array.get a 0) (x.(n64)) then
                (let e := Array.get a 1 in
                 match Constr.Unsafe.kind e with
                 | Constr.Unsafe.App he b =>
                     (match Constr.Unsafe.kind he with
                      | Constr.Unsafe.Constructor _ _ => Int.equal (Array.length b) 1        (* [comment removed for export] *)
                      | Constr.Unsafe.Constant ke _ =>
                          if Constant.equal ke (x.(k_add)) then
                            if Int.equal (Array.length b) 2 then
                              (match Constr.Unsafe.kind (Array.get b 1) with
                               | Constr.Unsafe.App hc _ =>
                                   (match Constr.Unsafe.kind hc with
                                    | Constr.Unsafe.Constructor _ _ =>
                                        (match Constr.Unsafe.kind (Array.get b 0) with
                                         | Constr.Unsafe.App hu u =>
                                             if Int.equal (Array.length u) 2 then
                                               (match Constr.Unsafe.kind hu with
                                                | Constr.Unsafe.Constant ku _ =>
                                                    if Constant.equal ku (x.(k_unsigned)) then
                                                      (match Constr.Unsafe.kind (Array.get u 1) with Constr.Unsafe.Var _ => true | _ => false end)
                                                    else false
                                                | _ => false
                                                end)
                                             else false
                                         | _ => false
                                         end)
                                    | _ => false
                                    end)
                               | _ => false
                               end)
                            else false
                          else false
                      | _ => false
                      end)
                 | Constr.Unsafe.Constructor _ _ => true      (* [comment removed for export] *)
                 | _ => false
                 end)
              else false
            else false
        | _ => false
        end
      else false
  | _ => false
  end.

Ltac2 rec scan (x : det) (d : int) (c : constr) : unit :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var _ => ()
  | Constr.Unsafe.Rel _ => ()
  | Constr.Unsafe.App f a =>
      let b := (x.(budget)).(contents) in
      if Int.le b 0 then () else if Int.le d 0 then () else
      ((x.(budget)).(contents) := Int.sub b 1;
       match Constr.Unsafe.kind f with
       | Constr.Unsafe.Constant k _ =>
           (if Constant.equal k (x.(k_bvset)) then (x.(dr)).(contents) := true
            else if Constant.equal k (x.(k_regget)) then (x.(dr)).(contents) := true else ());
           (if FSet.mem k (x.(trig)) then
              (let was := if (x.(dv)).(contents) then true else (x.(dz)).(contents) in
               (if FSet.mem k (x.(cnd)) then cond_hit x k a
                else if FSet.mem k (x.(un_v)) then (x.(dv)).(contents) := true
                else (x.(dz)).(contents) := true);
               if was then () else (if (if (x.(dv)).(contents) then true else (x.(dz)).(contents)) then (x.(hitd)).(contents) := d else ()))
            else ());
           scan_args x (Int.sub d 1) a 0
       | Constr.Unsafe.Constructor kc _ =>
           (* [comment removed for export] *)
           if FSet.mem kc (x.(nums)) then () else scan_args x (Int.sub d 1) a 0
       (* [comment removed for export] *)
       | Constr.Unsafe.Lambda _ _ => (x.(dv)).(contents) := true; (x.(dz)).(contents) := true
       | Constr.Unsafe.Fix _ _ _ _ => (x.(dv)).(contents) := true; (x.(dz)).(contents) := true
       | _ => scan x (Int.sub d 1) f; scan_args x (Int.sub d 1) a 0
       end)
  | Constr.Unsafe.Constant k _ =>
      if FSet.mem k (x.(trig)) then
        (if FSet.mem k (x.(un_v)) then (x.(dv)).(contents) := true
         else if FSet.mem k (x.(un_z)) then (x.(dz)).(contents) := true else ())
      else ()
  | Constr.Unsafe.Lambda _ b => scan x (Int.sub d 1) b
  | Constr.Unsafe.Prod b t => scan x (Int.sub d 1) (Constr.Binder.type b); scan x (Int.sub d 1) t
  | Constr.Unsafe.LetIn _ v b => scan x (Int.sub d 1) v; scan x (Int.sub d 1) b
  | Constr.Unsafe.Case _ _ _ scr brs =>
      (if head_ctor scr then ((x.(dv)).(contents) := true; (x.(dz)).(contents) := true) else ());     (* [comment removed for export] *)
      scan x (Int.sub d 1) scr; scan_args x (Int.sub d 1) brs 0
  | Constr.Unsafe.Proj _ _ b => (if head_ctor b then ((x.(dv)).(contents) := true; (x.(dz)).(contents) := true) else ()); scan x (Int.sub d 1) b
  | Constr.Unsafe.Cast b _ _ => scan x d b
  | _ => ()
  end
with scan_args (x : det) (d : int) (a : constr array) (j : int) : unit :=
  if Int.lt j (Array.length a) then (scan x d (Array.get a j); scan_args x d a (Int.add j 1)) else ().

(* [comment removed for export] *)
Ltac2 rec scan_fchain (x : det) (d : int) (prev : int) (f : constr) : unit :=
  match Constr.Unsafe.kind f with
  | Constr.Unsafe.App h a =>
      if (if Int.equal (Array.length a) 5 then is_const reference:(bvmap_set) h else false) then
        ((match bv_lit (Array.get a 2) with
          | Some (_, k) => if Int.lt prev k then scan_fchain x d k (Array.get a 4) else (x.(dr)).(contents) := true
          | None => (x.(dr)).(contents) := true
          end);
         scan x d (Array.get a 3))
      else scan x d f
  | _ => scan x d f
  end.

Ltac2 rec count (c : constr) : int :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.App f a => Array.fold_left (fun n t => Int.add n (count t)) (Int.add 1 (count f)) a
  | Constr.Unsafe.Lambda _ b => Int.add 1 (count b)
  | Constr.Unsafe.Case _ _ _ scr brs => Array.fold_left (fun n t => Int.add n (count t)) (Int.add 1 (count scr)) brs
  | _ => 1
  end.
(* [comment removed for export] *)
(* [comment removed for export] *)
Ltac2 Type opts := { z : bool; known : bool; rp : Ltac1.t; rpm : Ltac1.t; vh : Ltac1.t }.

Ltac2 run_frm () : unit := ltac1:(stepL_frm).
Ltac2 run_zsimp () : unit := ltac1:(zsimp).
Ltac2 run_vtail () : unit := ltac1:(vnorm_tail).
Ltac2 run_bi () : unit := ltac1:(cbv_concl_beta_iota).

(* [comment removed for export] *)
Ltac2 Type small := { bi_ : bool; vt : bool; zs : bool }.
Ltac2 after_small (sm : small) (is_load : bool) : unit :=
  (if sm.(bi_) then run_bi () else ());
  (if is_load then (if sm.(vt) then run_vtail () else ()) else ());
  (if sm.(zs) then run_zsimp () else ()).

(* [comment removed for export] *)
Ltac2 val_pass (o : opts) (sm : small) (i : constr) (s : constr) : unit :=
  let iv := Ltac1.of_constr i in
  let sv := Ltac1.of_constr s in
  ltac1:(i S vh |- stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S; vh) iv sv (o.(vh));
  after_small sm false.
(* [comment removed for export] *)
Ltac2 addr_pass (i : constr) (s : constr) : unit :=
  let iv := Ltac1.of_constr i in
  let sv := Ltac1.of_constr s in
  ltac1:(i S |- stepL_frm; vnorm_rw_for i; vnorm_tail_ctx S) iv sv.
(* [comment removed for export] *)
Ltac2 load_pass (o : opts) (sm : small) : unit :=
  ltac1:(vh |- stepL_frm; solve_load; cbv_concl_beta_iota; load_post; vh) (o.(vh));
  after_small sm true.
Ltac2 bytes_pass (o : opts) (s : constr) : unit :=
  let sv := Ltac1.of_constr s in
  ltac1:(S vh |- stepL_frm; vnorm_tail_ctx S; rewrite ?store_bytes_8', ?store_bytes_4', ?store_bytes_2', ?store_bytes_1'; vh) sv (o.(vh)).

Ltac2 word_ty () : constr := '(bv 64).

(* [comment removed for export] *)
Ltac2 Type regfile := [ Folded (constr, constr array) | Raw (constr) ].

Ltac2 rec int_path (p : int) : bool list :=
  if Int.le p 1 then [] else (Int.equal (Int.mod p 2) 1) :: int_path (Int.div p 2).
Ltac2 tnode_args (t : constr) : constr array :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App h a => if Int.equal (Array.length a) 4 then (if is_ctor reference:(TNode) h then a else sf_fail "raw tree") else sf_fail "raw tree"
  | _ => sf_fail "raw tree"
  end.
Ltac2 some_arg (o : constr) : constr :=
  match Constr.Unsafe.kind o with
  | Constr.Unsafe.App h a => if Int.equal (Array.length a) 2 then (if is_ctor reference:(Some) h then Array.get a 1 else sf_fail "raw tree slot") else sf_fail "raw tree slot"
  | _ => sf_fail "raw tree slot"
  end.
Ltac2 rec tree_get (path : bool list) (t : constr) : constr :=
  let a := tnode_args t in
  match path with
  | [] => some_arg (Array.get a 2)
  | b :: path' => tree_get path' (Array.get a (if b then 3 else 1))
  end.
Ltac2 rec tree_set (path : bool list) (v : constr) (t : constr) : constr :=
  let a := tnode_args t in
  let h := match Constr.Unsafe.kind t with Constr.Unsafe.App h _ => h | _ => sf_fail "raw tree" end in
  match path with
  | [] =>
      let o := Array.get a 2 in
      let (hs, ty) := match Constr.Unsafe.kind o with
                      | Constr.Unsafe.App hs b => if Int.equal (Array.length b) 2 then (hs, Array.get b 0) else sf_fail "raw tree slot"
                      | _ => sf_fail "raw tree slot"
                      end in
      (if is_ctor reference:(Some) hs then () else sf_fail "raw tree slot");
      mk_app h [| Array.get a 0; Array.get a 1; mk_app hs [| ty; v |]; Array.get a 3 |]
  | b :: path' =>
      if b then mk_app h [| Array.get a 0; Array.get a 1; Array.get a 2; tree_set path' v (Array.get a 3) |]
      else mk_app h [| Array.get a 0; tree_set path' v (Array.get a 1); Array.get a 2; Array.get a 3 |]
  end.
Ltac2 rec tree_iter (f : constr -> unit) (skip : bool list option) (t : constr) : unit :=
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.App _ a =>
      if Int.equal (Array.length a) 4 then
        ((match skip with
          | Some [] => ()
          | _ => (match Constr.Unsafe.kind (Array.get a 2) with
                  | Constr.Unsafe.App _ b => if Int.equal (Array.length b) 2 then f (Array.get b 1) else ()
                  | _ => ()
                  end)
          end);
         tree_iter f (match skip with Some (false :: p) => Some p | _ => None end) (Array.get a 1);
         tree_iter f (match skip with Some (true :: p) => Some p | _ => None end) (Array.get a 3))
      else ()
  | _ => ()
  end.

Ltac2 regfile_of (r : constr) : regfile :=
  match Constr.Unsafe.kind r with
  | Constr.Unsafe.App h a =>
      if Int.equal (Array.length a) 31 then (if is_const reference:(mkR) h then Folded h a else sf_fail "register file")
      else if Int.equal (Array.length a) 4 then (if is_ctor reference:(TNode) h then Raw r else sf_fail "register file")
      else ((if sf_debug then printf "SF-REGFILE head %t nargs %i" h (Array.length a) else ()); sf_fail "register file")
  | _ => (if sf_debug then printf "SF-REGFILE %t" r else ()); sf_fail "register file"
  end.
Ltac2 rf_get (rf : regfile) (k : int) : constr :=
  match rf with
  | Folded _ a => Array.get a (Int.sub k 1)
  | Raw t => tree_get (int_path (Int.add k 1)) t
  end.
Ltac2 rf_set (rf : regfile) (k : int) (v : constr) : constr :=
  match rf with
  | Folded h a => let a' := Array.copy a in Array.set a' (Int.sub k 1) v; mk_app h a'
  | Raw t => tree_set (int_path (Int.add k 1)) v t
  end.
(* [comment removed for export] *)
Ltac2 rf_iter (rf : regfile) (skip : int) (f : constr -> unit) : unit :=
  match rf with
  | Folded _ a => Array.iteri (fun j t => if Int.equal (Int.add j 1) skip then () else f t) a
  | Raw t => tree_iter f (if Int.equal skip 0 then None else Some (int_path (Int.add skip 1))) t
  end.
Ltac2 rf_is_raw (rf : regfile) : bool := match rf with Raw _ => true | _ => false end.

(* [comment removed for export] *)
Ltac2 operand (rf : regfile) (rs : constr) : constr :=
  let k := reg_int rs in
  if Int.equal k 0 then '(w0) else bi (rf_get rf k).

(* [comment removed for export] *)
Ltac2 Type shape := [ SVar (constr) | SLit (int) | SOff (constr, constr, constr, int) | SOther ].
Ltac2 small_int (v : int) : bool := if Int.lt v 1152921504606846976 then Int.gt v (Int.sub 0 1152921504606846976) else false.
Ltac2 shape_of (is_w0 : bool) (t : constr) : shape :=
  if is_w0 then SLit 0 else
  match Constr.Unsafe.kind t with
  | Constr.Unsafe.Var _ => SVar t
  | Constr.Unsafe.App h a =>
      if Int.equal (Array.length a) 2 then
        if is_const reference:(Z_to_bv) h then
          if is_64 (Array.get a 0) then
            let e := Array.get a 1 in
            match z_int e with
            | Some v => if small_int v then SLit v else SOther
            | None =>
                match Constr.Unsafe.kind e with
                | Constr.Unsafe.App he b =>
                    if Int.equal (Array.length b) 2 then
                      if is_const reference:(Z.add) he then
                        match z_int (Array.get b 1) with
                        | Some c =>
                            if small_int c then
                              (let ee := Array.get b 0 in
                               match Constr.Unsafe.kind ee with
                               | Constr.Unsafe.App hu u =>
                                   if Int.equal (Array.length u) 2 then
                                     if is_const reference:(bv_unsigned) hu then
                                       if is_64 (Array.get u 0) then
                                         (match Constr.Unsafe.kind (Array.get u 1) with
                                          | Constr.Unsafe.Var _ => SOff ee (Array.get u 1) (Array.get b 1) c
                                          | _ => SOther
                                          end)
                                       else SOther
                                     else SOther
                                   else SOther
                               | _ => SOther
                               end)
                            else SOther
                        | None => SOther
                        end
                      else SOther
                    else SOther
                | _ => SOther
                end
            end
          else SOther
        else SOther
      else SOther
  | _ => SOther
  end.

Ltac2 operand_shape (rf : regfile) (rs : constr) : constr * shape :=
  let k := reg_int rs in
  if Int.equal k 0 then ('(w0), SLit 0) else (let t := bi (rf_get rf k) in (t, shape_of false t)).

Ltac2 zlit_add (p : int) (k : int) : int :=
  let t := Int.add p k in
  if Int.lt t 0 then sf_fail "negative pc" else t.

Ltac2 eq_refl_z (t : constr) : constr := mk_app (gref reference:(eq_refl)) [| gref reference:(Z); t |].

(* [comment removed for export] *)
Ltac2 Type comps := { g_segs : constr; g_q : constr; g_r : constr; g_f : constr; g_pc : constr; g_fc : constr; g_rv : constr;
                      g_m : constr; g_ro : constr }.
Ltac2 comps_of (g : constr) : comps :=
  let (segs, q, st) :=
    match Constr.Unsafe.kind g with
    | Constr.Unsafe.App h a =>
        if Int.equal (Array.length a) 3 then
          (if is_const reference:(evt) h then (Array.get a 0, Array.get a 1, Array.get a 2) else sf_fail "goal head")
        else sf_fail "goal shape"
    | _ => sf_fail "goal shape"
    end in
  let sa :=
    match Constr.Unsafe.kind st with
    | Constr.Unsafe.App h a =>
        if Int.equal (Array.length a) 7 then (if is_const reference:(MS) h then a else sf_fail "state head") else sf_fail "state shape"
    | _ => sf_fail "state shape"
    end in
  { g_segs := segs; g_q := q; g_r := Array.get sa 0; g_f := Array.get sa 1; g_pc := Array.get sa 2; g_fc := Array.get sa 3;
    g_rv := Array.get sa 4; g_m := Array.get sa 5; g_ro := Array.get sa 6 }.
Ltac2 mem_of_goal (g : constr) : constr := (comps_of g).(g_m).

Ltac2 sf_step (o : opts) : unit :=
  let g := Control.goal () in
  let c := comps_of g in
  let segs := c.(g_segs) in let q := c.(g_q) in let r := c.(g_r) in let f := c.(g_f) in let pcw := c.(g_pc) in
  let fc := c.(g_fc) in let rv := c.(g_rv) in let m := c.(g_m) in let ro := c.(g_ro) in
  let st := match Constr.Unsafe.kind g with Constr.Unsafe.App _ a => Array.get a 2 | _ => sf_fail "goal shape" end in
  (* [comment removed for export] *)
  (match Constr.Unsafe.kind segs with Constr.Unsafe.Constant _ _ => () | _ => sf_fail "abstract image" end);
  let rf := regfile_of r in
  let (ztobv, n64, pcz) :=
    match Constr.Unsafe.kind pcw with
    | Constr.Unsafe.App h a =>
        if Int.equal (Array.length a) 2 then (if is_const reference:(Z_to_bv) h then (h, Array.get a 0, Array.get a 1) else sf_fail "pc") else sf_fail "pc"
    | _ => sf_fail "pc"
    end in
  let p := match z_int pcz with Some p => p | None => sf_fail "pc literal" end in
  (if Int.lt p 0 then sf_fail "pc range" else ());
  (match n_int n64 with Some w => if Int.equal w 64 then () else sf_fail "pc width" | None => sf_fail "pc width" end);
  (* [comment removed for export] *)
  let fd := mk_app (gref reference:(fetch_dec)) [| segs; pcw |] in
  let fdv := tm "vm" (fun () => Std.eval_vm None fd) in
  let (opt_ty, w, i, sz) :=
    match Constr.Unsafe.kind fdv with
    | Constr.Unsafe.App _ a =>
        if Int.equal (Array.length a) 2 then
          match Constr.Unsafe.kind (Array.get a 1) with
          | Constr.Unsafe.App _ b =>
              if Int.equal (Array.length b) 4 then
                match Constr.Unsafe.kind (Array.get b 3) with
                | Constr.Unsafe.App _ c =>
                    if Int.equal (Array.length c) 4 then (Array.get a 0, Array.get b 2, Array.get c 2, Array.get c 3) else sf_fail "decode"
                | _ => sf_fail "decode"
                end
              else sf_fail "decode"
          | _ => sf_fail "decode"
          end
        else sf_fail "fetch"
    | _ => sf_fail "fetch"
    end in
  let szi := match z_int sz with Some k => k | None => sf_fail "size" end in
  let wd := word_ty () in
  (* [comment removed for export] *)
  let pc_add (k : int) : constr * constr :=
    let t := zlit_add p k in
    let tz := int_z t in
    (mk_app ztobv [| n64; tz |], mk_app (gref reference:(sf_pc_add)) [| pcz; int_z k; tz; eq_refl_z tz |]) in
  (* [comment removed for export] *)
  let pc_tgt (imm : constr) : constr * constr :=
    let s := match imm_signed imm with Some s => s | None => sf_fail "immediate" end in
    let t := zlit_add p s in
    let tz := int_z t in
    let n := match bv_lit imm with Some (n, _) => n | None => sf_fail "immediate" end in
    (mk_app ztobv [| n64; tz |], mk_app (gref reference:(sf_btgt)) [| pcz; n; imm; tz; eq_refl_z tz |]) in
  (* [comment removed for export] *)
  let zadd := gref reference:(Z.add) in
  let addimm (alu : bool) (x : constr) (sh : shape) (imm : constr) : (constr * constr) option :=
    if Bool.neg sf_fastpaths then None else if Bool.neg (o.(known)) then None else
    match imm_signed imm, bv_lit imm with
    | Some s, Some (n, _) =>
        (match sh with
         | SVar _ =>
             if Int.equal s 0 then
               Some (x, mk_app (gref (if alu then reference:(sf_addi0) else reference:(sf_addr0))) [| x; n; imm; eq_refl_z (int_z 0) |])
             else
               Some (mk_app ztobv [| n64; mk_app zadd [| mk_app (gref reference:(bv_unsigned)) [| n64; x |]; int_z s |] |],
                     mk_app (gref (if alu then reference:(alu_addi) else reference:(b_addsext))) [| x; n; imm |])
         | SLit v =>
             let tz := int_z (Int.add v s) in
             Some (mk_app ztobv [| n64; tz |],
                   mk_app (gref (if alu then reference:(sf_addi_lit) else reference:(sf_btgt))) [| int_z v; n; imm; tz; eq_refl_z tz |])
         | SOff ee y cz c =>
             let t := Int.add c s in
             if Int.equal t 0 then
               Some (y, mk_app (gref (if alu then reference:(sf_addi_off0) else reference:(sf_addr_off0))) [| y; cz; n; imm; eq_refl_z (int_z 0) |])
             else
               (let tz := int_z t in
                Some (mk_app ztobv [| n64; mk_app zadd [| ee; tz |] |],
                      mk_app (gref (if alu then reference:(sf_addi_off) else reference:(sf_addr_off))) [| ee; cz; n; imm; tz; eq_refl_z tz |]))
         | SOther => None
         end)
    | _, _ => None
    end in
  (* [comment removed for export] *)
  let rel1 := Constr.Unsafe.make (Constr.Unsafe.Rel 1) in
  let fdf := mk_app (gref reference:(fetch_dec_fetch)) [| segs; pcw; w; i; sz; rel1 |] in
  let fde := mk_app (gref reference:(fetch_dec_ecall)) [| segs; pcw; w; i; sz; rel1 |] in
  let fdd := mk_app (gref reference:(fetch_dec_dec)) [| segs; pcw; w; i; sz; rel1 |] in
  let fd_ty := mk_app (gref reference:(eq)) [| mk_app (gref reference:(option)) [| opt_ty |]; fd; fdv |] in
  let fd_prf := Constr.Unsafe.make (Constr.Unsafe.Cast (mk_app (gref reference:(eq_refl)) [| mk_app (gref reference:(option)) [| opt_ty |]; fdv |])
                                      Constr.Cast.vm fd_ty) in
  let eq_false := '(@eq_refl bool false) in
  let eq_true := '(@eq_refl bool true) in
  (* [comment removed for export] *)
  let mk_state (cn : comps) (r' : constr) (pc' : constr) (m' : constr) : constr :=
    mk_app (gref reference:(evt)) [| cn.(g_segs); cn.(g_q);
       mk_app (gref reference:(MS)) [| r'; cn.(g_f); pc'; cn.(g_fc); cn.(g_rv); m'; cn.(g_ro) |] |] in
  let install (lem : constr) (args_pre : constr list) (args_post : constr list) (kty : constr) : unit :=
    let k := strip_cast open_constr:(_ : $kty) in
    let args := Array.of_list (List.append [segs; q; r; f; pcw; fc; rv; m; ro; w] (List.append args_pre (List.append [fdf; fde; fdd] (List.append args_post [k])))) in
    let body := mk_app lem args in
    let term := mk_app (Constr.Unsafe.make (Constr.Unsafe.Lambda (Constr.Binder.make (Some @c10fd) fd_ty) body)) [| fd_prf |] in
    match Constr.Unsafe.kind k with
    | Constr.Unsafe.Evar ev _ => tm "install" (fun () => Std.exact_no_check term; Control.new_goal ev)
    | _ => sf_fail "continuation evar"
    end in
  (* [comment removed for export] *)
  let rest (write : bool) : comps * regfile :=
    let fl := if write then (if rf_is_raw rf then { (bi_flags ()) with Std.rConst := [reference:(tset)] } else bi_flags ()) else bi_flags () in
    let g' := tm "bi" (fun () => Std.eval_cbv fl g) in
    let cn := comps_of g' in (cn, regfile_of (cn.(g_r))) in
  (* [comment removed for export] *)
  let x := mk_det n64 sf_scan_budget in
  let scan_state (cn : comps) (rfn : regfile) (skip : int) : unit :=
    if o.(known) then
      tm "scan" (fun () =>
        let d := sf_scan_depth in
        if Int.le d 0 then () else
        (rf_iter rfn skip (fun t => if clean_shape x t then () else scan x d t);
         scan x d (cn.(g_m)); scan x d (cn.(g_q)); scan_fchain x d (Int.sub 0 1) (cn.(g_f)); scan x d (cn.(g_fc)); scan x d (cn.(g_rv)); scan x d (cn.(g_ro));
         (if sf_debug then printf "SF-SCANNED %i" (Int.sub sf_scan_budget ((x.(budget)).(contents))) else ())))
    else () in
  let whole_v (mem_class : bool) : bool := if o.(known) then (if mem_class then (x.(dv)).(contents) else false) else false in
  let whole_z (mem_class : bool) : bool :=
    if o.(known) then (if o.(z) then (if (x.(dz)).(contents) then true else whole_v mem_class) else false) else false in
  let small_of (mem_class : bool) (wr_raw : bool) : small :=
    { bi_ := wr_raw;
      vt := (if o.(known) then Bool.neg (whole_v mem_class) else false);
      zs := (if o.(known) then (if o.(z) then Bool.neg (whole_z mem_class) else false) else false) } in
  (* [comment removed for export] *)
  let post_v (mem_class : bool) : unit :=
    if o.(known) then (if whole_v mem_class then ((if sf_debug then printf "SF-DIRTY-V depth %i" (Int.sub sf_scan_depth ((x.(hitd)).(contents))) else ()); run_vtail ()) else ())
    else Ltac1.run (if mem_class then o.(rpm) else o.(rp)) in
  let post_z (mem_class : bool) : unit :=
    if whole_z mem_class then ((if sf_debug then printf "SF-DIRTY-Z depth %i" (Int.sub sf_scan_depth ((x.(hitd)).(contents))) else ()); run_zsimp ()) else () in
  let post (mem_class : bool) : unit := run_frm (); post_v mem_class; post_z mem_class in
  (* [comment removed for export] *)
  let post_w (mem_class : bool) : unit :=
    (if o.(known) then (if (x.(dr)).(contents) then ((if sf_debug then printf "SF-DIRTY-R" else ()); ltac1:(simp_regs)) else ())
     else ltac1:(simp_regs));
    post mem_class in
  let (hd, ia) :=
    match Constr.Unsafe.kind i with
    | Constr.Unsafe.App h a => (h, a)
    | _ => sf_fail "instruction"
    end in
  let arg (k : int) : constr := Array.get ia k in
  (* [comment removed for export] *)
  let rd_class (lem : Std.reference) (fields : constr list) (rd : constr) (fast : unit -> (constr * constr) option) (lhs : unit -> constr) : unit :=
    (if Int.equal szi 4 then () else sf_fail "size");
    let k := reg_int rd in
    (if Int.equal k 0 then sf_fail "rd = x0" else ());
    let (cn, rfn) := rest true in
    scan_state cn rfn k;
    let sm := small_of false (rf_is_raw rf) in
    let (v, hv) := match fast () with
                   | Some r => r
                   | None => let lhs := lhs () in (if sf_debug then printf "SF-SLOWVAL %t" lhs else ()); tm "val" (fun () => small_eq wd lhs (fun () => val_pass o sm i st))
                   end in
    let (pc', hpc) := pc_add 4 in
    install (gref lem) (List.append fields [v; pc']) [eq_false; hv; hpc] (mk_state cn (rf_set rfn k v) pc' (cn.(g_m)));
    post_w false in
  if is_ctor reference:(OpImm) hd then
    let op := arg 0 in let rd := arg 1 in let rs := arg 2 in let imm := arg 3 in
    rd_class reference:(evt_OpImm) [op; rd; rs; imm] rd
      (fun () => if is_ctor reference:(ALU_ADD) op then (let (x, sh) := operand_shape rf rs in addimm true x sh imm) else None)
      (fun () => let x := operand rf rs in '(alu64 $op $x (sext 64 $imm)))
  else if is_ctor reference:(ShiftImm) hd then
    let op := arg 0 in let rd := arg 1 in let rs := arg 2 in let sh := arg 3 in
    rd_class reference:(evt_ShiftImm) [op; rd; rs; sh] rd (fun () => None) (fun () => let x := operand rf rs in '(alu64 $op $x (zext 64 $sh)))
  else if is_ctor reference:(Op) hd then
    let op := arg 0 in let rd := arg 1 in let rs1 := arg 2 in let rs2 := arg 3 in
    rd_class reference:(evt_Op) [op; rd; rs1; rs2] rd (fun () => None) (fun () => let x1 := operand rf rs1 in let x2 := operand rf rs2 in '(alu64 $op $x1 $x2))
  else if is_ctor reference:(OpImm32) hd then
    let rd := arg 0 in let rs := arg 1 in let imm := arg 2 in
    rd_class reference:(evt_OpImm32) [rd; rs; imm] rd (fun () => None) (fun () => let x := operand rf rs in '(sext 64 (alu32 ALU_ADD (low32 $x) (sext 32 $imm))))
  else if is_ctor reference:(ShiftImm32) hd then
    let op := arg 0 in let rd := arg 1 in let rs := arg 2 in let sh := arg 3 in
    rd_class reference:(evt_ShiftImm32) [op; rd; rs; sh] rd (fun () => None) (fun () => let x := operand rf rs in '(sext 64 (alu32 $op (low32 $x) (zext 32 $sh))))
  else if is_ctor reference:(Op32) hd then
    let op := arg 0 in let rd := arg 1 in let rs1 := arg 2 in let rs2 := arg 3 in
    rd_class reference:(evt_Op32) [op; rd; rs1; rs2] rd (fun () => None)
      (fun () => let x1 := operand rf rs1 in let x2 := operand rf rs2 in '(sext 64 (alu32 $op (low32 $x1) (low32 $x2))))
  else if is_ctor reference:(Mul) hd then
    let op := arg 0 in let rd := arg 1 in let rs1 := arg 2 in let rs2 := arg 3 in
    rd_class reference:(evt_Mul) [op; rd; rs1; rs2] rd (fun () => None) (fun () => let x1 := operand rf rs1 in let x2 := operand rf rs2 in '(mul_div $op $x1 $x2))
  else if is_ctor reference:(Mul32) hd then
    let op := arg 0 in let rd := arg 1 in let rs1 := arg 2 in let rs2 := arg 3 in
    rd_class reference:(evt_Mul32) [op; rd; rs1; rs2] rd (fun () => None)
      (fun () => let x1 := operand rf rs1 in let x2 := operand rf rs2 in '(sext 64 (mul_div $op (low32 $x1) (low32 $x2))))
  else if is_ctor reference:(Lui) hd then
    let rd := arg 0 in let imm := arg 1 in
    rd_class reference:(evt_Lui) [rd; imm] rd
      (fun () => if Bool.neg sf_fastpaths then None else if Bool.neg (o.(known)) then None else
                 match imm_signed imm with
                 | Some s => let tz := int_z (Int.mul s 4096) in
                             Some (mk_app ztobv [| n64; tz |], mk_app (gref reference:(sf_lui)) [| imm; tz; eq_refl_z tz |])
                 | None => None
                 end)
      (fun () => '(sext 64 (bv_concat 32 $imm (Z_to_bv 12 0))))
  else if is_ctor reference:(Auipc) hd then
    let rd := arg 0 in let imm := arg 1 in
    rd_class reference:(evt_Auipc) [rd; imm] rd
      (fun () => if Bool.neg sf_fastpaths then None else if Bool.neg (o.(known)) then None else
                 match imm_signed imm with
                 | Some s => let t := Int.add (Int.mul s 4096) p in
                             if Int.lt t 0 then None else
                             (let tz := int_z t in
                              Some (mk_app ztobv [| n64; tz |], mk_app (gref reference:(sf_auipc)) [| pcz; imm; tz; eq_refl_z tz |]))
                 | None => None
                 end)
      (fun () => '(bv_add $pcw (sext 64 (bv_concat 32 $imm (Z_to_bv 12 0)))))
  else if is_ctor reference:(Load) hd then
   ((if Int.equal szi 4 then () else sf_fail "size");
    let msz := arg 0 in let sgn := arg 1 in let rd := arg 2 in let rs := arg 3 in let imm := arg 4 in
    let k := reg_int rd in
    (if Int.equal k 0 then sf_fail "rd = x0" else ());
    let (x, shx) := operand_shape rf rs in
    let (cn, rfn) := rest true in
    scan_state cn rfn k;
    let sm := small_of true (rf_is_raw rf) in
    let (a, ha) := match addimm false x shx imm with
                   | Some r => r
                   | None => tm "addr" (fun () => small_eq wd '(bv_add $x (sext 64 $imm)) (fun () => addr_pass i st))
                   end in
    let lhs0 := mk_app (gref reference:(sf_load_lhs)) [| segs; m; msz; sgn; a |] in
    let lhs := Std.eval_cbv { (bi_flags ()) with Std.rConst := [reference:(sf_load_lhs); reference:(width_bytes)] } lhs0 in
    let ev := strip_cast open_constr:(_ : $wd) in
    let owd := mk_app (gref reference:(option)) [| wd |] in
    let (sv, hv) := tm "load" (fun () => small_eq_gen owd lhs (mk_app (gref reference:(Some)) [| wd; ev |]) (fun () => load_pass o sm)) in
    let v := some_arg sv in
    let (pc', hpc) := pc_add 4 in
    install (gref reference:(evt_Load)) [msz; sgn; rd; rs; imm; a; v; pc'] [eq_false; ha; hv; hpc] (mk_state cn (rf_set rfn k v) pc' (cn.(g_m)));
    post_w true)
  else if is_ctor reference:(Store) hd then
   ((if Int.equal szi 4 then () else sf_fail "size");
    let msz := arg 0 in let rs1 := arg 1 in let rs2 := arg 2 in let imm := arg 3 in
    (match Constr.Unsafe.kind rv with
     | Constr.Unsafe.App h _ => if is_ctor reference:(None) h then () else sf_fail "reservation"
     | _ => sf_fail "reservation"
     end);
    let (cn, rfn) := rest false in
    scan_state cn rfn 0;
    let (x1, shx) := operand_shape rf rs1 in let x2 := operand rf rs2 in
    let (a, ha) := match addimm false x1 shx imm with
                   | Some r => r
                   | None => tm "addr" (fun () => small_eq wd '(bv_add $x1 (sext 64 $imm)) (fun () => addr_pass i st))
                   end in
    let lhsb := Std.eval_cbv { (bi_flags ()) with Std.rConst := [reference:(sf_store_lhs); reference:(width_bytes)] }
                  (mk_app (gref reference:(sf_store_lhs)) [| msz; x2 |]) in
    let (bs, hbs) := tm "bytes" (fun () => small_eq '(list byte) lhsb (fun () => bytes_pass o st)) in
    let n := Std.eval_cbv { (bi_flags ()) with Std.rConst := [reference:(sf_store_n); reference:(width_bytes)] }
                  (mk_app (gref reference:(sf_store_n)) [| msz |]) in
    let eva := strip_cast open_constr:(_ : $wd) in
    let okty := '(store_ok $segs $m $a $n = true /\ $a = $eva) in
    let hok := tm "store_ok" (fun () => prove okty (fun () => ltac1:(stepL_store_ok))) in
    let a' := match Constr.Unsafe.kind eva with
              | Constr.Unsafe.Evar _ _ => sf_fail "store address"
              | ka => Constr.Unsafe.make ka
              end in
    (* [comment removed for export] *)
    (if o.(known) then (if Int.le sf_scan_depth 0 then () else scan x sf_scan_depth a') else ());
    let hrv := mk_app (gref reference:(eq_refl)) [| mk_app (gref reference:(option)) [| wd |]; rv |] in
    let (pc', hpc) := pc_add 4 in
    let m' := mk_app (gref reference:(write_to_mem)) [| cn.(g_m); a'; bs |] in
    install (gref reference:(evt_Store)) [msz; rs1; rs2; imm; a; a'; bs; rv; pc'] [ha; hbs; hok; hrv; hpc] (mk_state cn (cn.(g_r)) pc' m');
    run_frm (); post_v true;
    ltac1:(mem_after_store_opt);
    (if o.(z) then
       (if o.(known) then
          (* [comment removed for export] *)
          Control.enter (fun () =>
            match Constr.Unsafe.kind (mem_of_goal (Control.goal ())) with
            | Constr.Unsafe.Var _ => post_z true
            | _ => run_zsimp ()
            end)
        else ())
     else ()))
  else if is_ctor reference:(Branch) hd then
   ((if Int.equal szi 4 then () else sf_fail "size");
    let bc := arg 0 in let rs1 := arg 1 in let rs2 := arg 2 in let imm := arg 3 in
    let (cn, rfn) := rest false in
    scan_state cn rfn 0;
    let (x1, sh1) := operand_shape rf rs1 in let (x2, sh2) := operand_shape rf rs2 in
    let sm := small_of true false in
    let bfl := { (bi_flags ()) with Std.rConst := [reference:(branch_taken)] } in
    (* [comment removed for export] *)
    let simple (sh : shape) : bool := match sh with SVar _ => true | SLit _ => true | _ => false end in
    let (cnd, hc) :=
      if (if sf_fastpaths then (if o.(known) then (if simple sh1 then simple sh2 else false) else false) else false) then
        (let z0 := mk_app ztobv [| n64; int_z 0 |] in
         let y1 := if Int.equal (reg_int rs1) 0 then z0 else x1 in
         let y2 := if Int.equal (reg_int rs2) 0 then z0 else x2 in
         let nf := Std.eval_cbv bfl '(branch_taken $bc $y1 $y2) in
         (nf, mk_app (gref reference:(eq_refl)) [| gref reference:(bool); nf |]))
      else
        (let lhs := Std.eval_cbv bfl '(branch_taken $bc $x1 $x2) in
         tm "cnd" (fun () => small_eq '(bool) lhs (fun () => val_pass o sm i st))) in
    let (tgt, ht) := pc_tgt imm in
    let (pc', hpc) := pc_add 4 in
    let npc := '(match $cnd return bv 64 with true => $tgt | false => $pc' end) in
    install (gref reference:(evt_Branch)) [bc; rs1; rs2; imm; cnd; tgt; pc'] [hc; ht; hpc] (mk_state cn (cn.(g_r)) npc (cn.(g_m)));
    post true)
  else if is_ctor reference:(Jal) hd then
    let rd := arg 0 in let imm := arg 1 in
    let k := reg_int rd in
    let (tgt, ht) := pc_tgt imm in
    if Int.equal k 0 then
      (let (cn, rfn) := rest false in
       scan_state cn rfn 0;
       install (gref reference:(evt_Jal_x0)) [rd; imm; sz; tgt] [eq_true; ht] (mk_state cn (cn.(g_r)) tgt (cn.(g_m))); post true)
    else
      (let (cn, rfn) := rest true in
       scan_state cn rfn k;
       let (npc, hn) := pc_add szi in
       install (gref reference:(evt_Jal)) [rd; imm; sz; npc; tgt] [eq_false; hn; ht] (mk_state cn (rf_set rfn k npc) tgt (cn.(g_m))); post_w true)
  else if is_ctor reference:(Jalr) hd then
    let rd := arg 0 in let rs := arg 1 in let imm := arg 2 in
    let k := reg_int rd in
    let x := operand rf rs in
    let lhs := '(bv_and (bv_add $x (sext 64 $imm)) (bv_not w1)) in
    if Int.equal k 0 then
      (let (cn, rfn) := rest false in
       scan_state cn rfn 0;
       let sm := small_of true false in
       let (tgt, ht) := tm "tgt" (fun () => small_eq wd lhs (fun () => val_pass o sm i st)) in
       install (gref reference:(evt_Jalr_x0)) [rd; rs; imm; sz; tgt] [eq_true; ht] (mk_state cn (cn.(g_r)) tgt (cn.(g_m))); post true)
    else
      (let (cn, rfn) := rest true in
       scan_state cn rfn k;
       let sm := small_of true (rf_is_raw rf) in
       let (tgt, ht) := tm "tgt" (fun () => small_eq wd lhs (fun () => val_pass o sm i st)) in
       let (npc, hn) := pc_add szi in
       install (gref reference:(evt_Jalr)) [rd; rs; imm; sz; npc; tgt] [eq_false; hn; ht] (mk_state cn (rf_set rfn k npc) tgt (cn.(g_m))); post_w true)
  else sf_fail "unsupported instruction class".

(* [comment removed for export] *)
Ltac2 sf_old (o : opts) : unit :=
  ltac1:(rp rpm vh |- step2_with_old rp rpm vh) (o.(rp)) (o.(rpm)) (o.(vh));
  if o.(z) then run_zsimp () else ().

Ltac2 nf (c : constr) : constr := Std.eval_cbv (no_flags ()) c.
Ltac2 snapshot (norm : bool) : (constr * (ident * constr option * constr) list) list :=
  let acc := { contents := [] } in
  Control.enter (fun () =>
    let n (c : constr) := if norm then nf c else c in
    let g := n (Control.goal ()) in
    let hs := List.map (fun (id, b, t) => (id, Option.map n b, n t)) (Control.hyps ()) in
    acc.(contents) := (g, hs) :: acc.(contents));
  List.rev (acc.(contents)).

Ltac2 hyps_equal (h1 : (ident * constr option * constr) list) (h2 : (ident * constr option * constr) list) : bool :=
  if Int.equal (List.length h1) (List.length h2) then
    List.for_all2 (fun (a : ident * constr option * constr) (b : ident * constr option * constr) =>
       let (ia, ba, ta) := a in let (ib, bb, tb) := b in
       if Ident.equal ia ib then
         if Constr.equal ta tb then
           match ba, bb with
           | None, None => true
           | Some x, Some y => Constr.equal x y
           | _, _ => false
           end
         else false
       else false) h1 h2
  else false.
Ltac2 snaps_equal (s1 : (constr * (ident * constr option * constr) list) list) (s2 : (constr * (ident * constr option * constr) list) list) : bool :=
  if Int.equal (List.length s1) (List.length s2) then
    List.for_all2 (fun (a : constr * (ident * constr option * constr) list) (b : constr * (ident * constr option * constr) list) =>
       let (ga, ha) := a in let (gb, hb) := b in
       if Constr.equal ga gb then hyps_equal ha hb else false) s1 s2
  else false.

Ltac2 pc_of_goal (g : constr) : constr :=
  match Constr.Unsafe.kind g with
  | Constr.Unsafe.App _ a =>
      if Int.equal (Array.length a) 3 then
        match Constr.Unsafe.kind (Array.get a 2) with
        | Constr.Unsafe.App _ b => if Int.equal (Array.length b) 7 then Array.get b 2 else g
        | _ => g
        end
      else g
  | _ => g
  end.

Ltac2 sf_dual (o : opts) : unit :=
  let g0 := Control.goal () in
  let pc := pc_of_goal g0 in
  let old := Control.plus (fun () => sf_old o; Control.zero (SF_Captured (snapshot true)))
               (fun e => match e with SF_Captured s => Some s | _ => None end) in
  match old with
  | None =>
      (* [comment removed for export] *)
      printf "SF-OLDFAIL %t" pc; sf_old o
  | Some so =>
      let ok := Control.plus (fun () =>
                   sf_step o;
                   let sn := snapshot false in
                   if snaps_equal so sn then 1 else Control.zero SF_Mismatch)
                 (fun e => match e with
                           | SF_Mismatch => 2
                           | Tactic_failure (Some msg) => printf "SF-FALLBACK %t : %a" pc (fun () m => m) msg; 3
                           | _ => printf "SF-FALLBACK %t : %a" pc (fun () e => Message.of_exn e) e; 3
                           end) in
      if Int.equal ok 1 then printf "SF-OK %t" pc
      else ((if Int.equal ok 2 then
               (let fast := Control.plus (fun () => sf_step o; Control.zero (SF_Captured (snapshot true)))
                              (fun e => match e with SF_Captured s => s | _ => [] end) in
                match so, fast with
                | (go, _) :: _, (gf, _) :: _ =>
                    if Constr.equal go gf then printf "SF-MISMATCH(hyps) %t" pc
                    else (printf "SF-MISMATCH(goal) %t@ OLD: %t@ FAST: %t" pc go gf; if sf_debug then printf "SF-PRE: %t" g0 else ())
                | _, _ => printf "SF-MISMATCH(goals) %t" pc
                end)
             else ());
            sf_old o)
  end.

Ltac2 sf_core1 (o : opts) : unit :=
  if Int.equal sf_mode 0 then sf_old o
  else if Int.equal sf_mode 1 then
    Control.once (fun () =>
      Control.plus (fun () => sf_step o)
        (fun e => (if sf_debug then printf "SF-FALLBACK %a" (fun () e => Message.of_exn e) e else ()); sf_old o))
  else Control.once (fun () => sf_dual o).

Ltac2 sf_core (o : opts) : unit := Control.enter (fun () => sf_core1 o).

Ltac2 idtac1 () : Ltac1.t := ltac1val:(idtac).
Ltac2 vtail1 () : Ltac1.t := ltac1val:(vnorm_tail).

(* [comment removed for export] *)
Ltac2 entry_generic (rp : Ltac1.t) (rpm : Ltac1.t) (vh : Ltac1.t) : unit :=
  sf_core { z := false; known := false; rp := rp; rpm := rpm; vh := vh }.
Ltac2 entry_fast (z : bool) : unit :=
  sf_core { z := z; known := true; rp := idtac1 (); rpm := vtail1 (); vh := idtac1 () }.
Ltac2 entry_step () : unit := entry_fast false.
Ltac2 entry_zstep () : unit := entry_fast true.

End SF.

#[local] Set Default Proof Mode "Classic".

(* [comment removed for export] *)
Ltac sf_step2_with rp rpm vh :=
  lazymatch goal with
  | |- SFM.marker2 => exact SFM.mark2
  | |- SFM.marker => fail "not the stock step2_fast"
  | |- _ => let f := ltac2:(rp rpm vh |- SF.entry_generic rp rpm vh) in f rp rpm vh
  end.
Ltac sf_step2_with_is_mine := let _ := constr:(ltac:(step2_with ltac:(idtac) ltac:(idtac) ltac:(idtac)) : SFM.marker2) in idtac.
Ltac sf_step2_fast :=
  lazymatch goal with
  | |- SFM.marker => sf_step2_with_is_mine; exact SFM.mark
  | |- _ => tryif sf_step2_with_is_mine then ltac2:(SF.entry_step ()) else step2_with ltac:(idtac) ltac:(vnorm_tail) ltac:(idtac)
  end.
(* [comment removed for export] *)
Ltac sf_stepz_is_default := let _ := constr:(ltac:(stepz) : SFM.marker) in idtac.
Ltac sf_zstep := tryif sf_stepz_is_default then ltac2:(SF.entry_zstep ()) else (stepz; zsimp).

Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_with rp rpm vh ::= sf_step2_with rp rpm vh.
Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.step2_fast ::= sf_step2_fast.
Ltac OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.zstep ::= sf_zstep.
