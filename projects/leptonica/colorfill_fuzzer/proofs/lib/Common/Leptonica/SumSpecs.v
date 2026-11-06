(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.colorfill_fuzzer.lib.Common Require Import PropExec CatExec CatSim StoreOk Hoare ZStores.
Import ListNotations.
Open Scope Z_scope.

Module SSP.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sterm : Type :=
| TV (i : nat)                    (* [comment removed for export] *)
| TLit (z : Z)
| TAdd (a b : sterm)
| TSub (a b : sterm)
| TMul (a b : sterm)
| TDiv (a : sterm) (k : Z)        (* [comment removed for export] *)
| TSp.                           (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive sitem : Type :=
| SReg   (r : nat)                           (* [comment removed for export] *)
| SCell  (base : sterm) (off : Z) (w : nat)  (* [comment removed for export] *)
| SFresh (lo hi : Z)                         (* [comment removed for export] *)
| SLit   (t : sterm) (z : Z)                 (* [comment removed for export] *)
| SIn    (t : sterm) (zs : list Z)           (* [comment removed for export] *)
| SRange (t : sterm) (lo hi : Z)             (* [comment removed for export] *)
| SAlign (t : sterm) (m : Z)                 (* [comment removed for export] *)
| SLe    (a b : sterm)                       (* [comment removed for export] *)
| SEq    (a b : sterm)                       (* [comment removed for export] *)
| SRegionW (base len : sterm)                (* [comment removed for export] *)
| SRegionR (base len : sterm)                (* [comment removed for export] *)
| SRoStr (t : sterm) (maxlen : Z)            (* [comment removed for export] *)
| SImgClear (lo hi : Z)                      (* [comment removed for export] *)
| SApart (b1 l1 b2 l2 : sterm).              (* [comment removed for export] *)

(* [comment removed for export] *)
Inductive seffect : Type :=
| EFrame (size : Z)                          (* [comment removed for export] *)
| EHavoc (base len : sterm)                  (* [comment removed for export] *)
| EZero  (base len : sterm)                  (* [comment removed for export] *)
| EStore (base : sterm) (off : Z) (w : nat) (v : sterm).
                                             (* [comment removed for export] *)

Record sumspec : Type := SUM {
  su_entry   : Z;                 (* [comment removed for export] *)
  su_exit    : option Z;          (* [comment removed for export] *)
  su_items   : list sitem;
  su_effects : list seffect;
  su_clobber : list nat;          (* [comment removed for export] *)
  su_result  : option (nat * sterm) (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Fixpoint lit_items (i : nat) (lits : list (nat * Z)) : list sitem :=
  match lits with
  | [] => []
  | (r, z) :: rest => SReg r :: SLit (TV i) z :: lit_items (S i) rest
  end.
Definition two64m1z : Z := 2 ^ 64 - 1.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition caller_saved : list nat := [1; 5; 6; 7; 10; 11; 12; 13; 14; 15; 16; 17; 28; 29; 30; 31]%nat.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition reg_of (r : nat) : bv 5 :=
  match r with
  | 0%nat => 0 | 1%nat => 1 | 2%nat => 2 | 3%nat => 3 | 4%nat => 4 | 5%nat => 5 | 6%nat => 6 | 7%nat => 7
  | 8%nat => 8 | 9%nat => 9 | 10%nat => 10 | 11%nat => 11 | 12%nat => 12 | 13%nat => 13 | 14%nat => 14
  | 15%nat => 15 | 16%nat => 16 | 17%nat => 17 | 18%nat => 18 | 19%nat => 19 | 20%nat => 20 | 21%nat => 21
  | 22%nat => 22 | 23%nat => 23 | 24%nat => 24 | 25%nat => 25 | 26%nat => 26 | 27%nat => 27 | 28%nat => 28
  | 29%nat => 29 | 30%nat => 30 | 31%nat => 31 | _ => 0
  end%bv.

Definition var (ws : list Z) (i : nat) : Z := nth i ws 0.

Fixpoint tval (ws : list Z) (sp : Z) (t : sterm) : Z :=
  match t with
  | TV i => var ws i
  | TLit z => z
  | TAdd a b => tval ws sp a + tval ws sp b
  | TSub a b => tval ws sp a - tval ws sp b
  | TMul a b => tval ws sp a * tval ws sp b
  | TDiv a k => tval ws sp a / k
  | TSp => sp
  end.

(* [comment removed for export] *)
Fixpoint n_inputs_l (its : list sitem) : nat :=
  match its with
  | [] => 0
  | SReg _ :: r | SCell _ _ _ :: r => S (n_inputs_l r)
  | _ :: r => n_inputs_l r
  end.
Fixpoint n_outputs_l (its : list sitem) : nat :=
  match its with
  | [] => 0
  | SFresh _ _ :: r => S (n_outputs_l r)
  | _ :: r => n_outputs_l r
  end.
Definition n_inputs (S : sumspec) : nat := n_inputs_l (su_items S).
Definition n_outputs (S : sumspec) : nat := n_outputs_l (su_items S).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.
Context {fx : FPState}.   (* [comment removed for export] *)

(* [comment removed for export] *)
Definition cell_holds (M : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
  0 <= v < 2 ^ (8 * Z.of_nat w)
  /\ rdn segs M (Z_to_bv 64 a) w = Some (Z_to_le_bytes w v).
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition flatZ (a len : Z) : Prop := 0 <= a /\ 0 <= len /\ a + len <= 2 ^ 64.

(* [comment removed for export] *)
Definition rostr_win (a k : Z) : Z := ((a + k) / 8) * 8 + 8 - a.   (* [comment removed for export] *)
Definition rostr (M : word -> option byte) (a k : Z) : Prop :=
  0 <= k /\ flatZ a (rostr_win a k)
  /\ (forall i, 0 <= i <= k -> M (Z_to_bv 64 (a + i)) = None)
  /\ (forall i, 0 <= i < k -> exists b : byte, seg_rom segs (Z_to_bv 64 (a + i)) = Some b /\ bv_unsigned b <> 0)
  /\ seg_rom segs (Z_to_bv 64 (a + k)) = Some (Z_to_bv 8 0)
  /\ (exists bs, rdn segs M (Z_to_bv 64 a) (Z.to_nat (rostr_win a k)) = Some bs).

(* [comment removed for export] *)
Fixpoint pre_items (its : list sitem) (i : nat) (ws : list Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  let sp := bv_unsigned (getr R 2) in
  match its with
  | [] => True
  | it :: rest =>
      let here :=
        match it with
        | SReg r => getr R (reg_of r) = Z_to_bv 64 (var ws i) /\ 0 <= var ws i < 2 ^ 64
        | SCell b off w => (1 <= w <= 8)%nat /\ flatZ (tval ws sp b + off) (Z.of_nat w)
                           /\ cell_holds M (tval ws sp b + off) w (var ws i)
        | SFresh _ _ => True
        | SLit t z => tval ws sp t = z
        | SIn t zs => In (tval ws sp t) zs
        | SRange t lo hi => lo <= tval ws sp t <= hi
        | SAlign t m => 0 < m /\ tval ws sp t mod m = 0
        | SLe a b => tval ws sp a <= tval ws sp b
        | SEq a b => tval ws sp a = tval ws sp b
        | SRegionW b l => flatZ (tval ws sp b) (tval ws sp l)
                          /\ store_ok segs M (Z_to_bv 64 (tval ws sp b)) (Z.to_nat (tval ws sp l)) = true
        | SRegionR b l => flatZ (tval ws sp b) (tval ws sp l)
                          /\ exists bs, rdn segs M (Z_to_bv 64 (tval ws sp b)) (Z.to_nat (tval ws sp l)) = Some bs
        | SRoStr t maxlen => exists k, k <= maxlen /\ rostr M (tval ws sp t) k
        | SImgClear lo hi => forall i, lo <= i < hi -> M (Z_to_bv 64 i) = None
        | SApart b1 l1 b2 l2 => tval ws sp b1 + tval ws sp l1 <= tval ws sp b2
                                \/ tval ws sp b2 + tval ws sp l2 <= tval ws sp b1
        end in
      let i' := match it with SReg _ | SCell _ _ _ | SFresh _ _ => S i | _ => i end in
      here /\ pre_items rest i' ws R M
  end.

(* [comment removed for export] *)
Fixpoint pre_effects (efs : list seffect) (ws : list Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  let sp := bv_unsigned (getr R 2) in
  match efs with
  | [] => True
  | EFrame sz :: rest => 0 <= sz /\ flatZ (sp - sz) sz /\ store_ok segs M (Z_to_bv 64 (sp - sz)) (Z.to_nat sz) = true
                        /\ pre_effects rest ws R M
  | EHavoc b l :: rest | EZero b l :: rest => flatZ (tval ws sp b) (tval ws sp l) /\ pre_effects rest ws R M
  | EStore b off w v :: rest => (1 <= w <= 8)%nat /\ flatZ (tval ws sp b + off) (Z.of_nat w) /\ pre_effects rest ws R M
  end.

(* [comment removed for export] *)
Fixpoint item_footprints (its : list sitem) (i : nat) (ws : list Z) (sp : Z) : list (Z * Z) :=
  match its with
  | [] => []
  | it :: rest =>
      let i' := match it with SReg _ | SCell _ _ _ | SFresh _ _ => S i | _ => i end in
      match it with
      | SCell b off w => (tval ws sp b + off, Z.of_nat w) :: item_footprints rest i' ws sp
      | SRegionW b l | SRegionR b l => (tval ws sp b, tval ws sp l) :: item_footprints rest i' ws sp
      | SRoStr t maxlen => (tval ws sp t, maxlen + 16) :: item_footprints rest i' ws sp
      | _ => item_footprints rest i' ws sp
      end
  end.
Fixpoint frame_apart (lo hi : Z) (fps : list (Z * Z)) : Prop :=
  match fps with
  | [] => True
  | (b, l) :: rest => (b + l <= lo \/ hi <= b) /\ frame_apart lo hi rest
  end.
Fixpoint frames_apart (efs : list seffect) (sp : Z) (fps : list (Z * Z)) : Prop :=
  match efs with
  | [] => True
  | EFrame sz :: rest => frame_apart (sp - sz) sp fps /\ frames_apart rest sp fps
  | _ :: rest => frames_apart rest sp fps
  end.

Definition spec_pre (S : sumspec) (ws : list Z) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
  let sp := bv_unsigned (getr R 2) in
  pre_items (su_items S) 0 ws R M
  /\ pre_effects (su_effects S) ws R M
  /\ frames_apart (su_effects S) sp (item_footprints (su_items S) 0 ws sp)
  /\ match su_exit S with None => ret_ok (getr R 1) | Some _ => True end.

(* [comment removed for export] *)
Fixpoint outside_effects (efs : list seffect) (ws : list Z) (sp : Z) (x : Z) : Prop :=
  match efs with
  | [] => True
  | ef :: rest =>
      (match ef with
       | EFrame sz => x < sp - sz \/ sp <= x
       | EHavoc b l | EZero b l => x < tval ws sp b \/ tval ws sp b + tval ws sp l <= x
       | EStore b off w _ => x < tval ws sp b + off \/ tval ws sp b + off + Z.of_nat w <= x
       end)
      /\ outside_effects rest ws sp x
  end.

(* [comment removed for export] *)
Fixpoint post_effects (efs : list seffect) (ws : list Z) (sp : Z) (M' : word -> option byte) : Prop :=
  match efs with
  | [] => True
  | ef :: rest =>
      (match ef with
       | EFrame _ | EHavoc _ _ => True
       | EZero b l => forall i, 0 <= i < tval ws sp l -> M' (Z_to_bv 64 (tval ws sp b + i)) = Some (Z_to_bv 8 0)
       | EStore b off w v => cell_holds M' (tval ws sp b + off) w ((tval ws sp v) mod 2 ^ (8 * Z.of_nat w))
       end)
      /\ post_effects rest ws sp M'
  end.

(* [comment removed for export] *)
Fixpoint post_items (its : list sitem) (i : nat) (ws : list Z) : Prop :=
  match its with
  | [] => True
  | SFresh lo hi :: rest => (lo <= var ws i <= hi) /\ post_items rest (S i) ws
  | (SReg _ | SCell _ _ _) :: rest => post_items rest (S i) ws
  | _ :: rest => post_items rest i ws
  end.

(* [comment removed for export] *)
Fixpoint nat_inb (r : nat) (l : list nat) : bool :=
  match l with [] => false | x :: t => if Nat.eqb r x then true else nat_inb r t end.
Definition reg_kept (S : sumspec) (r : nat) : bool :=
  if nat_inb r (su_clobber S) then false
  else match su_result S with Some (rr, _) => negb (Nat.eqb r rr) | None => true end.
Fixpoint kfilter (S : sumspec) (l : list nat) : list nat :=
  match l with [] => [] | r :: t => if reg_kept S r then r :: kfilter S t else kfilter S t end.
Definition all_regs : list nat :=
  [1; 2; 3; 4; 5; 6; 7; 8; 9; 10; 11; 12; 13; 14; 15; 16; 17; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27; 28; 29; 30; 31]%nat.
(* [comment removed for export] *)
Definition kept_list (S : sumspec) : list nat := kfilter S all_regs.
Fixpoint regs_kept_l (l : list nat) (R R' : bvmap 5 word) : Prop :=
  match l with
  | [] => True
  | r :: t => getr R' (reg_of r) = getr R (reg_of r) /\ regs_kept_l t R R'
  end.

Definition spec_post (S : sumspec) (ws : list Z) (R : bvmap 5 word) (M : word -> option byte)
           (R' : bvmap 5 word) (M' : word -> option byte) : Prop :=
  let sp := bv_unsigned (getr R 2) in
  (* [comment removed for export] *)
  regs_kept_l (kept_list S) R R'
  /\ match su_result S with
     | Some (rr, t) => getr R' (reg_of rr) = Z_to_bv 64 (tval ws sp t)
     | None => True
     end
  (* [comment removed for export] *)
  /\ (forall x : word, outside_effects (su_effects S) ws sp (bv_unsigned x) -> M' x = M x)
  /\ mem_grows M M'
  /\ post_effects (su_effects S) ws sp M'
  (* [comment removed for export] *)
  /\ post_items (su_items S) 0 ws.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition exit_target (S : sumspec) (R : bvmap 5 word) : word :=
  match su_exit S with
  | None => getr R 1
  | Some pc => Z_to_bv 64 pc
  end.

Definition sum_contract (S : sumspec) : Prop :=
  forall (ins : list Z) (R : bvmap 5 word) (M rom : word -> option byte),
    length ins = n_inputs S ->
    spec_pre S ins R M ->
    exists (outs : list Z) (R' : bvmap 5 word) (M' : word -> option byte),
      length outs = n_outputs S
      /\ msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
      /\ spec_post S (ins ++ outs) R M R' M'.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

Ltac spec_unfold_in H :=
  cbv beta iota zeta delta [spec_pre spec_post pre_items pre_effects post_items post_effects outside_effects
                            exit_target n_inputs n_outputs n_inputs_l n_outputs_l
                            su_entry su_exit su_items su_effects su_clobber su_result
                            tval var nth reg_of reg_kept kept_list kfilter nat_inb all_regs regs_kept_l Nat.eqb negb
                            item_footprints frame_apart frames_apart lit_items two64m1z caller_saved] in H.
Ltac spec_unfold :=
  cbv beta iota zeta delta [spec_pre spec_post pre_items pre_effects post_items post_effects outside_effects
                            exit_target n_inputs n_outputs n_inputs_l n_outputs_l
                            su_entry su_exit su_items su_effects su_clobber su_result
                            tval var nth reg_of reg_kept kept_list kfilter nat_inb all_regs regs_kept_l Nat.eqb negb
                            item_footprints frame_apart frames_apart lit_items two64m1z caller_saved].
(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition spec_memset (entry : Z) : sumspec :=
  SUM entry None
      [SReg 10; SReg 11; SReg 12;
       SLit (TV 1) 0;
       SRange (TV 2) 1 (2 ^ 31);
       SRegionW (TV 0) (TV 2)]
      [EZero (TV 0) (TV 2)]
      [11; 12; 13; 14; 15; 16]%nat          (* [comment removed for export] *)
      (Some (10%nat, TV 0)).                (* [comment removed for export] *)

(* [comment removed for export] *)
Record ls_addrs : Type := LSA {
  ls_entry : Z; ls_handler_cell : Z; ls_devnull : Z; ls_canary_got : Z; ls_canary : Z;
  ls_img_lo : Z; ls_img_hi : Z; ls_frame : Z; ls_sp_lo : Z; ls_sp_hi : Z;
  ls_fmts1 : list Z; ls_fmts2 : list Z;
  ls_sev_got : Z;    (* [comment removed for export] *)
  ls_sev : Z }.      (* [comment removed for export] *)

Definition spec_lept_stderr_s1 (L : ls_addrs) : sumspec :=
  SUM (ls_entry L) None
      [SReg 10; SIn (TV 0) (ls_fmts1 L); SRoStr (TV 0) 200;
       SReg 11; SRoStr (TV 1) 200;
       SCell (TLit (ls_handler_cell L)) 0 8; SLit (TV 2) (ls_devnull L);
       SCell (TLit (ls_canary_got L)) 0 8; SLit (TV 3) (ls_canary L);
       SCell (TLit (ls_canary L)) 0 8;
       SImgClear (ls_img_lo L) (ls_img_hi L);
       SAlign TSp 16; SRange TSp (ls_sp_lo L) (ls_sp_hi L)]
      [EFrame (ls_frame L)]
      caller_saved
      None.

Definition spec_lept_stderr_s2 (L : ls_addrs) : sumspec :=
  SUM (ls_entry L) None
      [SReg 10; SIn (TV 0) (ls_fmts2 L); SRoStr (TV 0) 200;
       SReg 11; SRoStr (TV 1) 200;
       SReg 12; SRoStr (TV 2) 200;
       SCell (TLit (ls_handler_cell L)) 0 8; SLit (TV 3) (ls_devnull L);
       SCell (TLit (ls_canary_got L)) 0 8; SLit (TV 4) (ls_canary L);
       SCell (TLit (ls_canary L)) 0 8;
       SImgClear (ls_img_lo L) (ls_img_hi L);
       SAlign TSp 16; SRange TSp (ls_sp_lo L) (ls_sp_hi L)]
      [EFrame (ls_frame L)]
      caller_saved
      None.

(* [comment removed for export] *)
Definition spec_padbits (entry frame : Z) : sumspec :=
  SUM entry None
      [SReg 10; SRange (TV 0) 1 two64m1z; SAlign (TV 0) 8;
       SReg 11; SLit (TV 1) 0;
       SCell (TV 0) 0 4;  SRange (TV 2) 1 20000;           (* [comment removed for export] *)
       SCell (TV 0) 4 4;  SRange (TV 3) 1 20000;           (* [comment removed for export] *)
       SCell (TV 0) 8 4;  SIn (TV 4) [1; 2; 4; 8; 16];     (* [comment removed for export] *)
       SCell (TV 0) 16 4; SEq (TV 5) (TDiv (TAdd (TMul (TV 2) (TV 4)) (TLit 31)) 32);   (* [comment removed for export] *)
       SCell (TV 0) 56 8; SRange (TV 6) 1 two64m1z; SAlign (TV 6) 4;   (* [comment removed for export] *)
       SRegionW (TV 6) (TMul (TLit 4) (TMul (TV 5) (TV 3)));                          (* [comment removed for export] *)
       SApart (TV 0) (TLit 64) (TV 6) (TMul (TLit 4) (TMul (TV 5) (TV 3)));
       SAlign TSp 16]
      [EFrame frame; EHavoc (TV 6) (TMul (TLit 4) (TMul (TV 5) (TV 3)))]
      caller_saved
      (Some (10%nat, TLit 0)).

(* [comment removed for export] *)
Definition spec_padbits24 (entry frame : Z) (L : ls_addrs) : sumspec :=
  SUM entry None
      [SReg 10; SRange (TV 0) 1 two64m1z; SAlign (TV 0) 8;
       SReg 11; SLit (TV 1) 0;
       SCell (TV 0) 0 4; SCell (TV 0) 4 4;
       SCell (TV 0) 8 4; SLit (TV 4) 24;
       SCell (TLit (ls_handler_cell L)) 0 8; SLit (TV 5) (ls_devnull L);
       SCell (TLit (ls_canary_got L)) 0 8; SLit (TV 6) (ls_canary L);
       SCell (TLit (ls_canary L)) 0 8;
       SCell (TLit (ls_sev_got L)) 0 8; SLit (TV 8) (ls_sev L);
       SCell (TLit (ls_sev L)) 0 4;
       SImgClear (ls_img_lo L) (ls_img_hi L);
       SAlign TSp 16; SRange TSp (ls_sp_lo L + frame) (ls_sp_hi L)]
      [EFrame frame]
      caller_saved
      (Some (10%nat, TLit 1)).

(* [comment removed for export] *)
Definition spec_cmapfill (entry exit_pc : Z) (r_cmap r_data : nat) (data_ofs : Z) (r_nc : nat)
           (lits : list (nat * Z)) (clob : list nat) : sumspec :=
  let data := TAdd (TV 1) (TLit (- data_ofs)) in
  SUM entry (Some exit_pc)
      ([SReg r_cmap; SRange (TV 0) 1 two64m1z; SAlign (TV 0) 8;
        SReg r_data; SReg r_nc; SRange (TV 2) 1 256;
        SRange data 1 two64m1z;                                (* [comment removed for export] *)
        SCell (TV 0) 0 8; SRange (TV 3) 1 two64m1z;            (* [comment removed for export] *)
        SCell (TV 0) 12 4; SLe (TV 2) (TV 4); SRange (TV 4) 2 256;   (* [comment removed for export] *)
        SCell (TV 0) 16 4; SLit (TV 5) 0;                      (* [comment removed for export] *)
        SRegionR data (TMul (TLit 4) (TV 2));                  (* [comment removed for export] *)
        SRegionW (TV 3) (TMul (TLit 4) (TV 4));                (* [comment removed for export] *)
        SRegionW (TV 0) (TLit 24);                             (* [comment removed for export] *)
        SApart (TV 0) (TLit 24) (TV 3) (TMul (TLit 4) (TV 4));
        SApart (TV 0) (TLit 24) data (TMul (TLit 4) (TV 2));
        SApart (TV 3) (TMul (TLit 4) (TV 4)) data (TMul (TLit 4) (TV 2))]
       ++ lit_items 6 lits)
      [EHavoc (TV 3) (TMul (TLit 4) (TV 2)); EStore (TV 0) 16 4 (TV 2)]   (* [comment removed for export] *)
      clob
      None.

(* [comment removed for export] *)
Definition spec_cmapfill_null (entry exit_pc : Z) (r_cmap r_data : nat) (data_ofs : Z) (r_nc r_sev : nat)
           (lits : list (nat * Z)) (clob : list nat) (frame : Z) (L : ls_addrs) : sumspec :=
  let data := TAdd (TV 1) (TLit (- data_ofs)) in
  SUM entry (Some exit_pc)
      ([SReg r_cmap; SLit (TV 0) 0;
        SReg r_data; SReg r_nc; SRange (TV 2) 1 256;
        SRange data 1 two64m1z;
        SReg r_sev; SLit (TV 3) (ls_sev L);
        SCell (TLit (ls_handler_cell L)) 0 8; SLit (TV 4) (ls_devnull L);
        SCell (TLit (ls_canary_got L)) 0 8; SLit (TV 5) (ls_canary L);
        SCell (TLit (ls_canary L)) 0 8;
        SCell (TLit (ls_sev L)) 0 4;
        SImgClear (ls_img_lo L) (ls_img_hi L);
        SRegionR data (TMul (TLit 4) (TV 2));
        SAlign TSp 16; SRange TSp (ls_sp_lo L + frame) (ls_sp_hi L)]
       ++ lit_items 8 lits)
      [EFrame frame]
      clob
      None.

(* [comment removed for export] *)
Definition spec_maxindex (entry frame : Z) : sumspec :=
  SUM entry None
      [SReg 10; SRange (TV 0) 1 two64m1z; SAlign (TV 0) 8;
       SReg 11; SRange (TV 1) 1 two64m1z;
       SCell (TV 0) 0 4;  SRange (TV 2) 1 20000;
       SCell (TV 0) 4 4;  SRange (TV 3) 1 20000;
       SCell (TV 0) 8 4;  SIn (TV 4) [1; 2; 4; 8];
       SCell (TV 0) 16 4; SEq (TV 5) (TDiv (TAdd (TMul (TV 2) (TV 4)) (TLit 31)) 32);
       SCell (TV 0) 56 8; SRange (TV 6) 1 two64m1z; SAlign (TV 6) 4;
       SRegionR (TV 6) (TMul (TLit 4) (TMul (TV 5) (TV 3)));
       SRange (TAdd (TV 6) (TMul (TLit 4) (TMul (TV 5) (TV 3)))) 0 two64m1z;   (* [comment removed for export] *)
       SRegionW (TV 1) (TLit 4); SAlign (TV 1) 4;
       SApart (TV 1) (TLit 4) (TV 0) (TLit 64);
       SAlign TSp 16;
       SFresh 0 255]
      [EFrame frame; EStore (TV 1) 0 4 (TV 7)]
      caller_saved
      (Some (10%nat, TLit 0)).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Intro.
Variable segs : list Segment.
Context {fx : FPState}.

(* [comment removed for export] *)
Lemma sum_contract_in3 : forall S, n_inputs S = 3%nat -> n_outputs S = 0%nat ->
  (forall a b c R M rom, spec_pre segs S [a; b; c] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c] R M R' M') ->
  sum_contract segs S.
Proof.
  intros S Hi Ho H ins R M rom Hlen PRE. rewrite Hi in Hlen.
  destruct ins as [|a [|b [|c [|? ?]]]]; try discriminate Hlen.
  destruct (H a b c R M rom PRE) as (R' & M' & Hm & Hp).
  exists [], R', M'. rewrite Ho. split; [reflexivity|]. split; [exact Hm|]. rewrite app_nil_r. exact Hp.
Qed.

Lemma sum_contract_in5 : forall S, n_inputs S = 5%nat -> n_outputs S = 0%nat ->
  (forall a b c d e R M rom, spec_pre segs S [a; b; c; d; e] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e] R M R' M') ->
  sum_contract segs S.
Proof.
  intros S Hi Ho H ins R M rom Hlen PRE. rewrite Hi in Hlen.
  destruct ins as [|a [|b [|c [|d [|e [|? ?]]]]]]; try discriminate Hlen.
  destruct (H a b c d e R M rom PRE) as (R' & M' & Hm & Hp).
  exists [], R', M'. rewrite Ho. split; [reflexivity|]. split; [exact Hm|]. rewrite app_nil_r. exact Hp.
Qed.

Lemma sum_contract_in6 : forall S, n_inputs S = 6%nat -> n_outputs S = 0%nat ->
  (forall a b c d e f R M rom, spec_pre segs S [a; b; c; d; e; f] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e; f] R M R' M') ->
  sum_contract segs S.
Proof.
  intros S Hi Ho H ins R M rom Hlen PRE. rewrite Hi in Hlen.
  destruct ins as [|a [|b [|c [|d [|e [|f [|? ?]]]]]]]; try discriminate Hlen.
  destruct (H a b c d e f R M rom PRE) as (R' & M' & Hm & Hp).
  exists [], R', M'. rewrite Ho. split; [reflexivity|]. split; [exact Hm|]. rewrite app_nil_r. exact Hp.
Qed.

Lemma sum_contract_in7 : forall S, n_inputs S = 7%nat -> n_outputs S = 0%nat ->
  (forall a b c d e f g R M rom, spec_pre segs S [a; b; c; d; e; f; g] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e; f; g] R M R' M') ->
  sum_contract segs S.
Proof.
  intros S Hi Ho H ins R M rom Hlen PRE. rewrite Hi in Hlen.
  destruct ins as [|a [|b [|c [|d [|e [|f [|g [|? ?]]]]]]]]; try discriminate Hlen.
  destruct (H a b c d e f g R M rom PRE) as (R' & M' & Hm & Hp).
  exists [], R', M'. rewrite Ho. split; [reflexivity|]. split; [exact Hm|]. rewrite app_nil_r. exact Hp.
Qed.

(* [comment removed for export] *)
Lemma sum_contract_in7_out1 : forall S, n_inputs S = 7%nat -> n_outputs S = 1%nat ->
  (forall a b c d e f g R M rom, spec_pre segs S [a; b; c; d; e; f; g] R M ->
     exists o R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                     /\ spec_post segs S [a; b; c; d; e; f; g; o] R M R' M') ->
  sum_contract segs S.
Proof.
  intros S Hi Ho H ins R M rom Hlen PRE. rewrite Hi in Hlen.
  destruct ins as [|a [|b [|c [|d [|e [|f [|g [|? ?]]]]]]]]; try discriminate Hlen.
  destruct (H a b c d e f g R M rom PRE) as (o & R' & M' & Hm & Hp).
  exists [o], R', M'. rewrite Ho. split; [reflexivity|]. split; [exact Hm|]. exact Hp.
Qed.

End Intro.

(* [comment removed for export] *)

End SSP.
