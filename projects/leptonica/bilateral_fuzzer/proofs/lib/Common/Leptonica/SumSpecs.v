(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib.Common Require Import PropExec CatExec CatSim StoreOk Hoare ZStores.
From OSSVerify.Proofs.leptonica.bilateral_fuzzer.lib Require KReplay.
Ltac2 kr_t_SumSpecs () := "C46Stdlib5Lists4List9app_nil_rC47Corelib4Init5Logic8eq_ind_rc79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8n_inputsC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat02c79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9n_outputsC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2eq00K47Corelib7Numbers7BinNums8positive02K47Corelib7Numbers7BinNums8positive01K47Corelib7Numbers7BinNums1N02I45stdpp9bitvector;definitions2bv00C4ELinuxProcessSemantics5Riscv7Prelude5bvmapI47Corelib4Init9Datatypes6option00K47Corelib4Init9Datatypes4list01c79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8spec_preC1?~~~~~~~~~~~~~~~c79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP9spec_postC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic2ex00I47Corelib4Init9Datatypes4list00C47Corelib4Init5Logic6eq_indC47Corelib4Init5Logic9False_indc79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP;exit_targetC1?~~~~~~~~~~~~~~~C59OSSVerify5KrLib6Common8PropExec4mkstC1?~~~~~~~~~~~~~~~I47Corelib4Init5Logic3and00K47Corelib4Init5Logic2eq01K47Corelib4Init5Logic3and01K47Corelib4Init5Logic2ex01c79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP<sum_contractC1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes4list02c79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP8su_entryC1?~~~~~~~~~~~~~~~C45stdpp9bitvector;definitions7Z_to_bvI59OSSVerify5KrLib6Common6CatSim6msteps00C1?~~~~~~~~~~~~~~~C47Corelib4Init9Datatypes6lengthC47Corelib4Init9Datatypes3appI47Corelib4Init9Datatypes3nat00I47Corelib7Numbers7BinNums1Z00K47Corelib4Init5Logic4True01i79OSSVerify5KrLib6Common9Leptonica8SumSpecs3SSP7sumspec00C1?~~~~~~~~~~~~~~~K47Corelib4Init9Datatypes3nat01K47Corelib7Numbers7BinNums8positive03I47Corelib4Init5Logic4True00I47Corelib4Init5Logic5False00".
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
ltac2:(KReplay.run1 (kr_t_SumSpecs ()) ["Intro"] "p'0h02M'h12R'h24outsh34Hlenh43PREh52H0h61eh71li001lh81Mh91Rh:1ah;1bh<1ch=1ni011nh>3romh?1Hh@2HihA2HmhB2HohC2HphD1ShE3inshF1zi021zi031xp;1p;3p;2p;5p;7p;6p;4g0000R0p4p710g000NR1p4p710p8g000lj1NTg0027j1OTg002Vj1:Tg003bj3>Tg004<j1ATg004aj1`Tg005Fj1MTg005dj1STg006Gj2^Tg0073j1]Tg007Uj1\Tg0085j57Tg009@j72Tg00:LR2j20Tg00:fR3j1_Tg00;Fj6TTg00;bj2HTg00<Aj2CTg00=Oj59Tg00>HR4j2=Tg00>cj2cTP0j2bTP1j6ZTg00?=j4YTg00?Xj4JTg00@2j3aTg00AAj3@Tg00Aaj1WTg00Blj2XTg00CRj3ITg00DMj2VTg00Dmj3UTg00EJR1f1R0f0R53>p=Rg00EiR6?@05p=1f2R7A@6055@6p=5f5R8f4R9f3R:%W7'XP0P5D9p=8P8P91C:7P0P5D9p=3AI:70/=5p=F1V60=>15p=61V65p=D%:59>10p=L%W5,X0p=Bf6R;P8P9P:P7P0D9;I5p=Ef7R<P;AU689P:P7P0P5F2p=41=05,=7p=?P1P:P7g00FGP0P5ETp=GA>189AI:70/=5'=p=<A@6059@679@6:p=;AU605p=KP;P8P9P:P7P0P5F2,=<p=QA>170/=5p=[P9P:P7P0P5D99I;8p=Pg00Fc%N5g00GoR=#O#O#OR>'R%:0=>1=g00HN#AR?#`#M%A?#AR?#A#A#A#MR@#SRA'^RB%M?#S#]\ARAp,4segsR?f8RC%\6RD,1:RE9589P7P0D7P?p,2fxRFP8P@f;RGP9P:E8PFP0PGP8P5P:E3P?PG11;DRH95C<P8P9P0P5F2CFX0A,0AX1B,0B[^>A]8]9^<6^;6^:6%_6RI%N<,6:P?PCP9P:P7D7P1f9RJ#N16;5X=1P0P>PCET168>P3P6165>P?f<RKP0P<P;D7%D7RLf@RM'LRNP?PFPG1B@Mf:ROPJPFP0PMPGP5PJE3FERPP?PMP8P7PGPOP0P5G43?X0A,0AX1B,0BX2I,0I]4]3P;%DDRQ/R>P?PGPDP;P8D7PQP1p-0RRP5g00I3RSg00IORTn0110100020010000RUX61P>P0CGPTP?PMPDP7PGPOP0P5G49?NPX0A,0AX1B,0BX2I,0I/H5b5W4W3P3P61175RP/6>P?PM11:0RNPGPOD7fDRV,LLRWP?PFf?RX1B@Vf>RYf=RZPFP0PVPXP5PZE3FER[P?PV11<8R\P7PXPYP0P5G43?X0A,0AX1B,0BX2I,0I]4]3P5110DR]/6>P?PX117DR^POPJD7%DEP1PRP5PTPUn0110100020010101RUX61P>P0CGPTP?PV11<DR_P7PXPYP0P5G49?W[X0A,0AX1B,0BX2I,0I/H5b5W4W3P3P611;PRP/6>P?PV11<NRNPXPYD7fHR[,LLRWP?PFfCR`1B@[fBRafARbPFP0P[P`P5PbE3FERcP?P[11G\R\P7P`PaP0P5G43?X0A,0AX1B,0BX2I,0I]4]3P5118]R]/6>P?P`11;^R^PYPZD711<E#DP1PRP5PTPUn0110100020010101X61P>P0CGPTP?P[11G_P7P`PaP0P5G49?WcX0A,0AX1B,0BX2I,0I/H5b5W4W3P3P611OP/6>P?P[11GNP`PaD7PLfLRN#:P?PFfGRPP@PNfFR3fERcE8PFP0PNPPP5PcE3P?PN11X\P7PPP3P0P5G4E<X0A,0AX1B,0BX2I,0I]4]3P511J]/6>P?PP11O^PaPbD7PcPGP<P:P`PaPbP5O7P?PFPcP@fJR^PVP`E8PFP0P^PcP5P`E3P?P^PZPJP8PDC;PcPVP0P5F2CFX0A,0AX1B,0BP2PBP?PFP3P@fKR]PcPVE8PFP0P]P3P5PVE3P?P]A5YOHP3PcP0P5F2CFX0A,0AX1BfMRH#:P?PFP[1B@HPPP3PFP0PHP[P5P3E3FER\P?PHPMPKPCPDC;RW/K7P[PPP0P5GQ5[LX0A,0AX1B,0BX2I,0IP5P\P?PHPWP[PPP0P5GQX0A,0AP2PAP?PFfIR2P@fNRWP[PPE8PFP7PWP2P5PPE3P?PWPbPZPJPDC;P2P[P7P5F2CFX0APLfQR\#:P?PFPNP@P\P]P^E8R_PFP01C\NRUP5P^D9P?P\PVPMPKPDC;RKP7PNP]P0P5G4E<X0A,0AX1B,0BX2I,0IP5P?PFP]P@fPREP^P2E8RdPFP91CE]ReP5P2D9P?PEP`PXPGPDC;P]P^P9P5F2CFP4P?P_PFP8PUP0P^FPP?P\PKPNP]P8P0F2PLfURK#:RUP?PFPEP@PKfOR_PWE8R4PFP01CKERfP5PWD9P?PKP[PVPMPDC;RMP7PEP_P0P5G4E<X0A,0AX1B,0BX2I,0IP5P?PFPWfSRV,B@PHPNPFP<PVPWP:PNE3FEP?fTPPP`PXPDC;P_PWPCP9F2PIPLfXR9#:P?PFPVP@P9fRRCP\E8PFP0P9PVP5P\E3P?P9P]PPP`PDC;P7PVPCP0P5G4E<X0A,0AX1B,0BX2IPDPBPQfWRP#:P?PFPCP@PPP\PEE8PFP0PPPCP5PEE3P?PPP^P3PaPDC;PDPCP\P0P5G4E<X0A,0AX1BPJPAPQfVRC#:P?PFP\P@PCPEP_E8R@PFPO1CC\RaP5P_D9P?PCP2PcPbPDC;/KDRbP\PEPOP5F2E<X0AP8P1P=PQP5P?P@PFPOPaP;P_D9P?PCPbP\PEPOP;F2E<X=1A>1Q=P?P4PFPJPfP8PWFPRWP?PK1KMDRDPEP_PJP8F2R_'=1c1=PWP_P0PIPMP?PCP5P\PEPOP;F2X7IP5PD1b6MEZCYCYPUPVEZCJCJCJWCWAP0P5O2n2001000000121000000W5X0AP0P5O2n2001000000121103000W5X1BP0P5O2n2001000000121103000b6W4W3A580595ZJ/6>P?P]A5;7095YOP3PcD7A5<:795XG#DP1PRP5PTP1PRP5PTP1PRP5PTP1PRP5PTPSn0110100020010000n0110100020010101n0110100020010101n0110100020010101X61P>P0CGPTPL%:EP?PdPFP0PeP5P2D9P?PEA5G<;95`XP7P]P^P0P5G4E<X0A,0AX1B,0BX2I,0I/H5b5W4W3X7IXF6P0P5O2n10110000020121102100X7IX<6P0P5O2n10110000020021102100X7IX;6P0P5O2n10110000020021102100X7IX:6P0P5O2n10110000020021102100P5P0O2b3W4W3X>AX8AX9BWEAa?F:eW?WBW@WDo"). Qed.

Lemma sum_contract_in5 : forall S, n_inputs S = 5%nat -> n_outputs S = 0%nat ->
  (forall a b c d e R M rom, spec_pre segs S [a; b; c; d; e] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e] R M R' M') ->
  sum_contract segs S.
Proof.
ltac2:(KReplay.run1 (kr_t_SumSpecs ()) ["Intro"] "p'0h02M'h12R'h24outsh34Hlenh43PREh52H0h61eh71li001lh81Mh91Rh:1ah;1bh<1ch=1dh>2e0h?1ni011nh@3romhA1HhB2HihC2HmhD2HohE2HphF1ShG3inshH1zi021zi031xp;1p;3p;2p;5p;7p;6p;4g000lj1NTg0027j1JTg002Vj1;Tg003bj3CTg004<j1FTg004aj1aTg005Fj1OTg005dj1TTg006Gj2_Tg0073j1^Tg007Uj1]Tg0085j54Tg009@j76Tg00:LR0j20Tg00:fR1j1`Tg00;Fj6UTg00;bj2DTg00<Aj2HTg00=Oj5<Tg00>HR2j2>Tg00>cj2dTg0000j2cTg000Nj6[Tg00?=j4ZTg00?Xj4PTg00@2j3bTg00AAj37Tg00Aaj1YTg00Blj2XTg00CRj3LTg00DMj2WTg00Dmj3VTg00EJR3f1R4f0R53Cp=Sg00EiR6?745p=1f4R7f3R8f2R9A7645576576576p=Bf5R:P7%Y9,X8P4P5D<p=8P:P71H89P4P5D<p=5AL894/>5p=I1W64=C35p=31W65p=@%;59C34p=G%Y5,X4p=?f6R;P:P7P8P9P4D<;L5p=Af7R<P;AV6:7P8P9P4P5F6p=21>45,>9p=9P3P8P9g00FGP4P5EUp=EAC3:7AL894/>5'>p==A7645976997689767976:p=:AV645p=MP;P:P7P8P9P4P5F6,><p=RAC394/>5p=\P7P8P9P4P5D<9L;:p=QA76459769p=Kg00Fc%N5g00GoR=#J#J#J#J#JR>'S%;4=C3=g00HN#FR?#a#O%F?#FR?#F#F#F#OR@#TRA'_RB%O?#T#^\ARAp,4segsR?f:RCP<P;P:P7%]6RD,18REDBP9P4D4P?p,2fxRFP:P@f=RGP7P8E8PFP4PGP:P5P8E5P?PGPCf9RHf8RIP<11;DRJDBP:P7P4P5F6CIX0A,0AX1B,0B[^@A]8]9^66^=6^<6^;6^:6%`6RK%N<,38P?PIP7P8P9D4P3%NH13;5X?3P4P>PIEU13:>P1P6135>P?f<RLP4P<P;D4%@9RMf@RN'GROP?PFf;RP1?@NPCPHPFP4PNPPP5PHE5FARQP?PNP:P9PPPCP4P5G239X0A,0AX1B,0BX2K,0K]4]3P;%@DRR/S>P?PPPDP;P:D4PRP3p-0RSP5g00I3RTg00IORUn0110100020010000RVX63P>P4CEPUP?PNPDP9PPPCP4P5G299OQX0A,0AX1B,0BX2K,0K/D5b5W4W3P1P61195RQ/3>P?PN1184ROPPPCD4fDRW,GMRXP?PFf?RY1?@Wf>RZPGPFP4PWPYP5PGE5FAR[P?PW11<:R\P9PYPZP4P5G239X0A,0AX1B,0BX2K,0K]4]3P5114DR]/3>P?PY119DR^PCPHD4%@EP3PSP5PUPVn0110100020010101RVX63P>P4CEPUP?PW11<DR_P9PYPZP4P5G299X[X0A,0AX1B,0BX2K,0K/D5b5W4W3P1P611;QRQ/3>P?PW11<OROPYPZD4fHR[,GMRXP?PFfCR`1?@[fBRafARbPFP4P[P`P5PbE5FARcP?P[11P\R\P9P`PaP4P5G239X0A,0AX1B,0BX2K,0K]4]3P511:]R]/3>P?P`11;^R^PZPGD411<ERE#@P3PSP5PUPVn0110100020010101RVX63P>P4CEPUP?P[11P_R_P9P`PaP4P5G299XcX0A,0AX1B,0BX2K,0K/D5b5W4W3P1P611CQRQ/3>P?P[11POROP`PaD4fLRc,GMRXP?PFfGRd1?@cfFRefERfPFP4PcPdP5PfE5FARgP?Pc11Y\R\P9PdPeP4P5G239X0A,0AX1B,0BX2K,0K]4]3P511H]R]/3>P?Pd11C^R^PaPbD411PERE#@P3PSP5PUPVn0110100020010101RVX63P>P4CEPUP?Pc11Y_R_P9PdPeP4P5G299XgX0A,0AX1B,0BX2K,0K/D5b5W4W3P1P611ZQRQ/3>P?Pc11YOROPdPeD4fPRg,GMRXP?PFfKRh1?@gfJRifIRjPFP4PgPhP5PjE5FARkP?Pg11`\R\P9PhPiP4P5G239X0A,0AX1B,0BX2K,0K]4]3P511G]R]/3>P?Ph11Z^R^PePfD411YE#@P3PSP5PUPVn0110100020010101X63P>P4CEPUP?Pg11`_P9PhPiP4P5G299XkX0A,0AX1B,0BX2K,0K/D5b5W4W3P1P611aQ/3>P?Pg11`OPhPiD4PMfTRO#;P?PFfORQP@POfNR1fMRkE8PFP4POPQP5PkE5P?PO11d\P9PQP1P4P5G2E=X0A,0AX1B,0BX2K,0K]4]3P511b]/3>P?PQ11a^PiPjD4PkP`PYPPP<P8PhPiPjP5O9P?PFPkP@fRR^PcPhE8PFP4P^PkP5PhE5P?P^PfPbPGPHP:PDE:PkPcP4P5F6CIX0A,0AX1B,0BP0PBP?PFP1P@fSR]PkPcE8PFP4P]P1P5PcE5P?P]PePaPZPCPJDBP1PkP4P5F6CIX0A,0AX1BfURJ#;P?PFPg1?@JPQP1PFP4PJPgP5P1E5FAR\P?PJP[PWPNPLPIPDE:RX/M9PgPQP4P5GR5\MX0A,0AX1B,0BX2K,0KP5P\P?PJPXPgPQP4P5GRX0A,0AP0PAP?PFfQR0P@fVRXPgPQE8PFP9PXP0P5PQE5P?PXPjPfPbPGPHPDE:P0PgP9P5F6CIX0APMfYR\#;P?PFPOP@P\P]P^E8R_PFP41H\ORVP5P^D<P?P\PcP[PWPNPLPDE:RLP9POP]P4P5G2E=X0A,0AX1B,0BX2K,0KP5P?PFP]P@fXREP^P0E8RlPFP71HE]RmP5P0D<P?PEPhPdP`PYPPPDE:P]P^P7P5F6CIP2P?P_PFP:PVP4P^FQP?P\PLPOP]P:P4F6PMf]RL#;RVP?PFPEP@PLfWR_PXE8R2PFP41HLERnP5PXD<P?PLPgPcP[PWPNPDE:RNP9PEP_P4P5G2E=X0A,0AX1B,0BX2K,0KP5P?PFPXf[RW,?@PJPOPFP<PWPXP8POE5FAP?f\PQPhPdP`PYPDE:P_PXPIP7F6PKPMf`R7#;P?PFPWP@P7fZRIP\E8PFP4P7PWP5P\E5P?P7P]PQPhPdP`PDE:P9PWPIP4P5G2E=X0A,0AX1B,0BX2KPDPBPRf_RQ#;P?PFPIP@PQP\PEE8PFP4PQPIP5PEE5P?PQP^P1PiPePaPDE:PDPIP\P4P5G2E=X0A,0AX1BPHPAPRf^RI#;P?PFP\P@PIPEP_E8R@PFPC1HI\RiP5P_D<P?PIP0PkPjPfPbPDE:/MDRjP\PEPCP5F6E=X0AP:P3P=PRP5P?P@PFPCPiP;P_D<P?PIPjP\PEPCP;F6E=X?3AC3R=P?P2PFPHPnP:PXFQRXP?PL1MNDRDPEP_PHP:F6R_'>1d3=PXP_P4PKPNP?PIP5P\PEPCP;F6X7KP5PD1c6NE[CZCZPVPWE[CPCPCPWEWCP4P5O2n2001000000121000000W5X0AP4P5O2n2001000000121103000W5X1BP4P5O2n2001000000121103000b>W4W3PfPbPGPHAK:45DB/3>P?P]PePaPZPCAK;94DBP1PkD4PdP`PYPPAK<89DB#@P3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUPTn0110100020010000n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101X>3P>P4CEPUPM%;EP?PlPFP4PmP5P0D<P?PEPhPdP`PYAKP<;DBP9P]P^P4P5G2E=X0A,0AX1B,0BX2K,0K/D5b5W4W3X7KXH6P4P5O2n10110000020121102100X7KX66P4P5O2n10110000020121102100X7KX=6P4P5O2n10110000020121102100X7KX<6P4P5O2n10110000020121102100X7KX;6P4P5O2n10110000020021102100X7KX:6P4P5O2n10110000020021102100P5P4O2b3W4W3X@AX8AX9BWGAb?F8eWAWDWBWFo"). Qed.

Lemma sum_contract_in6 : forall S, n_inputs S = 6%nat -> n_outputs S = 0%nat ->
  (forall a b c d e f R M rom, spec_pre segs S [a; b; c; d; e; f] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e; f] R M R' M') ->
  sum_contract segs S.
Proof.
ltac2:(KReplay.run1 (kr_t_SumSpecs ()) ["Intro"] "p'0h02M'h12R'h24outsh34Hlenh43PREh52H0h61li001lh71eh82e0h91Mh:1Rh;1ah<1bh=1ch>1dh?1fh@1ni011nhA3romhB1HhC2HihD2HmhE2HohF2HphG1ShH3inshI1zi021zi031xp;1p;3p;2p;5p;7p;6p;4g000lj1LTg0027j1DTg002Vj1;Tg003bj3BTg004<j1FTg004aj1`Tg005Fj1KTg005dj1RTg006Gj2^Tg0073j1]Tg007Uj1\Tg0085j54Tg009@j77Tg00:LR0j20Tg00:fR1j1_Tg00;Fj6TTg00;bj2CTg00<Aj2GTg00=Oj5<Tg00>HR2j2?Tg00>cj2ZTg0000j2bTg000Nj6YTg00?=j4XTg00?Xj4MTg00@2j3aTg00AAj3:Tg00Aaj1WTg00Blj2STg00CRj3ITg00DMj2VTg00Dmj3UTg00EJR3f1R4f0R53Bp=Qg00EiR6?:45p=1f4R7f3R8f2R9A:6455:65:65:6p=Nf5R:P7%W9,S8P4P5D<p=9P:P71G89P4P5D<p=5AI894/?5p=H1V64=B35p=31V65p=>%;59B34p=Ef7R;f6R<P:%W8,S7P9P4D<;I5p==P;P<AU6:7P8P9P4P5F7p=21?45,?9p=8P3P8P9g00FGP4P5ETp=AAB3:7AI894/?5'?p=@A:6459:699:689:679:6:9:6<p=6AU645p=JP<P:P7P8P9P4P5F7,?;p=PAB394/?5p=[P7P8P9P4P5D<9I<:p=Og00Fc%L5g00GoR=#D#D#D#D#D#DR>'Q%;4=B3=g00HN#FR?#`#K%F?#FR?#F#F#F#KR@#RRA'^RB%K?#R#]\ARAp,4segsR?f;RCf8RDP;P<P:%\6RE,18RF,17DNP9P4D4P?p,2fxRGP:P@f>RHP7P8E9PGP4PHP:P5P8E5P?PHPCf:RIf9RJPD11<ERK,1;DNP:P7P4P5F7CHX0A,0AX1B,0B[^AA]9]:^?6^76^>6^=6^<6^;6%_6RL%L;,38P?PDP7P8P9D4P3%LJ13<5X@3P4P>PDET13:>P1P6135>P?f<RMP4P;P<D4%>9RNf@RO'ERPP?PGPCP@POPIPJPGP4POPCP5PJE5G=RQP?POP:P9PCPIP4P5G238X0A,0AX1B,0BX2L,0L]4]3P<%>ERR/Q>P?PCPEP<P:D4PRP3p-0RSP5g00I3RTg00IORUn0110100020010000RVX73P>P4CAPUP?POPEP9PCPIP4P5G298PQX0A,0AX1B,0BX2L,0L/C5b5W4W3P1P61195RQ/3>P?PO1184RPPCPID4fDRW,ENRXP?PGf?RYP@PWPHf=RZPGP4PWPYP5PZE5G=R[P?PW11;:R\P9PYPHP4P5G238X0A,0AX1B,0BX2L,0L]4]3P5114ER]/3>P?PY119ER^PIPJD4%>FP3PSP5PUPVn0110100020010101RVX73P>P4CAPUP?PW11;ER_P9PYPHP4P5G298X[X0A,0AX1B,0BX2L,0L/C5b5W4W3P1P611<QRQ/3>P?PW11;PRPPYPHD4fHR[,ENRXP?PGfCR`P@P[fBRafARbPGP4P[P`P5PbE5G=RcP?P[11C\R\P9P`PaP4P5G238X0A,0AX1B,0BX2L,0L]4]3P511:]R]/3>P?P`11<^R^PHPZD411;FRF#>P3PSP5PUPVn0110100020010101RVX73P>P4CAPUP?P[11C_R_P9P`PaP4P5G298XcX0A,0AX1B,0BX2L,0L/C5b5W4W3P1P611IQRQ/3>P?P[11CPRPP`PaD4fLRc,ENRXP?PGfGRdP@PcfFRefERfPGP4PcPdP5PfE5G=RgP?Pc11Y\R\P9PdPeP4P5G238X0A,0AX1B,0BX2L,0L]4]3P511J]R]/3>P?Pd11I^R^PaPbD411CFRF#>P3PSP5PUPVn0110100020010101RVX73P>P4CAPUP?Pc11Y_R_P9PdPeP4P5G298XgX0A,0AX1B,0BX2L,0L/C5b5W4W3P1P611HQRQ/3>P?Pc11YPRPPdPeD4fPRg,ENRXP?PGfKRhP@PgfJRifIRjPGP4PgPhP5PjE5G=RkP?Pg11`\R\P9PhPiP4P5G238X0A,0AX1B,0BX2L,0L]4]3P511Z]R]/3>P?Ph11H^R^PePfD411YFRF#>P3PSP5PUPVn0110100020010101RVX73P>P4CAPUP?Pg11`_R_P9PhPiP4P5G298XkX0A,0AX1B,0BX2L,0L/C5b5W4W3P1P611aQRQ/3>P?Pg11`PRPPhPiD4fTRk,ENRXP?PGfORlP@PkfNRmfMRnPGP4PkPlP5PnE5G=RoP?Pk11d\R\P9PlPmP4P5G238X0A,0AX1B,0BX2L,0L]4]3P511b]R]/3>P?Pl11a^R^PiPjD411`F#>P3PSP5PUPVn0110100020010101X83P>P4CAPUP?Pk11d_P9PlPmP4P5G298XoX0A,0AX1B,0BX2L,0L/C5b5W4W3P1P611eQ/3>P?Pk11dPPlPmD4PNfXRP#;P?PGfSRQP@PPfRR1fQRoE9PGP4PPPQP5PoE5P?PP11h\P9PQP1P4P5G2E@X0A,0AX1B,0BX2L,0L]4]3P511f]/3>P?PQ11e^PmPnD4PoPdP`PYPCP;P8PlPmPnP5O:P?PGPoP@fVR^PgPlE9PGP4P^PoP5PlE5P?P^PjPfPbPZPJP:PEF6PoPgP4P5F7CHX0A,0AX1B,0BP0PBP?PGP1P@fWR]PoPgE9PGP4P]P1P5PgE5P?P]PiPePaPH11IKDNP1PoP4P5F7CHX0A,0AX1BfYRK#;P?PGPkP@PKPQP1PGP4PKPkP5P1E5G=R\P?PKPcP[PWPOPMPDPEF6RX/J9PkPQP4P5GP5[NX0A,0AX1B,0BX2L,0LP5P\P?PKPXPkPQP4P5GPX0A,0AP0PAP?PGfUR0P@fZRXPkPQE9PGP9PXP0P5PQE5P?PXPnPjPfPbPZPJPEF6P0PkP9P5F7CHX0APNf]R\#;P?PGPPP@P\P]P^E9R_PGP41G\PRVP5P^D<P?P\PgPcP[PWPOPMPEF6RMP9PPP]P4P5G2E@X0A,0AX1B,0BX2L,0LP5P?PGP]P@f\RFP^P0E9RpPGP71GF]RqP5P0D<P?PFPlPhPdP`PYPCPEF6P]P^P7P5F7CHP2P?P_PGP:PVP4P^FOP?P\PMPPP]P:P4F7PNfaRM#;RVP?PGPFP@PMf[R_PXE9R2PGP41GMFRrP5PXD<P?PMPkPgPcP[PWPOPEF6ROP9PFP_P4P5G2E@X0A,0AX1B,0BX2L,0LP5P?PGPXP@f_RWPKPPPGP;PWPXP8PPE5G=P?f`PQPlPhPdP`PYPEF6P_PXPDP7F7PLPNfdR7#;P?PGPWP@P7f^RDP\E9PGP4P7PWP5P\E5P?P7P]PQPlPhPdP`PEF6P9PWPDP4P5G2E@X0A,0AX1B,0BX2LPEPBPRfcRQ#;P?PGPDP@PQP\PFE9PGP4PQPDP5PFE5P?PQP^P1PmPiPePaPEF6PEPDP\P4P5G2E@X0A,0AX1BPJPAPRfbRD#;P?PGP\P@PDPFP_E9R@PGPI1GD\RmP5P_D<P?PDP0PoPnPjPfPbPEF6/JERnP\PFPIP5F7E@X0AP:P3P=PRP5P?P@PGPIPmP<P_D<P?PDPnP\PFPIP<F7E@X@3AB3R=P?P2PGPJPrP:PXFORXP?PM1JOEREPFP_PJP:F7R_'?1Z3=PXP_P4PLPOP?PDP5P\PFPIP<F7X6LP5PE1b6OEYCXCXPVPWEYCMCMCMWFWDP4P5O2n2001000000121000000W5X0AP4P5O2n2001000000121103000W5X1BP4P5O2n2001000000121103000b8W4W3PjPfPbPZPJP:1145F6/3>P?P]PiPePaPHPIP<1194F6P1PoD4PhPdP`PYPCP;1189F6#>P3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUPTn0110100020010000n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101X83P>P4CAPUPN%;FP?PpPGP4PqP5P0D<P?PFPlPhPdP`PYPC11;<F6P9P]P^P4P5G2E@X0A,0AX1B,0BX2L,0L/C5b5W4W3X6LXI6P4P5O2n10110000020121102100X6LX?6P4P5O2n10110000020121102100X6LX76P4P5O2n10110000020121102100X6LX>6P4P5O2n10110000020121102100X6LX=6P4P5O2n10110000020121102100X6LX<6P4P5O2n10110000020021102100X6LX;6P4P5O2n10110000020021102100P5P4O2b3W4W3XAAX9AX:BWHAa?G8eWBWEWCWGo"). Qed.

Lemma sum_contract_in7 : forall S, n_inputs S = 7%nat -> n_outputs S = 0%nat ->
  (forall a b c d e f g R M rom, spec_pre segs S [a; b; c; d; e; f; g] R M ->
     exists R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                   /\ spec_post segs S [a; b; c; d; e; f; g] R M R' M') ->
  sum_contract segs S.
Proof.
ltac2:(KReplay.run1 (kr_t_SumSpecs ()) ["Intro"] "p'0h02M'h12R'h24outsh34Hlenh43PREh52H0h61li001lh71eh82e0h91Mh:1Rh;1ah<1bh=1ch>1dh?1fh@1ghA1ni011nhB3romhC1HhD2HihE2HmhF2HohG2HphH1ShI3inshJ1zi021zi031xp;1p;3p;2p;5p;7p;6p;4g000lj1NTg0027j1ETg002Vj1<Tg003bj3FTg004<j1GTg004aj1`Tg005Fj1MTg005dj1STg006Gj2^Tg0073j1]Tg007Uj1\Tg0085j53Tg009@j78Tg00:LR0j20Tg00:fR1j1_Tg00;Fj6TTg00<Aj2HTg00=Oj5;Tg00>HR2j2CTg00>cj2dTg0000j2cTg000Nj6ZTg00?=j4YTg00?Xj4KTg00@2j3bTg00AAj37Tg00Aaj1WTg00Blj2XTg00CRj3JTg00DMj2VTg00Dmj3UTg00;bj2aTg00EJR3f1R4f0R53Fp=Rg00EiR6?745p=1f2R7A7645576p=Of4R8f3R9A76459767576576p=9f5R:P8%W7,X9P4P5D;p=:P:P81H97P4P5D;p=5AJ974/C5p=I1V64=F35p=41V65p=>%<59F34p=Df7R;f6R<P:%W9,X8P7P4D;;J5p=?P;P<AU6:8P9P7P4P5F8p=21C45,C7p=6P3P9P7g00FGP4P5ETp=B1074/a5p=@AF3:8AJ974/C5'Cp=AA7645976797699768976:976<976;p==AU645p=LP<P:P8P9P7P4P5F8,C;p=QAF374/C5p=[P8P9P7P4P5D;9J<:p=Pg00Fc%N5g00GoR=#E#E#E#E#E#E#ER>'R%<4=F3=g00HN#GR?#`#M%G?#GR?#G#G#G#MR@#SRA'^RB%M?#S#]\ARAp,4segsR?f<RCf9RDf8REP;P<%\6RF,19RG9O:8D9P7P4D3P?p,2fxRHP:P@f?RIP8P9E:PHP4PIP:P5P9E5P?PIPCf;RJf:RKPD11<FRL9OE;D9P:P8P4P5F8CIX0A,0AX1B,0B[^BA]9]:^@6^?6^76^>6^=6^<6^;6%_6RM%N;,49P?PEP8P9P7D3P3%ND14<5XA3P4P>PEET14:>P1P6145>P?PCP4P;P<D3%>7RNf@RO'DRPP?PHPJP@POPKPDPHP4POPJP5PDE5G?RQP?POP:P7PJPKP4P5G236X0A,0AX1B,0BX2M,0M]4]3P<%>FRR/R>P?PJPFP<P:D3PRP3p-0RSP5g00I3RTg00IORUn0110100020010000RVX73P>P4CBPUP?POPFP7PJPKP4P5G296PQX0A,0AX1B,0BX2M=@M5b5W4W3P1P61175RQ/4>P?PO1194RPPJPKD3fDRW,DNRXP?PHPIP@PWf>RYf=RZPHP4PWPIP5PZE5G?R[P?PW11;:R\P7PIPYP4P5G236X0A,0AX1B,0BX2M,0M]4]3P5114FR]/4>P?PI117FR^PKPDD3%>GP3PSP5PUPVn0110100020010101RVX73P>P4CBPUP?PW11;FR_P7PIPYP4P5G296X[X0A,0AX1B,0BX2M=@M5b5W4W3P1P611<QRQ/4>P?PW11;PRPPIPYD3fHR[,DNRXP?PHfCR`P@P[fBRafARbPHP4P[P`P5PbE5G?RcP?P[11J\R\P7P`PaP4P5G236X0A,0AX1B,0BX2M,0M]4]3P511:]R]/4>P?P`11<^R^PYPZD311;GRG#>P3PSP5PUPVn0110100020010101RVX73P>P4CBPUP?P[11J_R_P7P`PaP4P5G296XcX0A,0AX1B,0BX2M=@M5b5W4W3P1P611KQRQ/4>P?P[11JPRPP`PaD3fLRc,DNRXP?PHfGRdP@PcfFRefERfPHP4PcPdP5PfE5G?RgP?Pc11I\R\P7PdPeP4P5G236X0A,0AX1B,0BX2M,0M]4]3P511D]R]/4>P?Pd11K^R^PaPbD311JGRG#>P3PSP5PUPVn0110100020010101RVX73P>P4CBPUP?Pc11I_R_P7PdPeP4P5G296XgX0A,0AX1B,0BX2M=@M5b5W4W3P1P611YQRQ/4>P?Pc11IPRPPdPeD3fPRg,DNRXP?PHfKRhP@PgfJRifIRjPHP4PgPhP5PjE5G?RkP?Pg11`\R\P7PhPiP4P5G236X0A,0AX1B,0BX2M,0M]4]3P511Z]R]/4>P?Ph11Y^R^PePfD311IGRG#>P3PSP5PUPVn0110100020010101RVX73P>P4CBPUP?Pg11`_R_P7PhPiP4P5G296XkX0A,0AX1B,0BX2M=@M5b5W4W3P1P611aQRQ/4>P?Pg11`PRPPhPiD3fTRk,DNRXP?PHfORlP@PkfNRmfMRnPHP4PkPlP5PnE5G?RoP?Pk11d\R\P7PlPmP4P5G236X0A,0AX1B,0BX2M,0M]4]3P511b]R]/4>P?Pl11a^R^PiPjD311`GRG#>P3PSP5PUPVn0110100020010101RVX83P>P4CBPUP?Pk11d_R_P7PlPmP4P5G296XoX0A,0AX1B,0BX2M=@M5b5W4W3P1P611eQRQ/4>P?Pk11dPRPPlPmD3fXRo,DNRXP?PHfSRpP@PofRRqfQRrPHP4PoPpP5PrE5G?RsP?Po11h\R\P7PpPqP4P5G236X0A,0AX1B,0BX2M,0M]4]3P511f]R]/4>P?Pp11e^R^PmPnD311dG#>P3PSP5PUPVn0110100020010101X83P>P4CBPUP?Po11h_P7PpPqP4P5G296XsX0A,0AX1B,0BX2M=@M5b5W4W3P1P611iQ/4>P?Po11hPPpPqD3PNf\RP#<P?PHfWRQP@PPfVR1fURsE:PHP4PPPQP5PsE5P?PP11l\P7PQP1P4P5G2EAX0A,0AX1B,0BX2M,0M]4]3P511j]/4>P?PQ11i^PqPrD3PsPhPdP`PIPJP;P9PpPqPrP5O;P?PHPsP@fZR^PkPpE:PHP4P^PsP5PpE5P?P^PnPjPfPbPZPDP:PFG=PsPkP4P5F8CIX0A,0AX1B,0BP0PBP?PHP1P@f[R]PsPkE:PHP4P]P1P5PkE5P?P]PmPiPePaAOYKLD9P1PsP4P5F8CIX0A,0AX1Bf]RL#<P?PHPoP@PLPQP1PHP4PLPoP5P1E5G?R\P?PLPgPcP[PWPOPCPEPFG=RX/L7PoPQP4P5GQ5[NX0A,0AX1B,0BX2M,0MP5P\P?PLPXPoPQP4P5GQX0A,0AP0PAP?PHfYR0P@f^RXPoPQE:PHP7PXP0P5PQE5P?PXPrPnPjPfPbPZPDPFG=P0PoP7P5F8CIX0APNfaR\#<P?PHPPP@P\P]P^E:R_PHP41H\PRVP5P^D;P?P\PkPgPcP[PWPOPCPFG=RCP7PPP]P4P5G2EAX0A,0AX1B,0BX2M,0MP5P?PHP]P@f`RGP^P0E:RtPHP81HG]RuP5P0D;P?PGPpPlPhPdP`PIPJPFG=P]P^P8P5F8CIP2P?P_PHP:PVP4P^FPP?P\PCPPP]P:P4F8PNfeRC#<RVP?PHPGP@PCf_R_PXE:R2PHP41HCGRvP5PXD;P?PCPoPkPgPcP[PWPOPFG=ROP7PGP_P4P5G2EAX0A,0AX1B,0BX2M,0MP5P?PHPXP@fcRWPLPPPHP;PWPXP9PPE5G?P?fdPQPpPlPhPdP`PIPFG=P_PXPEP8F8PMPNfhR8#<P?PHPWP@P8fbREP\E:PHP4P8PWP5P\E5P?P8P]PQPpPlPhPdP`PFG=P7PWPEP4P5G2EAX0A,0AX1B,0BX2MPFPBPRfgRQ#<P?PHPEP@PQP\PGE:PHP4PQPEP5PGE5P?PQP^P1PqPmPiPePaPFG=PFPEP\P4P5G2EAX0A,0AX1BPDPAPRffRE#<P?PHP\P@PEPGP_E:R@PHPK1HE\RqP5P_D;P?PEP0PsPrPnPjPfPbPFG=/LFRrP\PGPKP5F8EAX0AP:P3P=PRP5P?P@PHPKPqP<P_D;P?PEPrP\PGPKP<F8EAXA3AF3R=P?P2PHPDPvP:PXFPRXP?PC1LOFRFPGP_PDP:F8R_'C1d3=PXP_P4PMPOP?PEP5P\PGPKP<F8X6MP5PF1c6OEZCYCYPVPWEZCKCKCKWGWEP4P5O2n2001000000121000000W5X0AP4P5O2n2001000000121103000W5X1BP4P5O2n2001000000121103000b8W4W3PnPjPfPbPZPDP:P4P5D9D9/4>P?P]PmPiPePaPYPKP<P7P4D9D9P1PsD3PlPhPdP`PIPJP;P9P7D9D9#>P3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUPTn0110100020010000n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101X83P>P4CBPUPN%<GP?PtPHP4PuP5P0D;P?PGPpPlPhPdP`PIPJP;P<D9D9P7P]P^P4P5G2EAX0A,0AX1B,0BX2M=@M5b5W4W3X6MXJ6P4P5O2n10110001020121102100X6MX@6P4P5O2n10110000020121102100X6MX?6P4P5O2n10110000020121102100X6MX76P4P5O2n10110000020121102100X6MX>6P4P5O2n10110000020121102100X6MX=6P4P5O2n10110000020121102100X6MX<6P4P5O2n10110000020021102100X6MX;6P4P5O2n10110000020021102100P5P4O2b3W4W3XBAX9AX:BWIAb?H9eWCWFWDWHo"). Qed.

(* [comment removed for export] *)
Lemma sum_contract_in7_out1 : forall S, n_inputs S = 7%nat -> n_outputs S = 1%nat ->
  (forall a b c d e f g R M rom, spec_pre segs S [a; b; c; d; e; f; g] R M ->
     exists o R' M', msteps segs (mkst R (Z_to_bv 64 (su_entry S)) M rom) (mkst R' (exit_target S R) M' rom)
                     /\ spec_post segs S [a; b; c; d; e; f; g; o] R M R' M') ->
  sum_contract segs S.
Proof.
ltac2:(KReplay.run1 (kr_t_SumSpecs ()) ["Intro"] "p'0h02M'h12R'h24outsh34Hlenh43PREh52H0h61li001lh71eh82e0h91oh:1Mh;1Rh<1ah=1bh>1ch?1dh@1fhA1ghB1ni011nhC3romhD1HhE2HihF2HmhG2HohH2HphI1ShJ3inshK1zi021zi031xp;1p;2p;5p;6p;7p;4p;3g000lj1TTg0027j1ETg002Vj1KTg004<j1GTg004aj1bTg005Fj1RTg005dj1XTg006Gj2_Tg0073j1]Tg007Uj1\Tg0085j55Tg00=Oj5<Tg00:LR0j20Tg00:fR1j1`Tg00;Fj6WTg00<Aj2MTg009@j7JTg00>HR2j2@Tg00>cj2fTg00?=j4[Tg000Nj6dTg00?Xj4NTg00@2j3cTg003bj3ITg00AAj37Tg00Aaj1STg00Blj2QTg00CRj3HTg00DMj2YTg00Dmj3ZTg00;bj2aTg00EJR3f1R4f0R53Ip=Pg00EiR6?745p=1f6R7f5R8f4R9f3R:f2R;A7645576576576576576p=>%S5,Q4p=eP8P91M:;P4P5D<p=3A7645976;976:9769p=6f7R<P7A7689P:P;P4P5FJp=AAH:;4/@5p=91Y64=I35p=41Y65p=;%K59I34p=DP8P9P:P;P4D<=H75p=^P<P7AZ689P:P;P4P5FJp=21@45,@;p=8P3P:P;g00FGP4P5EWp=?10;4/a5p=CP7P8%S:,Q9P;P4D<=H<5p==A76;4=Z65p=OP7P8P9P:P;P4P5FJ,@<p=L%K49I3;/@5p=BP8P9%S;,Q:P4P5D<p=:A7645976;976:p=FP9P:P;P4P5D<9H78p=VAI389AH:;4/@5'@p=Ug00Fc%T5g00Go#ER=#E#E#E#E#E#ER>'P%K4/P=g00HN#GR?#b#R%G?#GR?#G#G#G#RR@#XRA'_RB%R?#X#]\ARAp,4segsR?f<RCf9RDf8REP<P7P8P9%\6RF,1:RGF>P;P4D5P?p,2fxRHP7f@RI,e@RJP8P9D<PHP4PIP7P5P9E3P?PIf=RKPCf;RLf:RMPD11;FRN,1<RO,1ED6P7P8P4P5GAC9X0A,0AX1B,0BX96,06[^CA]:];^A6^@6^76^?6^>6^=6^<6%`6RP%T<,4:P?PEP9P:P;D5P3%TD1475XB3P4P>PEEW148>P1P6145>P?PCP4P<P7D5%;;RQ/DIRRP?PHPLPJPMPDPHP4PIPLP5PDE3F^RJP?PIP8P;PLPMP4P5G238X0A,0AX1B,0BX2P,0P]4]3P7%;FRS/P>P?PLPFP7P8D5PSP3p-0RSP5g00I3RTg00IORUn0110100020010000RVX73P>P4C?PUP?PIPFP;PLPMP4P5G298RJX0A,0AX1B,0BX2P=CP5b5W4W3P1P611;5RJ/4>P?PI11:4RRPLPMD5fDRW,DQRXP?PHf?RYP@PWf>RZPKPHP4PWPYP5PKE3G=R[P?PW11<8R\P;PYPZP4P5G238X0A,0AX1B,0BX2P,0P]4]3P5114FR]/4>P?PYPNPMPDD5%;GP3PSP5PUPVn0110100020010101RVX73P>P4C?PUP?PW11<FR^P;PYPZP4P5G298X[X0A,0AX1B,0BX2P=CP5b5W4W3P1P6117JRJ/4>P?PW11<RRRPYPZD5fHR[,DQRXP?PHfCR_P@P[fBR`fARaPHP4P[P_P5PaE3G=RbP?P[11L\R\P;P_P`P4P5G238X0A,0AX1B,0BX2P,0P]4]3P5118]R]/4>P?P_117NRcPZPKD511<GRd#;P3PSP5PUPVn0110100020010101RVX73P>P4C?PUP?P[11L^R^P;P_P`P4P5G298XbX0A,0AX1B,0BX2P=CP5b5W4W3P1P611MJRJ/4>P?P[11LRRRP_P`D5fLRb,DQRXP?PHfGReP@PbfFRffERgPHP4PbPeP5PgE3G=RhP?Pb11Y\R\P;PePfP4P5G238X0A,0AX1B,0BX2P,0P]4]3P511D]R]/4>P?Pe11McRcP`PaD511LdRd#;P3PSP5PUPVn0110100020010101RVX73P>P4C?PUP?Pb11Y^R^P;PePfP4P5G298XhX0A,0AX1B,0BX2P=CP5b5W4W3P1P611ZJRJ/4>P?Pb11YRRRPePfD5fPRh,DQRXP?PHfKRiP@PhfJRjfIRkPHP4PhPiP5PkE3G=RlP?Ph11_\R\P;PiPjP4P5G238X0A,0AX1B,0BX2P,0P]4]3P511K]R]/4>P?Pi11ZcRcPfPgD511YdRd#;P3PSP5PUPVn0110100020010101RVX73P>P4C?PUP?Ph11_^R^P;PiPjP4P5G298XlX0A,0AX1B,0BX2P=CP5b5W4W3P1P611`JRJ/4>P?Ph11_RRRPiPjD5fTRl,DQRXP?PHfORmP@PlfNRnfMRoPHP4PlPmP5PoE3G=RpP?Pl11e\R\P;PmPnP4P5G238X0A,0AX1B,0BX2P,0P]4]3P511a]R]/4>P?Pm11`cRcPjPkD511_dRd#;P3PSP5PUPVn0110100020010101RVX83P>P4C?PUP?Pl11e^R^P;PmPnP4P5G298XpX0A,0AX1B,0BX2P=CP5b5W4W3P1P611fJRJ/4>P?Pl11eRRRPmPnD5fXRp,DQRXP?PHfSRqP@PpfRRrfQRsPHP4PpPqP5PsE3G=RtP?Pp11i\R\P;PqPrP4P5G238X0A,0AX1B,0BX2P,0P]4]3P511g]R]/4>P?Pq11fcRcPnPoD511ed#;P3PSP5PUPVn0110100020010101X83P>P4C?PUP?Pp11i^P;PqPrP4P5G298XtX0A,0AX1B,0BX2P=CP5b5W4W3P1P611jJ/4>P?Pp11iRPqPrD5f\RRP?PHfWRJP@PRfVR1fURtPHP4PRPJP5PtE3G=RXP?PRAOm\;PJP1P4P5GL5BQX0A,0AX1B,0BX2P,0P]4]3P511k]/4>P?PJ11jcRcPrPsD5PtPiPeP_PYPLP<P:PqPrPsP5O;P?PHP1P@f[R]PtPlE:PHP4P]P1P5PlE3P?P]PnPcP1PtP4P5GAC9X0A,0AX1B,0BX96,06P0P6PXP?PRPmPiPeP_PYPLPOF>PJP1P4P5GLX0A,0AX1B,0BX96f]ROP?PHPpP@POPJP1E:PHP4POPpP5P1E3P?POPhPbP[PWPIPC11EFRXF>P;PpPJP4P5G2C95BQX0A,0AX1B,0BX2P,0PP5P?PHfYRcP@f^R\PpPJE:PHP4P\PcP5PJE3P?P\PsPoPkPgPaPKPDPNF>PcPpP4P5GAC9X0A,0AX1B,0BP0PBP?PHfZRNP@f_R^PcPpE:PHP4P^PNP5PpE3P?P^PrPnPjPfP`PZPMPGF>PNPcP4P5GAC9X0A,0AX1BfaRGP?PHPRP@PGP]PNPHP4PGPRP5PNE3G=RVP?PGPhPbP[PW11CFRd,1ID6=Ol;PRP]P4P5GL5BQX0A,0AX1B,0BX2P,0PP5PVP?PGPlPhPbP[PWPIPCP8PFD6D6PRP]P4P5GLX0A,0AP0PAP?PHPOP@fbR0PRP]E:PHP;P0POP5P]E3P?P0PtPsPoPkPgPaPKP7PFCFD6POPRP;P5GAC9X0AfeRCP?PHf`RVP@PCP^P\E:RuPHP41MCVRvP5P\D<P?PCPpPlPhPbP[PWPIPFCFD6P;PVP^P4P5G2C95BQX0A,0AX1B,0BX2P,0PP5P?PHP^P@fdRwP\POE:PHP9PwP^P5POE3P?PwPJPqPmPiPeP_PYPXF>P^P\P9P5GAC9P2P?PuPHP8PvP4P\FVP?PCPpPlPhPbP[PWPIPDPFCFD6PVP^P8P4GAPQfiRI#KRvP?PHPwP@PIfcRuP0E:R2PHP41MIwRXP5P0D<P?PIPRPpPlPhPbP[PWPFCFD6RWP;PwPuP4P5G2EUX0A,0AX1B,0BX2P,0PP5P?PHP0P@fgR[PGPVPHP<P[P0P:PVE3G=P?fhP]PJPqPmPiPeP_PdF>PuP0PEP9GAPPflR9P?PHP[P@P9ffREPCE:PHP4P9P[P5PCE3P?P9P^P]PJPqPmPiPePFCFD6P;P[PEP4P5G2C95BQX0A,0AX1B,0BX2P11KFRJPB11YFR^#;fkR9P?PHPEP@P9PCPwE:PHP4P9PEP5PwE3P?P9P\PNP1PrPnPjPfPFCFD6P^PEPCP4P5G2C93BX0A,0AX1BPDPA11ZFRE#;R^fjRrP?PHPCP@PrPwPuE:R\PHPM1MrCR9P5PuD<P?PrPcPtPsPoPkPgPFF>=OOEREPCPwPMP5FJC93BX0AP8P3P=P^P5P?P\PHPMP9P7PuD<P?PrPEPCPwPMP7FJEUXB314J=P?P2PHPDPXP8P0FVR0P?PIPWPJPwPuPDP8G2Ru'@1f3=P0PuP4P5C[C[PvP[EdCNCNCNWHWFP4P5O2n2001000000121000000W5X0AP4P5O2n2001000000121103000W5X1BP4P5O2n2001000000121103000W5X96P4P5O2n2001000000121103000b8W4W3PoPkPgPaPKPDP8P4P5D6D6/4>P?P]PnPjPfP`PZPMP7P;P4D6D6P1PtD5PmPiPeP_PYPLP<P:P;D6D6#;P3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUP3PSP5PUPTn0110100020010000n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101n0110100020010101X83P>P4C?PUP?PHP]P@PVPNPcE:PHP4PVP]P5PcE3P?PVPqPmPiPeP_PYPLP<P7D6D6P;P]PNP4P5G2C99BQVX0A,0AX1B,0BX2P=CP5b5W4W3X6PXK6P4P5O2n10110001020121102100X6PXA6P4P5O2n10110000020121102100X6PX@6P4P5O2n10110000020121102100X6PX76P4P5O2n10110000020121102100X6PX?6P4P5O2n10110000020121102100X6PX>6P4P5O2n10110000020121102100X6PX=6P4P5O2n10110000020021102100X6PX<6P4P5O2n10110000020021102100P5P4O2b3W4W3XCAX:AX;BWJAc?H:eWDWGWEWIo"). Qed.

End Intro.

(* [comment removed for export] *)

End SSP.
