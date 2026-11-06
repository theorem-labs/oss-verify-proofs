(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import FunctionalExtensionality.
From Stdlib Require Import ZArith NArith List Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Instr.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import PropExec.
From OSSVerify.Proofs.double_conversion.string_to_double_fuzzer.lib Require Import AxSymExec3 AxSymExec3B AsanPlanCore.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import AX2. Import AX2B. Import APC.
Open Scope Z_scope.

Module RPN.
(* [comment removed for export] *)
Notation "x &&& y" := (if x then y else false) (at level 40, left associativity, only parsing).
Notation "x ||| y" := (if x then true else y) (at level 50, left associativity, only parsing).

(* [comment removed for export] *)
Record rptab : Type := RPT {
  rp_entry : Z;               (* [comment removed for export] *)
  rc_entry : Z; rc_exit : Z;  (* [comment removed for export] *)
  qs_entry : Z; qs_exit : Z;  (* [comment removed for export] *)
  qd_entry : Z; qd_exit : Z;  (* [comment removed for export] *)
  rp_gsb : Z; rp_csb : Z;     (* [comment removed for export] *)
  rp_gm1 : Z; rp_cm1 : Z;     (* [comment removed for export] *)
  rp_gm2 : Z; rp_cm2 : Z;     (* [comment removed for export] *)
  rp_ghi : Z; rp_chi : Z;     (* [comment removed for export] *)
  msb_entry : Z; msb_exit : Z; (* [comment removed for export] *)
  ls_entry : Z; ls_exit : Z;   (* [comment removed for export] *)
  mv_entry : Z; mv_exit : Z    (* [comment removed for export] *)
}.
(* [comment removed for export] *)
Definition RP_ASAN : rptab := RPT 0x77fe8 0x62b84 0x62bdc 0x75a2c 0x75a64 0x75a74 0x75aac 0x129ea8 0x132278 0x129eb0 0x132f68 0x129eb8 0x132f70 0x129ec0 0x132f60 0x548e4 0x5498c 0x549d0 0x549f0 0x890ac 0x8911c.
Definition RP_BOTH : rptab := RPT 0x7812c 0x62cc8 0x62d20 0x75b70 0x75ba8 0x75bb8 0x75bf0 0x12a380 0x132738 0x12a388 0x133428 0x12a390 0x133430 0x12a398 0x133420 0x54a28 0x54ad0 0x54b14 0x54b34 0x891f0 0x89260.

Definition SB : Z := 0x7fff8000.
Definition kLowEnd : Z := 0x7fff7fff.
Definition kHighBeg : Z := 0x10007fff8000.
Definition kHighEnd : Z := 0x7fffffffffff.

(* [comment removed for export] *)
Definition side_ok (k : list kentry) (beg ne : expr) (blo bhi nhi : Z) : bool :=
  (Z.leb (bhi + nhi) kLowEnd ||| (Z.leb kHighBeg blo &&& Z.leb (bhi + nhi) kHighEnd))
  ||| (Z.leb bhi (2 ^ 47) &&& Z.leb nhi (2 ^ 47)
      &&& ranges_apart_x k beg 0 ne (ELit kLowEnd) 0 (ELit (kHighBeg - kLowEnd))
      &&& (Z.leb (bhi + nhi) kHighEnd
          ||| match base_range k beg with
             | Some (lo1, hi1) => match end_hi k beg 0 ne lo1 hi1 nhi with Some e => Z.leb e kHighEnd | None => false end
             | None => false
             end)).

(* [comment removed for export] *)
Definition msb_regs (r18_0 w : word) : word * word * word * word * word :=
  let r11_1 := v_srli r18_0 1 in   (* [comment removed for export] *)
  let r12_1 := v_lui 1431654400 in   (* [comment removed for export] *)
  let r14_1 := v_lui 858992640 in   (* [comment removed for export] *)
  let r15_1 := v_lui 252645376 in   (* [comment removed for export] *)
  let r11_2 := v_or r18_0 r11_1 in   (* [comment removed for export] *)
  let r12_2 := v_addiw r12_1 (1365) in   (* [comment removed for export] *)
  let r14_2 := v_addiw r14_1 (819) in   (* [comment removed for export] *)
  let r15_2 := v_addiw r15_1 (-241) in   (* [comment removed for export] *)
  let r16_1 := v_srli r11_2 2 in   (* [comment removed for export] *)
  let r11_3 := v_or r11_2 r16_1 in   (* [comment removed for export] *)
  let r16_2 := v_slli r12_2 32 in   (* [comment removed for export] *)
  let r12_3 := v_add r12_2 r16_2 in   (* [comment removed for export] *)
  let r16_3 := v_slli r14_2 32 in   (* [comment removed for export] *)
  let r14_3 := v_add r14_2 r16_3 in   (* [comment removed for export] *)
  let r16_4 := v_slli r15_2 32 in   (* [comment removed for export] *)
  let r15_3 := v_add r15_2 r16_4 in   (* [comment removed for export] *)
  let r16_5 := v_srli r11_3 4 in   (* [comment removed for export] *)
  let r11_4 := v_or r11_3 r16_5 in   (* [comment removed for export] *)
  let r16_6 := v_srli r11_4 8 in   (* [comment removed for export] *)
  let r11_5 := v_or r11_4 r16_6 in   (* [comment removed for export] *)
  let r16_7 := v_srli r11_5 16 in   (* [comment removed for export] *)
  let r11_6 := v_or r11_5 r16_7 in   (* [comment removed for export] *)
  let r16_8 := v_srli r11_6 32 in   (* [comment removed for export] *)
  let r11_7 := v_or r11_6 r16_8 in   (* [comment removed for export] *)
  let r11_8 := v_xori r11_7 (-1) in   (* [comment removed for export] *)
  let r16_9 := v_srli r11_8 1 in   (* [comment removed for export] *)
  let r12_4 := v_and r16_9 r12_3 in   (* [comment removed for export] *)
  let r16_10 := v_lui 16842752 in   (* [comment removed for export] *)
  let r11_9 := v_sub r11_8 r12_4 in   (* [comment removed for export] *)
  let r12_5 := v_srli r11_9 2 in   (* [comment removed for export] *)
  let r11_10 := v_and r11_9 r14_3 in   (* [comment removed for export] *)
  let r12_6 := v_and r12_5 r14_3 in   (* [comment removed for export] *)
  let r14_4 := w in   (* [comment removed for export] *)
  let r16_11 := v_addiw r16_10 (257) in   (* [comment removed for export] *)
  let r11_11 := v_add r11_10 r12_6 in   (* [comment removed for export] *)
  let r12_7 := v_srli r11_11 4 in   (* [comment removed for export] *)
  let r11_12 := v_add r11_11 r12_7 in   (* [comment removed for export] *)
  let r12_8 := v_slli r16_11 32 in   (* [comment removed for export] *)
  let r11_13 := v_and r11_12 r15_3 in   (* [comment removed for export] *)
  let r12_9 := v_add r16_11 r12_8 in   (* [comment removed for export] *)
  let r11_14 := v_mul r11_13 r12_9 in   (* [comment removed for export] *)
  let r19_1 := v_srli r11_14 56 in   (* [comment removed for export] *)
  (r11_14, r12_9, r15_3, r16_11, r19_1).
Definition msb_res (x w : word) : word := snd (msb_regs x w).

Definition msb_val (x : Z) : Z := bv_unsigned (msb_res (Z_to_bv 64 x) (Z_to_bv 64 0)).
Fixpoint msb_scan (m : Z) (n : nat) (acc : Z * Z) : Z * Z :=
  match n with
  | O => acc
  | S n' => let v := msb_val (4096 * m) in msb_scan (m + 1) n' (Z.min (fst acc) v, Z.max (snd acc) v)
  end.
(* [comment removed for export] *)
Definition msb_range (lo hi : Z) : option (Z * Z) :=
  let m0 := (lo + 4095) / 4096 in let m1 := hi / 4096 in
  if (Z.leb 1 lo &&& Z.leb m0 m1 &&& Z.leb (m1 - m0) 32768)%Z%bool then
    let v0 := msb_val (4096 * m0) in Some (msb_scan (m0 + 1) (Z.to_nat (m1 - m0)) (v0, v0))
  else None.
(* [comment removed for export] *)
Definition msb_rangeF (lo hi : Z) : option (Z * Z) :=
  let m0 := (lo + 4095) / 4096 in let m1 := hi / 4096 in
  if (Z.leb 1 lo &&& Z.leb m0 m1 &&& Z.leb (m1 - m0) 32768 &&& Z.ltb hi (2 ^ 64))%Z%bool then
    Some (63 - Z.log2 (4096 * m1), 63 - Z.log2 (4096 * m0))
  else None.


Section WithSegs.
Variable segs : list Segment.
Variable A : atable.   (* [comment removed for export] *)
Variable nx0 : nat.
Variable T : rptab.

(* [comment removed for export] *)
Definition lit_cell (k : list kentry) (cell v : Z) : bool :=
  flat_x k (ELit 0) cell (ELit 8) &&&
  match know_lookup segs k (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, erange k e with [], Some (lo, hi) => Z.eqb lo v &&& Z.eqb hi v | _, _ => false end
  | _ => false
  end.
(* [comment removed for export] *)
Definition img8 (k : list kentry) (a : Z) : bool := img_cov k a (a + 8).

(* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition and7_of (k : list kentry) (m ne : expr) : bool :=
  (expr_eqb m (mkAnd k ne (ELit 7))
   ||| match m with
       | EAlu ALU_AND ne' (ELit 7) => lin_ge0 k [(ne', 0)] [(ne, 0)] &&& lin_ge0 k [(ne, 0)] [(ne', 0)]
       | _ => false
       end)%bool.
Definition vshape0 (k : list kentry) (v ne : expr) : bool :=
  match v with
  | EAlu ALU_ADD m1 (EMd M_MUL (ELit 250) (EAlu ALU_SLTU m2 (ELit 1))) => (expr_eqb m1 m2 &&& and7_of k m1 ne)%bool
  | _ => false
  end.
Definition vshape (k : list kentry) (v ne : expr) : bool :=
  (vshape0 k v ne ||| match v with EExt false 0%nat 1%nat v' => vshape0 k v' ne | _ => false end)%bool.
Definition partial_val_ok (k : list kentry) (v ne : expr) : bool :=
  (expr_eqb v (mkAlu ALU_AND ne (ELit 7)) ||| expr_eqb v (mkExt false 0 1 (mkAlu ALU_AND ne (ELit 7)))
   ||| expr_eqb v (mkAnd k ne (ELit 7)) ||| expr_eqb v (mkExt false 0 1 (mkAnd k ne (ELit 7)))
   ||| (expr_eqb v ne &&& match erange k ne with Some (lo, hi) => (0 <=? lo) &&& (hi <=? 7) | None => false end)
   ||| (expr_eqb v (mkExt false 0 1 ne) &&& match erange k ne with Some (lo, hi) => (0 <=? lo) &&& (hi <=? 7) | None => false end)
   ||| vshape k v ne)%bool.   (* [comment removed for export] *)
Definition is00 (r : option (Z * Z)) : bool := match r with Some (0, 0) => true | _ => false end.
Definition sym_shadow_ok (k : list kentry) (beg ne : expr) : bool :=
  let sbe := mkAlu ALU_ADD (mkSrl k beg 3) (ELit SB) in
  let '(sb, sk) := split_lit sbe in
  let ng := mkSrl k ne 3 in
  let g0 := is00 (erange k ng) in                      (* [comment removed for export] *)
  let pb := if g0 then sb else mkAlu ALU_ADD sb ng in   (* [comment removed for export] *)
  (Z.leb 3 (ealign k beg) &&& (g0 ||| kzero_x k k sb sk ng)
   &&& (is00 (erange k (mkAlu ALU_AND ne (ELit 7)))
       ||| (flat_x k pb sk (ELit 1) &&&
           match know_lookup segs k pb sk 1 false [] [] with
           | LHit v [] _ => partial_val_ok k v ne
           | _ => false
           end)))%bool.

(* [comment removed for export] *)
Definition and7_ofB (bc : bctx) (m ne : expr) : bool :=
  (expr_eqb m (mkAndB bc ne (ELit 7))
   ||| match m with
       | EAlu ALU_AND ne' (ELit 7) => lin_ge0B bc [(ne', 0)] [(ne, 0)] &&& lin_ge0B bc [(ne, 0)] [(ne', 0)]
       | _ => false
       end)%bool.
Lemma and7_ofB_eqf : forall fk, and7_ofB (mkbc fk) = and7_of fk.
Proof. intros. bcfe. unfold and7_ofB, and7_of. autorewrite with bceq. reflexivity. Qed.
Definition vshape0B (bc : bctx) (v ne : expr) : bool :=
  match v with
  | EAlu ALU_ADD m1 (EMd M_MUL (ELit 250) (EAlu ALU_SLTU m2 (ELit 1))) => (expr_eqb m1 m2 &&& and7_ofB bc m1 ne)%bool
  | _ => false
  end.
Lemma vshape0B_eqf : forall fk, vshape0B (mkbc fk) = vshape0 fk.
Proof. intros. bcfe. unfold vshape0B, vshape0. rewrite and7_ofB_eqf. reflexivity. Qed.
Definition vshapeB (bc : bctx) (v ne : expr) : bool :=
  (vshape0B bc v ne ||| match v with EExt false 0%nat 1%nat v' => vshape0B bc v' ne | _ => false end)%bool.
Lemma vshapeB_eqf : forall fk, vshapeB (mkbc fk) = vshape fk.
Proof. intros. bcfe. unfold vshapeB, vshape. rewrite vshape0B_eqf. reflexivity. Qed.
Definition partial_val_okB (bc : bctx) (v ne : expr) : bool :=
  (expr_eqb v (mkAlu ALU_AND ne (ELit 7)) ||| expr_eqb v (mkExt false 0 1 (mkAlu ALU_AND ne (ELit 7)))
   ||| expr_eqb v (mkAndB bc ne (ELit 7)) ||| expr_eqb v (mkExt false 0 1 (mkAndB bc ne (ELit 7)))
   ||| (expr_eqb v ne &&& match erangeB bc ne with Some (lo, hi) => (0 <=? lo) &&& (hi <=? 7) | None => false end)
   ||| (expr_eqb v (mkExt false 0 1 ne) &&& match erangeB bc ne with Some (lo, hi) => (0 <=? lo) &&& (hi <=? 7) | None => false end)
   ||| vshapeB bc v ne)%bool.
Lemma partial_val_okB_eqf : forall fk, partial_val_okB (mkbc fk) = partial_val_ok fk.
Proof. intros. bcfe. unfold partial_val_okB, partial_val_ok. rewrite vshapeB_eqf. autorewrite with bceq. reflexivity. Qed.
Definition sym_shadow_okB (bc : bctx) (beg ne : expr) : bool :=
  let sbe := mkAlu ALU_ADD (mkSrlB bc beg 3) (ELit SB) in
  let '(sb, sk) := split_lit sbe in
  let ng := mkSrlB bc ne 3 in
  let g0 := is00 (erangeB bc ng) in
  let pb := if g0 then sb else mkAlu ALU_ADD sb ng in
  (Z.leb 3 (ealignB bc beg) &&& (g0 ||| kzero_xB bc (bc_fk bc) sb sk ng)
   &&& (is00 (erangeB bc (mkAlu ALU_AND ne (ELit 7)))
       ||| (flat_xB bc pb sk (ELit 1) &&&
           match know_lookupB segs bc pb sk 1 false [] [] with
           | LHit v [] _ => partial_val_okB bc v ne
           | _ => false
           end)))%bool.
Lemma sym_shadow_okB_eqf : forall fk, sym_shadow_okB (mkbc fk) = sym_shadow_ok fk.
Proof.
  intros. bcfe. unfold sym_shadow_okB, sym_shadow_ok. cbn [bc_fk mkbc mkbc0].
  rewrite ?partial_val_okB_eqf, ?kzero_xB_eqf, ?flat_xB_eqf. autorewrite with bceq. reflexivity.
Qed.

(* [comment removed for export] *)
Definition enc_ok (k : list kentry) (beg ne : expr) (nhi : Z) (eb : expr) (ek elen : Z) : bool :=
  let d := mkAlu ALU_SUB beg (eaddz eb ek) in
  match erange k d with
  | Some (dlo, dhi) =>
      ((0 <=? dlo) &&& (0 <=? elen) &&& (elen <=? 2 ^ 40) &&& flat_x k eb ek (ELit elen)
       &&& ((dhi + nhi <=? elen)
           (* [comment removed for export] *)
           ||| ((dhi + nhi <? two64)
               &&& match erange k (mkAlu ALU_ADD d ne) with Some (_, thi) => thi <=? elen | None => false end)))%bool
  | None => false
  end.

(* [comment removed for export] *)
Definition lin_eqb (a b : expr) : bool := expr_eqb (unlin (lin_of a)) (unlin (lin_of b)).
Definition rpiece (K : kentry) : option (expr * Z * expr) :=
  match K with
  | KZero (SA b o) l | KFill (SA b o) l _ | KUnk (SA b o) l | KBlob (SA b o) l _ => Some (b, o, l)
  | KWord (SA b o) w _ => Some (b, o, ELit (Z.of_nat w))
  | _ => None
  end.
Fixpoint chain_go (fuel : nat) (ps : list (expr * Z * expr)) (cur : expr) : expr :=
  match fuel with
  | O => cur
  | S f =>
    match find (fun p => lin_eqb (eaddz (fst (fst p)) (snd (fst p))) cur) ps with
    | Some (b, o, l) => chain_go f ps (mkAlu ALU_ADD (eaddz b o) l)
    | None => cur
    end
  end.
(* [comment removed for export] *)
Definition chain_reached (start : expr) (minlen : Z) (cur : expr) : bool :=
  match lin_of (mkAlu ALU_SUB cur start) with
  | (d, []) => Z.leb minlen d
  | _ => false
  end.
Fixpoint chain_go_s (fuel : nat) (ps : list (expr * Z * expr)) (start : expr) (minlen : Z) (cur : expr) : expr :=
  match fuel with
  | O => cur
  | S f =>
    if chain_reached start minlen cur then cur else
    match find (fun p => lin_eqb (eaddz (fst (fst p)) (snd (fst p))) cur) ps with
    | Some (b, o, l) => chain_go_s f ps start minlen (mkAlu ALU_ADD (eaddz b o) l)
    | None => cur
    end
  end.
Definition kchain (k : list kentry) (b : expr) (off : Z) (minlen : Z) : bool :=
  let ps := flat_map (fun K => match rpiece K with Some p => [p] | None => [] end) k in
  let cur := chain_go_s (length ps) ps (eaddz b off) minlen (eaddz b off) in
  match lin_of (mkAlu ALU_SUB cur (eaddz b off)) with
  | (d, []) => ((minlen <=? d) &&& (d <? 2 ^ 62) &&& (0 <=? minlen))%bool
  | _ => false
  end.

(* [comment removed for export] *)
Definition shsplit (k : list kentry) (bb : expr) (bk : Z) : expr * Z := split_lit (eadd (ELit (SB + bk / 8)) (mkSrl k bb 3)).
(* [comment removed for export] *)
Definition ngran (bk len : Z) : Z := (bk + len - 1) / 8 - bk / 8 + 1.
(* [comment removed for export] *)
Definition lit_shadow_zero (k : list kentry) (bb : expr) (bk len : Z) : bool :=
  let '(hb, hk) := shsplit k bb bk in
  (Z.leb 3 (ealign k bb) &&& flat_x k bb bk (ELit 1)
   &&& flat_x k hb hk (ELit (ngran bk len)) &&& kzero_x k k hb hk (ELit (ngran bk len)))%bool.
(* [comment removed for export] *)
Definition lin_gcd (l : lin) : Z := fold_right (fun t g => Z.gcd (fst t) g) (fst l) (snd l).
Definition lin_align (e : expr) : Z := ctz64 (lin_gcd (lin_of e)).
(* [comment removed for export] *)
Definition window_cover_ref (k : list kentry) (hb : expr) (hk ng : Z) : bool :=
  existsb (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideL k hb (hk - 7) (ELit (ng + 14)) b o l then true
                        else (xinsideL k hb (hk - 7) (ELit (ng + 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Definition window_cover (k : list kentry) (hb : expr) (hk ng : Z) : bool :=
  let bc := mkbc k in   (* [comment removed for export] *)
  existsb_sc (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideLB bc hb (hk - 7) (ELit (ng + 14)) b o l then true
                        else (xinsideLB bc hb (hk - 7) (ELit (ng + 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Lemma window_cover_eq : forall k hb hk ng, window_cover k hb hk ng = window_cover_ref k hb hk ng.
Proof. intros. unfold window_cover, window_cover_ref. cbv zeta. rewrite existsb_sc_eq, xinsideLB_eqf. reflexivity. Qed.
(* [comment removed for export] *)
Definition shadow_window_ok (k : list kentry) (bb : expr) (bk len : Z) : bool :=
  let '(hb, hk) := shsplit k bb bk in
  let ng := ngran bk len in
  let w0 := hk - hk mod 8 in
  let w1 := (hk + ng - 1) - (hk + ng - 1) mod 8 + 8 in
  (Z.leb 3 (ealign k bb) &&& flat_x k bb bk (ELit 1)
   &&& (if (Z.leb 3 (ealign k hb) &&& flat_x k hb w0 (ELit (w1 - w0)) &&& kchain k hb w0 (w1 - w0))%bool then true
       else window_cover k hb hk ng))%bool.

(* [comment removed for export] *)
Definition ushadow (k : list kentry) (beg : expr) : expr * Z := split_lit (mkAlu ALU_ADD (mkSrl k beg 3) (ELit SB)).
Definition ugran (nhi : Z) : Z := (nhi - 1) / 8 + 2.
Definition ushadow_zero (k : list kentry) (beg : expr) (nhi : Z) : bool :=
  let '(sb, sk) := ushadow k beg in
  (flat_x k sb sk (ELit (ugran nhi)) &&& kzero_x k k sb sk (ELit (ugran nhi)))%bool.
(* [comment removed for export] *)
Definition ugran_sym (k : list kentry) (beg ne : expr) : expr :=
  mkAlu ALU_ADD (mkAlu ALU_SUB (mkSrl k (mkAlu ALU_ADD beg (mkAlu ALU_ADD ne (ELit (-1)))) 3) (mkSrl k beg 3)) (ELit 1).
Definition ushadow_zero_sym (k : list kentry) (beg ne : expr) : bool :=
  let '(sb, sk) := ushadow k beg in
  let G := ugran_sym k beg ne in
  (flat_x k sb sk G &&& kzero_x k k sb sk G)%bool.
(* [comment removed for export] *)
Definition ushadow_window (k : list kentry) (beg : expr) (nhi : Z) : bool :=
  let '(sb, sk) := ushadow k beg in
  (flat_x k sb sk (ELit (ugran nhi)) &&& window_cover k sb sk (ugran nhi))%bool.
(* [comment removed for export] *)
Definition window_cover_x_ref (k : list kentry) (hb : expr) (hk : Z) (ng : expr) : bool :=
  existsb (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideL k hb (hk - 7) (mkAlu ALU_ADD ng (ELit 14)) b o l then true
                        else (xinsideL k hb (hk - 7) (mkAlu ALU_ADD ng (ELit 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Definition window_cover_x (k : list kentry) (hb : expr) (hk : Z) (ng : expr) : bool :=
  let bc := mkbc k in   (* [comment removed for export] *)
  existsb_sc (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideLB bc hb (hk - 7) (mkAlu ALU_ADD ng (ELit 14)) b o l then true
                        else (xinsideLB bc hb (hk - 7) (mkAlu ALU_ADD ng (ELit 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Lemma window_cover_x_eq : forall k hb hk ng, window_cover_x k hb hk ng = window_cover_x_ref k hb hk ng.
Proof. intros. unfold window_cover_x, window_cover_x_ref. cbv zeta. rewrite existsb_sc_eq, xinsideLB_eqf. reflexivity. Qed.
(* [comment removed for export] *)
Definition ushadow_window_sym (k : list kentry) (beg ne : expr) : bool :=
  let '(sb, sk) := ushadow k beg in
  let G := ugran_sym k beg ne in
  (flat_x k sb sk G &&& window_cover_x k sb sk G)%bool.

(* [comment removed for export] *)
Definition region_shadow_ok (k : list kentry) (args : list expr) (beg ne : expr) (nhi : Z) : bool :=
  let '(bb, bk) := split_lit beg in
  match args with
  | [] => lit_shadow_zero k bb bk nhi ||| sym_shadow_ok k beg ne ||| ushadow_zero k beg nhi ||| ushadow_zero_sym k beg ne
  | [ebase; ELit elen] =>
      let '(eb, ek) := split_lit ebase in
      enc_ok k beg ne nhi eb ek elen &&& lit_shadow_zero k eb ek elen
  | _ => false
  end%bool.
(* [comment removed for export] *)
Definition region_window_ok (k : list kentry) (args : list expr) (beg ne : expr) (nhi : Z) : bool :=
  let '(bb, bk) := split_lit beg in
  match args with
  | [] => shadow_window_ok k bb bk nhi ||| ushadow_window k beg nhi ||| ushadow_window_sym k beg ne
  | [ebase; ELit elen] => let '(eb, ek) := split_lit ebase in shadow_window_ok k eb ek elen
  | _ => false
  end%bool.

Definition node_rpoison_v2 (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    (* [comment removed for export] *)
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (mkSrl k bb 3)) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      if (Z.leb 16 nlo &&& Z.leb nhi (2 ^ 40)
          &&& side_ok k beg ne blo bhi nhi
          &&& Z.leb 3 (ealign k bb) &&& flat_x k bb bk (ELit 1)
          &&& Z.leb 80 splo &&& Z.ltb sphi two64
          &&& Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          &&& Z.leb (rp_chi T + 8) (splo - 72) &&& Z.leb (rp_cm2 T + 8) (splo - 72) &&& Z.leb (rp_cm1 T + 8) (splo - 72)
          &&& Z.leb (rp_csb T + 8) (splo - 72) &&& Z.leb (rp_ghi T + 8) (splo - 72) &&& Z.leb (rp_gm2 T + 8) (splo - 72)
          &&& Z.leb (rp_gm1 T + 8) (splo - 72) &&& Z.leb (rp_gsb T + 8) (splo - 72)
          &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_gm1 T) &&& Z.leb 0 (rp_gm2 T) &&& Z.leb 0 (rp_ghi T)
          &&& Z.leb 0 (rp_csb T) &&& Z.leb 0 (rp_cm1 T) &&& Z.leb 0 (rp_cm2 T) &&& Z.leb 0 (rp_chi T)
          &&& kwritable A k k qb qk 72 &&& flat_x k qb qk (ELit 72)
          &&& flat_x k hb hk (ELit L) &&& kzero_x k k hb hk (ELit L)
          &&& img8 k (rp_gsb T) &&& img8 k (rp_gm1 T) &&& img8 k (rp_gm2 T) &&& img8 k (rp_ghi T)
          &&& img8 k (rp_cm1 T) &&& img8 k (rp_cm2 T)
          &&& lit_cell k (rp_csb T) SB &&& lit_cell k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_rpoison (args : list expr) (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      if (Z.leb 16 nlo &&& Z.leb nhi (2 ^ 40)
          &&& side_ok k beg ne blo bhi nhi
          &&& Z.leb 80 splo &&& Z.ltb sphi two64
          &&& Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          &&& Z.leb (rp_chi T + 8) (splo - 72) &&& Z.leb (rp_cm2 T + 8) (splo - 72) &&& Z.leb (rp_cm1 T + 8) (splo - 72)
          &&& Z.leb (rp_csb T + 8) (splo - 72) &&& Z.leb (rp_ghi T + 8) (splo - 72) &&& Z.leb (rp_gm2 T + 8) (splo - 72)
          &&& Z.leb (rp_gm1 T + 8) (splo - 72) &&& Z.leb (rp_gsb T + 8) (splo - 72)
          &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_gm1 T) &&& Z.leb 0 (rp_gm2 T) &&& Z.leb 0 (rp_ghi T)
          &&& Z.leb 0 (rp_csb T) &&& Z.leb 0 (rp_cm1 T) &&& Z.leb 0 (rp_cm2 T) &&& Z.leb 0 (rp_chi T)
          &&& kwritable A k k qb qk 72 &&& flat_x k qb qk (ELit 72)
          &&& region_shadow_ok k args beg ne nhi
          &&& img8 k (rp_gsb T) &&& img8 k (rp_gm1 T) &&& img8 k (rp_gm2 T) &&& img8 k (rp_ghi T)
          &&& img8 k (rp_cm1 T) &&& img8 k (rp_cm2 T)
          &&& lit_cell k (rp_csb T) SB &&& lit_cell k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havoc k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.

(* [comment removed for export] *)
Definition node_quick (qe qx : Z) (rb rs : nat) (args : list expr) (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) qe) then None else
  let beg := reg cs rb in let ne := reg cs 12 in
  if negb (expr_eqb (reg cs rs) (mkAlu ALU_ADD beg ne)) then None else
  match xlo k ne, xhi k ne, xhi k beg with
  | Some nlo, Some nhi, Some bhi =>
    if (Z.leb 1 nlo &&& Z.leb nhi 64 &&& Z.ltb (bhi + 64) two64
        &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_csb T) &&& img8 k (rp_gsb T) &&& lit_cell k (rp_csb T) SB
        &&& region_shadow_ok k args beg ne nhi &&& region_window_ok k args beg ne nhi
        &&& fresh_ok nx0 cs)%bool
    then match node_havoc nx0 cs [13; 14; 15; 16; 17]%nat with
         | Some cs1 => Some (with_ss cs1 (mk_ss qx (sr_upd (s_regs (a_ss cs1)) rs (eaddz (mkAlu ALU_ADD beg ne) (-1))) (kn cs1) (nxt cs1)))
         | None => None
         end
    else None
  | _, _, _ => None
  end.
Definition node_quick_src (args : list expr) (cs : acs) : option acs := node_quick (qs_entry T) (qs_exit T) 11 19 args cs.
Definition node_quick_dst (args : list expr) (cs : acs) : option acs := node_quick (qd_entry T) (qd_exit T) 10 20 args cs.

(* [comment removed for export] *)
Definition rc_regs (sr : list expr) (e1 e2 e3 e20 : expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 11 e1) 12 e2) 13 e3) 14 (ELit 0)) 15 (ELit 0)) 20 e20.
Definition node_readcheck (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rc_entry T)) then None else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrl k bb 3)) in
  match xlo k re, xhi k re, xhi k dst with
  | Some rlo, Some rhi, Some dhi =>
    if (Z.leb 1 rlo &&& Z.leb rhi 64 &&& Z.ltb (dhi + 64) two64 &&& Z.leb 6 (ealign k bb) &&& flat_x k bb bk (ELit 1)
        &&& fresh_ok nx0 cs
        &&& flat_x k hb hk (ELit 16) &&& kzero_x k k hb hk (ELit 16)
        &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_csb T) &&& img8 k (rp_gsb T) &&& lit_cell k (rp_csb T) SB)%bool
    then
      let e1 := eadd (ELit (SB + bk / 8)) (mkSrl k bb 3) in
      let e3 := eaddz (eadd dst re) (-1) in
      let e2 := eadd (ELit SB) (mkSrl k e3 3) in
      let e20 := eaddz (eaddz (reg cs 8) (-2048)) (-72) in
      Some (with_ss cs (mk_ss (rc_exit T) (rc_regs (s_regs (a_ss cs)) e1 e2 e3 e20) k (nxt cs)))
    else None
  | _, _, _ => None
  end.

(* [comment removed for export] *)
Definition MSBR : list nat := [11; 12; 15; 16; 19]%nat.
Definition node_msb (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (msb_entry T)) then None else
  match reg cs 9, erange k (reg cs 18) with
  | ELit s1, Some (lo, hi) =>
      let s := s1 mod two64 in
      match kreadZ segs k (ELit 0) (s + 48) 8, msb_rangeF lo hi with
      | Some nres, Some (cmin, cmax) =>
          if (Z.leb 12 (ealign k (reg cs 18)) &&& Z.leb 0 s &&& Z.ltb (s + 56) two64 &&& flat_x k (ELit 0) (s + 48) (ELit 8)
              &&& fresh_ok nx0 cs)%bool then
            match node_havoc nx0 cs MSBR with
            | Some cs1 => Some (with_ss cs1 (mk_ss (msb_exit T) (sr_upd (s_regs (a_ss cs1)) 14 (ELit nres))
                                                 (KRange (EVar (nxt cs + 4)%nat) cmin cmax :: kn cs1) (nxt cs1)))
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.

(* [comment removed for export] *)
Definition in63 (k : list kentry) (e : expr) : bool :=
  match erange k e with Some (lo, hi) => (Z.leb 0 lo &&& Z.leb hi 63)%bool | None => false end.
Definition idx_ok (k : list kentry) (e : expr) : bool :=
  match e with
  | EAlu ALU_XOR e' (ELit z) => if Z.eqb z 63 then in63 k e' else in63 k e
  | _ => in63 k e
  end.
Definition LSR : list nat := [11; 12; 13]%nat.
Definition node_largestats (cs : acs) : option acs :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (ls_entry T)) then None else
  match reg cs 9 with
  | ELit s1 =>
      let s := s1 mod two64 in
      if (idx_ok k (reg cs 11) &&& Z.leb 0 s &&& Z.ltb (s + 616) two64
          &&& kwritable A k k (ELit 0) (s + 96) 520 &&& flat_x k (ELit 0) (s + 96) (ELit 520) &&& fresh_ok nx0 cs)%bool then
        match node_havoc nx0 cs LSR with
        | Some cs1 => Some (with_ss cs1 (mk_ss (ls_exit T) (s_regs (a_ss cs1)) (kn_havoc (kn cs1) (ELit 0) (s + 96) (ELit 520)) (nxt cs1)))
        | None => None
        end
      else None
  | _ => None
  end.

(* [comment removed for export] *)
Fixpoint first_false (i : nat) (l : list bool) : nat :=
  match l with [] => 0 | b :: l' => if b then first_false (S i) l' else i end.
Definition diag_rpoison (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rp_entry T)) then 100%nat else
  match ret_lit cs with
  | None => 101%nat
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (mkSrl k bb 3)) in
    match xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      first_false 1 [Z.leb 16 nlo; Z.leb nhi (2 ^ 40);
        side_ok k beg ne blo bhi nhi;
        Z.leb 3 (ealign k bb); flat_x k bb bk (ELit 1); Z.leb 80 splo; Z.ltb sphi two64;
        Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72); Z.leb (rp_chi T + 8) (splo - 72);
        kwritable A k k qb qk 72; flat_x k qb qk (ELit 72); flat_x k hb hk (ELit L); kzero_x k k hb hk (ELit L);
        img8 k (rp_gsb T); img8 k (rp_gm1 T); img8 k (rp_gm2 T); img8 k (rp_ghi T); img8 k (rp_cm1 T); img8 k (rp_cm2 T);
        lit_cell k (rp_csb T) SB; lit_cell k (rp_chi T) kHighEnd; fresh_ok nx0 cs]%bool
    | _, _, _, _, _, _ => 102%nat
    end
  end.
Definition diag_readcheck (cs : acs) : nat :=
  let k := kn cs in
  if negb (Z.eqb (pc cs) (rc_entry T)) then 100%nat else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrl k bb 3)) in
  match xlo k re, xhi k re, xhi k dst with
  | Some rlo, Some rhi, Some dhi =>
      first_false 1 [Z.leb 1 rlo; Z.leb rhi 64; Z.ltb (dhi + 64) two64; Z.leb 6 (ealign k bb); flat_x k bb bk (ELit 1);
        fresh_ok nx0 cs; flat_x k hb hk (ELit 16); kzero_x k k hb hk (ELit 16); img8 k (rp_gsb T); lit_cell k (rp_csb T) SB]%bool
  | _, _, _ => 102%nat
  end.

(* [comment removed for export] *)
Definition diag_rpoison3 (args : list expr) (cs : acs) : list (nat * bool) :=
  let k := kn cs in
  let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
  let '(qb, qk) := split_lit (eaddz sp (-72)) in
  let '(bb, bk) := split_lit beg in
  match ret_lit cs, xlo k ne, xhi k ne, xlo k beg, xhi k beg, xlo k sp, xhi k sp with
  | Some _, Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      combine (seq 1 24)
      [Z.eqb (pc cs) (rp_entry T); Z.leb 16 nlo; Z.leb nhi (2 ^ 40);
       side_ok k beg ne blo bhi nhi;
       Z.leb 80 splo; Z.ltb sphi two64; Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72); Z.leb (rp_chi T + 8) (splo - 72);
       kwritable A k k qb qk 72; flat_x k qb qk (ELit 72);
       region_shadow_ok k args beg ne nhi; lit_shadow_zero k bb bk nhi; sym_shadow_ok k beg ne;
       img8 k (rp_gsb T) &&& img8 k (rp_gm1 T) &&& img8 k (rp_gm2 T) &&& img8 k (rp_ghi T) &&& img8 k (rp_cm1 T) &&& img8 k (rp_cm2 T);
       lit_cell k (rp_csb T) SB; lit_cell k (rp_chi T) kHighEnd; fresh_ok nx0 cs; ushadow_zero k beg nhi; ushadow_zero_sym k beg ne]%bool   (* [comment removed for export] *)
  | _, _, _, _, _, _, _ => [(0%nat, false)]
  end.
(* [comment removed for export] *)
Definition diag_sym (cs : acs) (beg ne : expr) : expr * Z * expr * bool * option (Z * Z) * bool * option (Z * Z) * bool * lres :=
  let k := kn cs in
  let sbe := mkAlu ALU_ADD (mkSrl k beg 3) (ELit SB) in
  let '(sb, sk) := split_lit sbe in
  let ng := mkSrl k ne 3 in
  let g0 := is00 (erange k ng) in
  let pb := if g0 then sb else mkAlu ALU_ADD sb ng in
  (sb, sk, ng, Z.leb 3 (ealign k beg), erange k ng, kzero_x k k sb sk ng, erange k (mkAlu ALU_AND ne (ELit 7)),
   flat_x k pb sk (ELit 1), know_lookup segs k pb sk 1 false [] []).
Definition diag_quick (qe : Z) (rb rs : nat) (args : list expr) (cs : acs) : list (nat * bool) :=
  let k := kn cs in
  let beg := reg cs rb in let ne := reg cs 12 in
  let '(bb, bk) := split_lit beg in
  match xlo k ne, xhi k ne, xhi k beg with
  | Some nlo, Some nhi, Some bhi =>
      combine (seq 1 24)
      [Z.eqb (pc cs) qe; expr_eqb (reg cs rs) (mkAlu ALU_ADD beg ne); Z.leb 1 nlo; Z.leb nhi 64; Z.ltb (bhi + 64) two64;
       Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_csb T); img8 k (rp_gsb T); lit_cell k (rp_csb T) SB;
       region_shadow_ok k args beg ne nhi; lit_shadow_zero k bb bk nhi; sym_shadow_ok k beg ne;
       region_window_ok k args beg ne nhi; fresh_ok nx0 cs; ushadow_zero k beg nhi; ushadow_window k beg nhi; ushadow_zero_sym k beg ne;
       ushadow_window_sym k beg ne]%bool   (* [comment removed for export] *)
  | _, _, _ => [(0%nat, false)]
  end.
(* [comment removed for export] *)
Definition diag_window (cs : acs) (args : list expr) (beg : expr) (nhi : Z) : expr * Z * Z * Z * expr * lin :=
  let k := kn cs in
  let '(bb0, bk0) := split_lit beg in
  let '(bb, bk, len) := match args with [ebase; ELit elen] => let '(eb, ek) := split_lit ebase in (eb, ek, elen) | _ => (bb0, bk0, nhi) end in
  let '(hb, hk) := shsplit k bb bk in
  let w0 := hk - hk mod 8 in
  let w1 := (hk + ngran bk len - 1) - (hk + ngran bk len - 1) mod 8 + 8 in
  let ps := flat_map (fun K => match rpiece K with Some p => [p] | None => [] end) k in
  let cur := chain_go (length ps) ps (eaddz hb w0) in
  (hb, hk, w0, w1, cur, lin_of (mkAlu ALU_SUB cur (eaddz hb w0))).

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition MV_A0 : Z := 2 ^ 47 - 1.
Definition MV_C55 : Z := 0x5555555555555555.
Definition MV_C33 : Z := 0x3333333333333333.
Definition MV_C0F : Z := 0x0f0f0f0f0f0f0f0f.
Definition MV_C01 : Z := 0x0101010101010101.
Definition MV_A5 : Z := 32767.
Definition mv_regs (sr : list expr) : list expr :=
  sr_upd (sr_upd (sr_upd (sr_upd (sr_upd (sr_upd sr 10 (ELit MV_A0)) 11 (ELit MV_C55)) 12 (ELit MV_C33)) 13 (ELit MV_C0F)) 14 (ELit MV_C01)) 15 (ELit MV_A5).
Definition node_maxva (cs : acs) : option acs :=
  if negb (Z.eqb (pc cs) (mv_entry T)) then None else
  match erange (kn cs) (reg cs 10) with
  | Some (lo, hi) =>
      if (Z.leb (2 ^ 46) lo &&& Z.leb hi MV_A0 &&& fresh_ok nx0 cs)%bool
      then Some (with_ss cs (mk_ss (mv_exit T) (mv_regs (s_regs (a_ss cs))) (kn cs) (nxt cs)))
      else None
  | None => None
  end.


(* [comment removed for export] *)
Definition window_coverB (bc : bctx) (k : list kentry) (hb : expr) (hk ng : Z) : bool :=
  existsb_sc (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideLB bc hb (hk - 7) (ELit (ng + 14)) b o l then true
                        else (xinsideLB bc hb (hk - 7) (ELit (ng + 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Lemma window_coverB_eqf : forall fk, window_coverB (mkbc fk) fk = window_cover fk.
Proof. intros. bcfe. reflexivity. Qed.
Definition window_cover_xB (bc : bctx) (k : list kentry) (hb : expr) (hk : Z) (ng : expr) : bool :=
  existsb_sc (fun K => match rpiece K with
                    | Some (b, o, l) =>
                        if xinsideLB bc hb (hk - 7) (mkAlu ALU_ADD ng (ELit 14)) b o l then true
                        else (xinsideLB bc hb (hk - 7) (mkAlu ALU_ADD ng (ELit 7)) b o l &&& Z.leb 3 (lin_align (mkAlu ALU_ADD (eaddz b o) l)))%bool
                    | None => false
                    end) k.
Lemma window_cover_xB_eqf : forall fk, window_cover_xB (mkbc fk) fk = window_cover_x fk.
Proof. intros. bcfe. reflexivity. Qed.
Definition side_okB (bc : bctx) (k : list kentry) (beg ne : expr) (blo bhi nhi : Z) : bool :=
  (Z.leb (bhi + nhi) kLowEnd ||| (Z.leb kHighBeg blo &&& Z.leb (bhi + nhi) kHighEnd))
  ||| (Z.leb bhi (2 ^ 47) &&& Z.leb nhi (2 ^ 47)
      &&& ranges_apart_xB bc beg 0 ne (ELit kLowEnd) 0 (ELit (kHighBeg - kLowEnd))
      &&& (Z.leb (bhi + nhi) kHighEnd
          ||| match base_rangeB bc beg with
             | Some (lo1, hi1) => match end_hi k beg 0 ne lo1 hi1 nhi with Some e => Z.leb e kHighEnd | None => false end
             | None => false
             end)).
Lemma side_okB_eqf : forall fk, side_okB (mkbc fk) fk = side_ok fk.
Proof. intros. bcfe. unfold side_okB, side_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf. reflexivity. Qed.
Definition lit_cellB (bc : bctx) (k : list kentry) (cell v : Z) : bool :=
  flat_xB bc (ELit 0) cell (ELit 8) &&&
  match know_lookupB segs bc (ELit 0) cell 8 false [] [] with
  | LHit e sc _ => match sc, erangeB bc e with [], Some (lo, hi) => Z.eqb lo v &&& Z.eqb hi v | _, _ => false end
  | _ => false
  end.
Lemma lit_cellB_eqf : forall fk, lit_cellB (mkbc fk) fk = lit_cell fk.
Proof. intros. bcfe. unfold lit_cellB, lit_cell. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf. reflexivity. Qed.
Definition img8B (bc : bctx) (k : list kentry) (a : Z) : bool := img_covB bc a (a + 8).
Lemma img8B_eqf : forall fk, img8B (mkbc fk) fk = img8 fk.
Proof. intros. bcfe. unfold img8B, img8. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf. reflexivity. Qed.
Definition enc_okB (bc : bctx) (k : list kentry) (beg ne : expr) (nhi : Z) (eb : expr) (ek elen : Z) : bool :=
  let d := mkAlu ALU_SUB beg (eaddz eb ek) in
  match erangeB bc d with
  | Some (dlo, dhi) =>
      ((0 <=? dlo) &&& (0 <=? elen) &&& (elen <=? 2 ^ 40) &&& flat_xB bc eb ek (ELit elen)
       &&& ((dhi + nhi <=? elen)
           
           ||| ((dhi + nhi <? two64)
               &&& match erangeB bc (mkAlu ALU_ADD d ne) with Some (_, thi) => thi <=? elen | None => false end)))%bool
  | None => false
  end.
Lemma enc_okB_eqf : forall fk, enc_okB (mkbc fk) fk = enc_ok fk.
Proof. intros. bcfe. unfold enc_okB, enc_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf. reflexivity. Qed.
Definition kchainB (bc : bctx) (k : list kentry) (b : expr) (off : Z) (minlen : Z) : bool :=
  let ps := flat_map (fun K => match rpiece K with Some p => [p] | None => [] end) k in
  let cur := chain_go_s (length ps) ps (eaddz b off) minlen (eaddz b off) in
  match lin_of (mkAlu ALU_SUB cur (eaddz b off)) with
  | (d, []) => ((minlen <=? d) &&& (d <? 2 ^ 62) &&& (0 <=? minlen))%bool
  | _ => false
  end.
Lemma kchainB_eqf : forall fk, kchainB (mkbc fk) fk = kchain fk.
Proof. intros. bcfe. unfold kchainB, kchain. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf. reflexivity. Qed.
Definition shsplitB (bc : bctx) (k : list kentry) (bb : expr) (bk : Z) : expr * Z := split_lit (eadd (ELit (SB + bk / 8)) (mkSrlB bc bb 3)).
Lemma shsplitB_eqf : forall fk, shsplitB (mkbc fk) fk = shsplit fk.
Proof. intros. bcfe. unfold shsplitB, shsplit. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf. reflexivity. Qed.
Definition lit_shadow_zeroB (bc : bctx) (k : list kentry) (bb : expr) (bk len : Z) : bool :=
  let '(hb, hk) := shsplitB bc k bb bk in
  (Z.leb 3 (ealignB bc bb) &&& flat_xB bc bb bk (ELit 1)
   &&& flat_xB bc hb hk (ELit (ngran bk len)) &&& kzero_xB bc k hb hk (ELit (ngran bk len)))%bool.
Lemma lit_shadow_zeroB_eqf : forall fk, lit_shadow_zeroB (mkbc fk) fk = lit_shadow_zero fk.
Proof. intros. bcfe. unfold lit_shadow_zeroB, lit_shadow_zero. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf. reflexivity. Qed.
Definition shadow_window_okB (bc : bctx) (k : list kentry) (bb : expr) (bk len : Z) : bool :=
  let '(hb, hk) := shsplitB bc k bb bk in
  let ng := ngran bk len in
  let w0 := hk - hk mod 8 in
  let w1 := (hk + ng - 1) - (hk + ng - 1) mod 8 + 8 in
  (Z.leb 3 (ealignB bc bb) &&& flat_xB bc bb bk (ELit 1)
   &&& (if (Z.leb 3 (ealignB bc hb) &&& flat_xB bc hb w0 (ELit (w1 - w0)) &&& kchainB bc k hb w0 (w1 - w0))%bool then true
       else window_coverB bc k hb hk ng))%bool.
Lemma shadow_window_okB_eqf : forall fk, shadow_window_okB (mkbc fk) fk = shadow_window_ok fk.
Proof. intros. bcfe. unfold shadow_window_okB, shadow_window_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf. reflexivity. Qed.
Definition ushadowB (bc : bctx) (k : list kentry) (beg : expr) : expr * Z := split_lit (mkAlu ALU_ADD (mkSrlB bc beg 3) (ELit SB)).
Lemma ushadowB_eqf : forall fk, ushadowB (mkbc fk) fk = ushadow fk.
Proof. intros. bcfe. unfold ushadowB, ushadow. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf. reflexivity. Qed.
Definition ushadow_zeroB (bc : bctx) (k : list kentry) (beg : expr) (nhi : Z) : bool :=
  let '(sb, sk) := ushadowB bc k beg in
  (flat_xB bc sb sk (ELit (ugran nhi)) &&& kzero_xB bc k sb sk (ELit (ugran nhi)))%bool.
Lemma ushadow_zeroB_eqf : forall fk, ushadow_zeroB (mkbc fk) fk = ushadow_zero fk.
Proof. intros. bcfe. unfold ushadow_zeroB, ushadow_zero. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf. reflexivity. Qed.
Definition ugran_symB (bc : bctx) (k : list kentry) (beg ne : expr) : expr :=
  mkAlu ALU_ADD (mkAlu ALU_SUB (mkSrlB bc (mkAlu ALU_ADD beg (mkAlu ALU_ADD ne (ELit (-1)))) 3) (mkSrlB bc beg 3)) (ELit 1).
Lemma ugran_symB_eqf : forall fk, ugran_symB (mkbc fk) fk = ugran_sym fk.
Proof. intros. bcfe. unfold ugran_symB, ugran_sym. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf. reflexivity. Qed.
Definition ushadow_zero_symB (bc : bctx) (k : list kentry) (beg ne : expr) : bool :=
  let '(sb, sk) := ushadowB bc k beg in
  let G := ugran_symB bc k beg ne in
  (flat_xB bc sb sk G &&& kzero_xB bc k sb sk G)%bool.
Lemma ushadow_zero_symB_eqf : forall fk, ushadow_zero_symB (mkbc fk) fk = ushadow_zero_sym fk.
Proof. intros. bcfe. unfold ushadow_zero_symB, ushadow_zero_sym. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf. reflexivity. Qed.
Definition ushadow_windowB (bc : bctx) (k : list kentry) (beg : expr) (nhi : Z) : bool :=
  let '(sb, sk) := ushadowB bc k beg in
  (flat_xB bc sb sk (ELit (ugran nhi)) &&& window_coverB bc k sb sk (ugran nhi))%bool.
Lemma ushadow_windowB_eqf : forall fk, ushadow_windowB (mkbc fk) fk = ushadow_window fk.
Proof. intros. bcfe. unfold ushadow_windowB, ushadow_window. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf. reflexivity. Qed.
Definition ushadow_window_symB (bc : bctx) (k : list kentry) (beg ne : expr) : bool :=
  let '(sb, sk) := ushadowB bc k beg in
  let G := ugran_symB bc k beg ne in
  (flat_xB bc sb sk G &&& window_cover_xB bc k sb sk G)%bool.
Lemma ushadow_window_symB_eqf : forall fk, ushadow_window_symB (mkbc fk) fk = ushadow_window_sym fk.
Proof. intros. bcfe. unfold ushadow_window_symB, ushadow_window_sym. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf. reflexivity. Qed.
Definition region_shadow_okB (bc : bctx) (k : list kentry) (args : list expr) (beg ne : expr) (nhi : Z) : bool :=
  let '(bb, bk) := split_lit beg in
  match args with
  | [] => lit_shadow_zeroB bc k bb bk nhi ||| sym_shadow_okB bc beg ne ||| ushadow_zeroB bc k beg nhi ||| ushadow_zero_symB bc k beg ne
  | [ebase; ELit elen] =>
      let '(eb, ek) := split_lit ebase in
      enc_okB bc k beg ne nhi eb ek elen &&& lit_shadow_zeroB bc k eb ek elen
  | _ => false
  end%bool.
Lemma region_shadow_okB_eqf : forall fk, region_shadow_okB (mkbc fk) fk = region_shadow_ok fk.
Proof. intros. bcfe. unfold region_shadow_okB, region_shadow_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf. reflexivity. Qed.
Definition region_window_okB (bc : bctx) (k : list kentry) (args : list expr) (beg ne : expr) (nhi : Z) : bool :=
  let '(bb, bk) := split_lit beg in
  match args with
  | [] => shadow_window_okB bc k bb bk nhi ||| ushadow_windowB bc k beg nhi ||| ushadow_window_symB bc k beg ne
  | [ebase; ELit elen] => let '(eb, ek) := split_lit ebase in shadow_window_okB bc k eb ek elen
  | _ => false
  end%bool.
Lemma region_window_okB_eqf : forall fk, region_window_okB (mkbc fk) fk = region_window_ok fk.
Proof. intros. bcfe. unfold region_window_okB, region_window_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf. reflexivity. Qed.
Definition in63B (bc : bctx) (k : list kentry) (e : expr) : bool :=
  match erangeB bc e with Some (lo, hi) => (Z.leb 0 lo &&& Z.leb hi 63)%bool | None => false end.
Lemma in63B_eqf : forall fk, in63B (mkbc fk) fk = in63 fk.
Proof. intros. bcfe. unfold in63B, in63. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf. reflexivity. Qed.
Definition idx_okB (bc : bctx) (k : list kentry) (e : expr) : bool :=
  match e with
  | EAlu ALU_XOR e' (ELit z) => if Z.eqb z 63 then in63B bc k e' else in63B bc k e
  | _ => in63B bc k e
  end.
Lemma idx_okB_eqf : forall fk, idx_okB (mkbc fk) fk = idx_ok fk.
Proof. intros. bcfe. unfold idx_okB, idx_ok. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf. reflexivity. Qed.
Definition node_rpoison_v2M (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    
    let '(bb, bk) := split_lit beg in
    let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8)) (mkSrlB bc bb 3)) in
    match xloB bc ne, xhiB bc ne, xloB bc beg, xhiB bc beg, xloB bc sp, xhiB bc sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      let L := (bk + nhi - 1) / 8 - bk / 8 + 1 in
      if (Z.leb 16 nlo &&& Z.leb nhi (2 ^ 40)
          &&& side_okB bc k beg ne blo bhi nhi
          &&& Z.leb 3 (ealignB bc bb) &&& flat_xB bc bb bk (ELit 1)
          &&& Z.leb 80 splo &&& Z.ltb sphi two64
          &&& Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          &&& Z.leb (rp_chi T + 8) (splo - 72) &&& Z.leb (rp_cm2 T + 8) (splo - 72) &&& Z.leb (rp_cm1 T + 8) (splo - 72)
          &&& Z.leb (rp_csb T + 8) (splo - 72) &&& Z.leb (rp_ghi T + 8) (splo - 72) &&& Z.leb (rp_gm2 T + 8) (splo - 72)
          &&& Z.leb (rp_gm1 T + 8) (splo - 72) &&& Z.leb (rp_gsb T + 8) (splo - 72)
          &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_gm1 T) &&& Z.leb 0 (rp_gm2 T) &&& Z.leb 0 (rp_ghi T)
          &&& Z.leb 0 (rp_csb T) &&& Z.leb 0 (rp_cm1 T) &&& Z.leb 0 (rp_cm2 T) &&& Z.leb 0 (rp_chi T)
          &&& kwritableB A bc k qb qk 72 &&& flat_xB bc qb qk (ELit 72)
          &&& flat_xB bc hb hk (ELit L) &&& kzero_xB bc k hb hk (ELit L)
          &&& img8B bc k (rp_gsb T) &&& img8B bc k (rp_gm1 T) &&& img8B bc k (rp_gm2 T) &&& img8B bc k (rp_ghi T)
          &&& img8B bc k (rp_cm1 T) &&& img8B bc k (rp_cm2 T)
          &&& lit_cellB bc k (rp_csb T) SB &&& lit_cellB bc k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havocM k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.
Lemma node_rpoison_v2M_feq : node_rpoison_v2M = node_rpoison_v2.
Proof. apply functional_extensionality; intros ?. unfold node_rpoison_v2M, node_rpoison_v2. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_rpoisonM (args : list expr) (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) (rp_entry T)) then None else
  match ret_lit cs with
  | Some ret =>
    let beg := reg cs 10 in let ne := reg cs 11 in let sp := reg cs 2 in
    let '(qb, qk) := split_lit (eaddz sp (-72)) in
    match xloB bc ne, xhiB bc ne, xloB bc beg, xhiB bc beg, xloB bc sp, xhiB bc sp with
    | Some nlo, Some nhi, Some blo, Some bhi, Some splo, Some sphi =>
      if (Z.leb 16 nlo &&& Z.leb nhi (2 ^ 40)
          &&& side_okB bc k beg ne blo bhi nhi
          &&& Z.leb 80 splo &&& Z.ltb sphi two64
          &&& Z.ltb (SB + (bhi + nhi - 1) / 8) (splo - 72)
          &&& Z.leb (rp_chi T + 8) (splo - 72) &&& Z.leb (rp_cm2 T + 8) (splo - 72) &&& Z.leb (rp_cm1 T + 8) (splo - 72)
          &&& Z.leb (rp_csb T + 8) (splo - 72) &&& Z.leb (rp_ghi T + 8) (splo - 72) &&& Z.leb (rp_gm2 T + 8) (splo - 72)
          &&& Z.leb (rp_gm1 T + 8) (splo - 72) &&& Z.leb (rp_gsb T + 8) (splo - 72)
          &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_gm1 T) &&& Z.leb 0 (rp_gm2 T) &&& Z.leb 0 (rp_ghi T)
          &&& Z.leb 0 (rp_csb T) &&& Z.leb 0 (rp_cm1 T) &&& Z.leb 0 (rp_cm2 T) &&& Z.leb 0 (rp_chi T)
          &&& kwritableB A bc k qb qk 72 &&& flat_xB bc qb qk (ELit 72)
          &&& region_shadow_okB bc k args beg ne nhi
          &&& img8B bc k (rp_gsb T) &&& img8B bc k (rp_gm1 T) &&& img8B bc k (rp_gm2 T) &&& img8B bc k (rp_ghi T)
          &&& img8B bc k (rp_cm1 T) &&& img8B bc k (rp_cm2 T)
          &&& lit_cellB bc k (rp_csb T) SB &&& lit_cellB bc k (rp_chi T) kHighEnd)%bool
      then after_call nx0 cs ret (Some (ELit 0)) (kn_havocM k qb qk (ELit 72))
      else None
    | _, _, _, _, _, _ => None
    end
  | None => None
  end.
Lemma node_rpoisonM_feq : node_rpoisonM = node_rpoison.
Proof. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. unfold node_rpoisonM, node_rpoison. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_quickM (qe qx : Z) (rb rs : nat) (args : list expr) (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) qe) then None else
  let beg := reg cs rb in let ne := reg cs 12 in
  if negb (expr_eqb (reg cs rs) (mkAlu ALU_ADD beg ne)) then None else
  match xloB bc ne, xhiB bc ne, xhiB bc beg with
  | Some nlo, Some nhi, Some bhi =>
    if (Z.leb 1 nlo &&& Z.leb nhi 64 &&& Z.ltb (bhi + 64) two64
        &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_csb T) &&& img8B bc k (rp_gsb T) &&& lit_cellB bc k (rp_csb T) SB
        &&& region_shadow_okB bc k args beg ne nhi &&& region_window_okB bc k args beg ne nhi
        &&& fresh_ok nx0 cs)%bool
    then match node_havoc nx0 cs [13; 14; 15; 16; 17]%nat with
         | Some cs1 => Some (with_ss cs1 (mk_ss qx (sr_upd (s_regs (a_ss cs1)) rs (eaddz (mkAlu ALU_ADD beg ne) (-1))) (kn cs1) (nxt cs1)))
         | None => None
         end
    else None
  | _, _, _ => None
  end.
Lemma node_quickM_feq : node_quickM = node_quick.
Proof. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. apply functional_extensionality; intros ?. unfold node_quickM, node_quick. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_readcheckM (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) (rc_entry T)) then None else
  let dst := reg cs 9 in let re := reg cs 10 in
  let '(bb, bk) := split_lit dst in
  let m := (SB + bk / 8) mod 8 in
  let '(hb, hk) := split_lit (eadd (ELit (SB + bk / 8 - m)) (mkSrlB bc bb 3)) in
  match xloB bc re, xhiB bc re, xhiB bc dst with
  | Some rlo, Some rhi, Some dhi =>
    if (Z.leb 1 rlo &&& Z.leb rhi 64 &&& Z.ltb (dhi + 64) two64 &&& Z.leb 6 (ealignB bc bb) &&& flat_xB bc bb bk (ELit 1)
        &&& fresh_ok nx0 cs
        &&& flat_xB bc hb hk (ELit 16) &&& kzero_xB bc k hb hk (ELit 16)
        &&& Z.leb 0 (rp_gsb T) &&& Z.leb 0 (rp_csb T) &&& img8B bc k (rp_gsb T) &&& lit_cellB bc k (rp_csb T) SB)%bool
    then
      let e1 := eadd (ELit (SB + bk / 8)) (mkSrlB bc bb 3) in
      let e3 := eaddz (eadd dst re) (-1) in
      let e2 := eadd (ELit SB) (mkSrlB bc e3 3) in
      let e20 := eaddz (eaddz (reg cs 8) (-2048)) (-72) in
      Some (with_ss cs (mk_ss (rc_exit T) (rc_regs (s_regs (a_ss cs)) e1 e2 e3 e20) k (nxt cs)))
    else None
  | _, _, _ => None
  end.
Lemma node_readcheckM_feq : node_readcheckM = node_readcheck.
Proof. apply functional_extensionality; intros ?. unfold node_readcheckM, node_readcheck. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_msbM (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) (msb_entry T)) then None else
  match reg cs 9, erangeB bc (reg cs 18) with
  | ELit s1, Some (lo, hi) =>
      let s := s1 mod two64 in
      match kreadZB segs bc (ELit 0) (s + 48) 8, msb_rangeF lo hi with
      | Some nres, Some (cmin, cmax) =>
          if (Z.leb 12 (ealignB bc (reg cs 18)) &&& Z.leb 0 s &&& Z.ltb (s + 56) two64 &&& flat_xB bc (ELit 0) (s + 48) (ELit 8)
              &&& fresh_ok nx0 cs)%bool then
            match node_havoc nx0 cs MSBR with
            | Some cs1 => Some (with_ss cs1 (mk_ss (msb_exit T) (sr_upd (s_regs (a_ss cs1)) 14 (ELit nres))
                                                 (KRange (EVar (nxt cs + 4)%nat) cmin cmax :: kn cs1) (nxt cs1)))
            | None => None
            end
          else None
      | _, _ => None
      end
  | _, _ => None
  end.
Lemma node_msbM_feq : node_msbM = node_msb.
Proof. apply functional_extensionality; intros ?. unfold node_msbM, node_msb. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_largestatsM (cs : acs) : option acs :=
  let k := kn cs in let bc := mkbc k in
  if negb (Z.eqb (pc cs) (ls_entry T)) then None else
  match reg cs 9 with
  | ELit s1 =>
      let s := s1 mod two64 in
      if (idx_okB bc k (reg cs 11) &&& Z.leb 0 s &&& Z.ltb (s + 616) two64
          &&& kwritableB A bc k (ELit 0) (s + 96) 520 &&& flat_xB bc (ELit 0) (s + 96) (ELit 520) &&& fresh_ok nx0 cs)%bool then
        match node_havoc nx0 cs LSR with
        | Some cs1 => Some (with_ss cs1 (mk_ss (ls_exit T) (s_regs (a_ss cs1)) (kn_havoc (kn cs1) (ELit 0) (s + 96) (ELit 520)) (nxt cs1)))
        | None => None
        end
      else None
  | _ => None
  end.
Lemma node_largestatsM_feq : node_largestatsM = node_largestats.
Proof. apply functional_extensionality; intros ?. unfold node_largestatsM, node_largestats. cbv zeta. rewrite ?window_coverB_eqf, ?window_cover_xB_eqf, ?kzero_xB_eqf, ?kwritableB_eqf, ?kwritable_xB_eqf, ?know_lookupB_eqf, ?kread8eB_eqf, ?kreadZB_eqf, ?xloB_eqf, ?xhiB_eqf, ?xlo1B_eqf, ?xhi1B_eqf, ?xlo2B_eqf, ?xhi2B_eqf, ?erangeB_eqf, ?ealignB_eqf, ?flat_xB_eqf, ?lin_ge0B_eqf, ?ranges_apart_xB_eqf, ?mkSrlB_eqf, ?mkAndB_eqf, ?base_rangeB_eqf, ?img_covB_eqf, ?extKB_eqf, ?kn_havocM_eq, ?partial_val_okB_eqf, ?sym_shadow_okB_eqf, ?side_okB_eqf, ?lit_cellB_eqf, ?img8B_eqf, ?enc_okB_eqf, ?kchainB_eqf, ?shsplitB_eqf, ?lit_shadow_zeroB_eqf, ?shadow_window_okB_eqf, ?ushadowB_eqf, ?ushadow_zeroB_eqf, ?ugran_symB_eqf, ?ushadow_zero_symB_eqf, ?ushadow_windowB_eqf, ?ushadow_window_symB_eqf, ?region_shadow_okB_eqf, ?region_window_okB_eqf, ?in63B_eqf, ?idx_okB_eqf. reflexivity. Qed.
Definition node_quick_srcM (args : list expr) (cs : acs) : option acs := node_quickM (qs_entry T) (qs_exit T) 11 19 args cs.
Definition node_quick_dstM (args : list expr) (cs : acs) : option acs := node_quickM (qd_entry T) (qd_exit T) 10 20 args cs.

Definition xn_ref (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 100 then node_rpoison args cs
  else if Nat.eqb id 101 then node_readcheck cs
  else if Nat.eqb id 102 then node_quick_src args cs
  else if Nat.eqb id 103 then node_quick_dst args cs
  else if Nat.eqb id 105 then node_msb cs
  else if Nat.eqb id 106 then node_largestats cs
  else if Nat.eqb id 107 then node_maxva cs   (* [comment removed for export] *)
  else None.

Definition xn (id : nat) (args : list expr) (cs : acs) : option acs :=
  if Nat.eqb id 100 then node_rpoisonM args cs
  else if Nat.eqb id 101 then node_readcheckM cs
  else if Nat.eqb id 102 then node_quick_srcM args cs
  else if Nat.eqb id 103 then node_quick_dstM args cs
  else if Nat.eqb id 105 then node_msbM cs
  else if Nat.eqb id 106 then node_largestatsM cs
  else if Nat.eqb id 107 then node_maxva cs   (* [comment removed for export] *)
  else None.
Lemma xn_eq : forall id args cs, xn id args cs = xn_ref id args cs.
Proof.
  intros. unfold xn, xn_ref, node_quick_srcM, node_quick_dstM, node_quick_src, node_quick_dst.
  rewrite ?node_rpoison_v2M_feq, ?node_rpoisonM_feq, ?node_quickM_feq, ?node_readcheckM_feq, ?node_msbM_feq, ?node_largestatsM_feq. reflexivity.
Qed.
End WithSegs.
End RPN.
