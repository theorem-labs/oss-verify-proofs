(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame LibDefs.
Unset Nia Cache.  (* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Open Scope Z_scope.

Record tags_abi : Type := TAGS {
  t_gettag   : Z;   (* [comment removed for export] *)
  t_getidx   : Z;   (* [comment removed for export] *)
  t_tagxyz   : Z;   (* [comment removed for export] *)
  t_xyzd50   : Z;   (* [comment removed for export] *)
  t_xyzd50_d : Z;   (* [comment removed for export] *)
  t_cicp     : Z;   (* [comment removed for export] *)
  t_usable   : Z;   (* [comment removed for export] *)
  t_parse    : Z;   (* [comment removed for export] *)
  t_parse_d  : Z;   (* [comment removed for export] *)
  t_ro_lo    : Z;   (* [comment removed for export] *)
  t_ro_hi    : Z
}.

Definition tags_src1 : tags_abi :=
  TAGS 0x137b4 0x139c8 0x138e8 0x1485c 32 0 0 0x13ae8 656 0x103ec 0x1048c.
Definition tags_infoub : tags_abi :=
  TAGS 0x13a68 0x13cfc 0x13bd8 0x14d04 48 0x1633c 0x1639c 0x13e4c 672 0x103ec 0x10490.

Section Specs.
Variable segs : list Segment.
Variable W : tags_abi.

#[local] Notation cell32 := (cell32 segs).
#[local] Notation cell64 := (cell64 segs).
#[local] Notation cell8 := (cell8 segs).
#[local] Notation writable := (writable segs).
#[local] Notation tag_ok := (tag_ok segs).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition gettag_pre (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz sig : Z) (T : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let t := bv_unsigned T in
  getr regs 10 = P /\ getr regs 11 = Z_to_bv 64 sig /\ getr regs 12 = T /\
  0 <= sig < 2 ^ 32 /\
  data_ok mem data len bs /\
  cell64 mem p data /\ cell32 mem (p + 20) tc /\ tags_ok len bs tc psz /\
  0 < p /\ p + 24 <= 2 ^ 64 /\ (p mod 8 = 0) /\
  0 < t /\ (t mod 8 = 0) /\ writable mem t 24 /\
  (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data) /\
  (p + 24 <= t \/ t + 24 <= p).

Definition gettag_post (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz sig : Z) (T : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  frame_mod mem mem' [(T, 24)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 ->
       tag_ok mem' data len t /\ cell32 mem' t sig /\ (exists ty, cell32 mem' (t + 4) ty)).

Definition gettag_contract : Prop :=
  forall data len bs P tc psz sig T,
    fn_contract segs (t_gettag W)
      (gettag_pre data len bs P tc psz sig T)
      (gettag_post data len bs P tc psz sig T).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition getidx_pre (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz idx : Z) (T : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let t := bv_unsigned T in
  getr regs 10 = P /\ getr regs 11 = Z_to_bv 64 idx /\ getr regs 12 = T /\
  0 <= idx < tc /\
  data_ok mem data len bs /\
  cell64 mem p data /\ cell32 mem (p + 20) tc /\ tags_ok len bs tc psz /\
  0 < p /\ p + 24 <= 2 ^ 64 /\ (p mod 8 = 0) /\
  0 < t /\ (t mod 8 = 0) /\ writable mem t 24 /\
  (bv_unsigned data + len <= t \/ t + 24 <= bv_unsigned data) /\
  (p + 24 <= t \/ t + 24 <= p).

Definition getidx_post (data : word) (len : Z) (bs : list byte)
    (P : word) (tc psz idx : Z) (T : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  frame_mod mem mem' [(T, 24)] /\
  tag_ok mem' data len t /\ (exists s, cell32 mem' t s) /\ (exists ty, cell32 mem' (t + 4) ty).

Definition getidx_contract : Prop :=
  forall data len bs P tc psz idx T,
    fn_contract segs (t_getidx W)
      (getidx_pre data len bs P tc psz idx T)
      (getidx_post data len bs P tc psz idx T).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fcell_ok (mem : word -> option byte) (data : word) (len : Z) (t : Z) (X : word) : Prop :=
  let x := bv_unsigned X in
  writable mem x 4 /\ (x mod 4 = 0) /\ 0 < x /\
  (bv_unsigned data + len <= x \/ x + 4 <= bv_unsigned data) /\
  (t + 24 <= x \/ x + 4 <= t).

Definition tagxyz_pre (data : word) (len : Z) (bs : list byte) (T X Y Zc : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  getr regs 10 = T /\ getr regs 11 = X /\ getr regs 12 = Y /\ getr regs 13 = Zc /\
  data_ok mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ t + 24 <= 2 ^ 64 /\
  fcell_ok mem data len t X /\ fcell_ok mem data len t Y /\ fcell_ok mem data len t Zc.

Definition tagxyz_post (data : word) (len : Z) (bs : list byte) (T X Y Zc : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(X, 4); (Y, 4); (Zc, 4)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition tagxyz_contract : Prop :=
  forall data len bs T X Y Zc,
    fn_contract segs (t_tagxyz W)
      (tagxyz_pre data len bs T X Y Zc)
      (tagxyz_post data len bs T X Y Zc).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition xtag_ok (mem : word -> option byte) (data : word) (len : Z) (sp : word) (m : Z) (T : word) : Prop :=
  let t := bv_unsigned T in
  let d := t_xyzd50_d W in
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ t + 24 <= 2 ^ 64 /\
  (bv_unsigned sp <= t \/ t + 24 <= bv_unsigned sp - d) /\
  (m + 36 <= t \/ t + 24 <= m).

Definition xyzd50_pre (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let m := bv_unsigned M in
  let d := t_xyzd50_d W in
  getr regs 2 = sp /\ getr regs 10 = T1 /\ getr regs 11 = T2 /\ getr regs 12 = T3 /\ getr regs 13 = M /\
  data_ok mem data len bs /\
  xtag_ok mem data len sp m T1 /\ xtag_ok mem data len sp m T2 /\ xtag_ok mem data len sp m T3 /\
  writable mem m 36 /\ (m mod 4 = 0) /\ 0 < m /\
  (bv_unsigned sp mod 16 = 0) /\ writable mem (bv_unsigned sp - d) d /\
  (bv_unsigned data + len <= m \/ m + 36 <= bv_unsigned data) /\
  (bv_unsigned sp <= m \/ m + 36 <= bv_unsigned sp - d) /\
  (bv_unsigned data + len <= bv_unsigned sp - d \/ bv_unsigned sp <= bv_unsigned data).

Definition xyzd50_post (data : word) (len : Z) (bs : list byte) (sp T1 T2 T3 M : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let d := t_xyzd50_d W in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - d), d); (M, 36)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition xyzd50_contract : Prop :=
  forall data len bs sp T1 T2 T3 M,
    fn_contract segs (t_xyzd50 W)
      (xyzd50_pre data len bs sp T1 T2 T3 M)
      (xyzd50_post data len bs sp T1 T2 T3 M).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition cicp_pre (data : word) (len : Z) (bs : list byte) (T C : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let t := bv_unsigned T in
  let c := bv_unsigned C in
  getr regs 10 = T /\ getr regs 11 = C /\
  data_ok mem data len bs /\
  (exists ty, cell32 mem (t + 4) ty) /\ tag_ok mem data len t /\
  (t mod 8 = 0) /\ t + 24 <= 2 ^ 64 /\
  writable mem c 4 /\
  (bv_unsigned data + len <= c \/ c + 4 <= bv_unsigned data) /\
  (t + 24 <= c \/ c + 4 <= t).

Definition cicp_post (data : word) (len : Z) (bs : list byte) (T C : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  frame_mod mem mem' [(C, 4)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition cicp_contract : Prop :=
  forall data len bs T C,
    fn_contract segs (t_cicp W) (cicp_pre data len bs T C) (cicp_post data len bs T C).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition bool8 (mem : word -> option byte) (a : Z) : Prop :=
  exists v, cell8 mem a v /\ (v = 0 \/ v = 1).

Definition usable_pre (P : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  getr regs 10 = P /\ (p mod 8 = 0) /\ p + 976 <= 2 ^ 64 /\
  bool8 mem (p + 964) /\ bool8 mem (p + 965) /\ bool8 mem (p + 966).

Definition usable_post (P : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  mem' = mem /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1).

Definition usable_contract : Prop :=
  forall P, fn_contract segs (t_usable W) (usable_pre P) (usable_post P).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition parsed_ok (mem : word -> option byte) (data : word) (len : Z) (bs : list byte) (p : Z) : Prop :=
  exists (psz tc htrc hasA2B : Z),
    cell64 mem p data /\ cell32 mem (p + 8) psz /\ cell32 mem (p + 20) tc /\
    tags_ok len bs tc psz /\
    curves_ok segs mem data len p /\
    cell8 mem (p + 964) htrc /\ (htrc = 0 \/ htrc = 1) /\
    cell8 mem (p + 966) hasA2B /\ (hasA2B = 0 \/ hasA2B = 1) /\
    (hasA2B <> 0 -> grid_ok_A2B segs mem data len p).

Lemma parsed_ok_profile_ok : forall mem data len bs p,
  parsed_ok mem data len bs p -> profile_ok segs mem data len bs p.
Proof.
  intros mem data len bs p (psz & tc & htrc & hasA2B & H0 & H8 & H20 & Ht & Hc & H964 & _ & H966 & _ & Hg).
  exists psz, tc, hasA2B.
  split; [exact H0|]. split; [exact H8|]. split; [exact H20|]. split; [exact Ht|].
  split; [exact Hc|]. split; [exact H966|]. exact Hg.
Qed.

Definition parse_pre (data : word) (len : Z) (bs : list byte) (sp prio P : word)
    (FP : FPState) (regs : bvmap 5 word) (mem : word -> option byte) : Prop :=
  let p := bv_unsigned P in
  let q := bv_unsigned prio in
  let d := t_parse_d W in
  getr regs 2 = sp /\ getr regs 10 = data /\ getr regs 11 = Z_to_bv 64 len /\
  getr regs 12 = prio /\ getr regs 13 = Z_to_bv 64 2 /\ getr regs 14 = P /\
  data_ok mem data len bs /\
  (* [comment removed for export] *)
  cell32 mem q 0 /\ cell32 mem (q + 4) 1 /\ (q mod 4 = 0) /\ 0 < q /\ q + 8 <= 2 ^ 64 /\
  (* [comment removed for export] *)
  writable mem p 976 /\ (p mod 8 = 0) /\ 0 < p /\
  (* [comment removed for export] *)
  (bv_unsigned sp mod 16 = 0) /\ writable mem (bv_unsigned sp - d) d /\
  rodata_clear mem (t_ro_lo W) (t_ro_hi W) /\
  (* [comment removed for export] *)
  (bv_unsigned data + len <= bv_unsigned sp - d \/ bv_unsigned sp <= bv_unsigned data) /\
  (bv_unsigned data + len <= p \/ p + 976 <= bv_unsigned data) /\
  (bv_unsigned data + len <= q \/ q + 8 <= bv_unsigned data) /\
  (bv_unsigned sp <= p \/ p + 976 <= bv_unsigned sp - d) /\
  (bv_unsigned sp <= q \/ q + 8 <= bv_unsigned sp - d) /\
  (p + 976 <= q \/ q + 8 <= p).

Definition parse_post (data : word) (len : Z) (bs : list byte) (sp prio P : word)
    (regs : bvmap 5 word) (mem : word -> option byte)
    (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
  let d := t_parse_d W in
  frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - d), d); (P, 976)] /\
  exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1) /\
    (r = 1 -> parsed_ok mem' data len bs (bv_unsigned P)).

Definition parse_contract : Prop :=
  forall data len bs sp prio P,
    fn_contract segs (t_parse W)
      (parse_pre data len bs sp prio P)
      (parse_post data len bs sp prio P).

End Specs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
