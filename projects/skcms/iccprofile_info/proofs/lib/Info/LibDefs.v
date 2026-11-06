(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)

From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Sem.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition abi_kept : list reg := [2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
(* [comment removed for export] *)
Definition abi_fkept : list reg := [8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.

Definition regs_kept (l : list reg) (regs regs' : bvmap 5 word) : Prop :=
  forall r, In r l -> getr regs' r = getr regs r.
Definition fregs_kept (l : list reg) (fr fr' : bvmap 5 word) : Prop :=
  forall r, In r l -> reg_get fr' r = reg_get fr r.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition fn_contract (entry : Z)
    (PRE : FPState -> bvmap 5 word -> (word -> option byte) -> Prop)
    (POST : bvmap 5 word -> (word -> option byte) ->
            FPState -> bvmap 5 word -> (word -> option byte) -> Prop) : Prop :=
  forall (FP : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte) (ret : word),
    getr regs 1 = ret -> ret_ok ret ->
    PRE FP regs mem ->
    exists (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps segs (mkst (FP:=FP) regs (Z_to_bv 64 entry) mem rom)
                  (mkst (FP:=FP') regs' ret mem' rom)
      /\ regs_kept abi_kept regs regs'
      /\ fregs_kept abi_fkept (fp_regs (FPState:=FP)) (fp_regs (FPState:=FP'))
      /\ POST regs mem FP' regs' mem'.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition cell (mem : word -> option byte) (a : Z) (w : nat) (x : word) : Prop :=
  rdn segs mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w x).
Definition cell64 (mem : word -> option byte) (a : Z) (x : word) : Prop := cell mem a 8 x.
Definition cell32 (mem : word -> option byte) (a : Z) (v : Z) : Prop :=
  (0 <= v < 2 ^ 32)%Z /\ cell mem a 4 (Z_to_bv 64 v).
Definition cell8 (mem : word -> option byte) (a : Z) (v : Z) : Prop :=
  (0 <= v < 256)%Z /\ cell mem a 1 (Z_to_bv 64 v).

(* [comment removed for export] *)
Definition writable (mem : word -> option byte) (lo n : Z) : Prop :=
  (0 <= lo)%Z /\ (0 < n)%Z /\ (lo + n <= 2 ^ 64)%Z /\
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 lo) (Z.to_nat n) = true.

(* [comment removed for export] *)
Definition rodata_clear (mem : word -> option byte) (lo hi : Z) : Prop :=
  forall i, (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

(* [comment removed for export] *)
Definition data_ok (mem : word -> option byte) (data : word) (len : Z) (bs : list byte) : Prop :=
  (0 <= len < 2 ^ 26)%Z /\ Z.of_nat (length bs) = len /\
  (0 < bv_unsigned data)%Z /\ (bv_unsigned data + len < 2 ^ 47)%Z /\
  forall i, (0 <= i < len)%Z ->
    mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0)).

Definition inDATA (data : word) (len : Z) (p : Z) (n : Z) : Prop :=
  (bv_unsigned data <= p)%Z /\ (0 <= n)%Z /\ (p + n <= bv_unsigned data + len)%Z.

(* [comment removed for export] *)
Definition bs_byte (bs : list byte) (i : Z) : Z := bv_unsigned (nth (Z.to_nat i) bs (Z_to_bv 8 0)).
Definition be16 (bs : list byte) (off : Z) : Z := (bs_byte bs off * 256 + bs_byte bs (off + 1))%Z.
Definition be32 (bs : list byte) (off : Z) : Z :=
  (bs_byte bs off * 16777216 + bs_byte bs (off + 1) * 65536 + bs_byte bs (off + 2) * 256 + bs_byte bs (off + 3))%Z.

End WithSegs.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section Invariants.
Variable segs : list Segment.
Variables (mem : word -> option byte) (data : word) (len : Z).

(* [comment removed for export] *)
Definition curve_ok (c : Z) : Prop :=
  exists (n : Z) (t8 t16 : word),
    cell32 segs mem c n /\ cell64 segs mem (c + 8) t8 /\ cell64 segs mem (c + 16) t16 /\
    (n = 0%Z \/
     ((2 <= n <= 2 ^ 24)%Z
      /\ (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z)
      /\ (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n)
      /\ (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n)))).

(* [comment removed for export] *)
Definition profile_curve_offsets : list Z :=
  [24; 56; 88;                      (* [comment removed for export] *)
   160; 192; 224; 256;              (* [comment removed for export] *)
   312; 344; 376;                   (* [comment removed for export] *)
   464; 496; 528;                   (* [comment removed for export] *)
   560; 592; 624;                   (* [comment removed for export] *)
   664; 696; 728;                   (* [comment removed for export] *)
   808; 840; 872; 904]%Z.           (* [comment removed for export] *)
Definition curves_ok (P : Z) : Prop :=
  Forall (fun off => curve_ok (P + off)%Z) profile_curve_offsets.

(* [comment removed for export] *)
Definition tag_ok (T : Z) : Prop :=
  exists (sz : Z) (buf : word),
    cell32 segs mem (T + 8) sz /\ cell64 segs mem (T + 16) buf /\
    (4 <= sz)%Z /\ inDATA data len (bv_unsigned buf) sz.

(* [comment removed for export] *)
Definition tags_ok (bs : list byte) (tc psz : Z) : Prop :=
  (0 <= tc)%Z /\ (132 + 12 * tc <= psz <= len)%Z /\
  forall i, (0 <= i < tc)%Z ->
    let off := be32 bs (132 + 12 * i + 4) in
    let s := be32 bs (132 + 12 * i + 8) in
    (4 <= s)%Z /\ (off + s <= psz)%Z.

(* [comment removed for export] *)
Fixpoint zprod (l : list Z) : Z := match l with [] => 1 | x :: r => x * zprod r end%Z.

Definition grid_ok_A2B (P : Z) : Prop :=
  exists (ic oc : Z) (gps : list Z) (g8 g16 : word),
    cell32 segs mem (P + 160 + 144) ic /\ cell32 segs mem (P + 160 + 300) oc /\
    (0 <= ic <= 4)%Z /\ Z.of_nat (length gps) = ic /\ Forall (fun g => (2 <= g <= 255)%Z) gps /\
    (forall i, (0 <= i < ic)%Z -> cell8 segs mem (P + 160 + 148 + i) (nth (Z.to_nat i) gps 0%Z)) /\
    cell64 segs mem (P + 160 + 128) g8 /\ cell64 segs mem (P + 160 + 136) g16 /\
    oc = 3%Z /\
    (ic <> 0%Z ->
       (bv_unsigned g8 <> 0%Z -> inDATA data len (bv_unsigned g8) (oc * zprod gps)) /\
       (bv_unsigned g16 <> 0%Z -> inDATA data len (bv_unsigned g16) (2 * (oc * zprod gps)))).

(* [comment removed for export] *)
Definition profile_ok (bs : list byte) (P : Z) : Prop :=
  exists (psz tc : Z) (hasA2B : Z),
    cell64 segs mem P data /\ cell32 segs mem (P + 8) psz /\ cell32 segs mem (P + 20) tc /\
    tags_ok bs tc psz /\ curves_ok P /\
    cell8 segs mem (P + 966) hasA2B /\ (hasA2B <> 0%Z -> grid_ok_A2B P).

End Invariants.
