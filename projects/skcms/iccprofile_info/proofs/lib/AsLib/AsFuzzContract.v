(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim Hoare Frame FuzzContract.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

(* [comment removed for export] *)
Definition AS_SB      : Z := 0x7fff8000.       (* [comment removed for export] *)
Definition AS_LOWEND  : Z := 0x7fff7000.       (* [comment removed for export] *)
Definition AS_HIGHBEG : Z := 0x10007fff8000.   (* [comment removed for export] *)
Definition AS_IMGLO   : Z := 0x10000.          (* [comment removed for export] *)
Definition AS_IMGHI   : Z := 0x5fc000.         (* [comment removed for export] *)
Abbreviation AS_STKLO := 0x7fff7f800000%Z.   (* [comment removed for export] *)
Abbreviation AS_CEILHI := 0x7fffff800000%Z.  (* [comment removed for export] *)

(* [comment removed for export] *)
Definition appm (a n : Z) : Prop :=
  (4096 <= a)%Z /\ (0 <= n)%Z /\ (a + n <= 2 ^ 47)%Z /\
  (a + n <= AS_LOWEND \/ AS_HIGHBEG <= a)%Z /\ (a + n <= AS_IMGLO \/ AS_IMGHI <= a)%Z.

(* [comment removed for export] *)
Definition FS_SIZE    : Z := 0xb09000.
Definition FS_HINT0   : Z := 0.        (* [comment removed for export] *)
Definition FS_HINT5   : Z := 40.       (* [comment removed for export] *)
Definition FS_SSL     : Z := 88.       (* [comment removed for export] *)
Definition FS_NEEDSGC : Z := 96.       (* [comment removed for export] *)
Definition FS_FLAGS0  : Z := 0x1000.   Definition FS_FLAGS0_LEN : Z := 0x4000.
Definition FS_FLAGS5  : Z := 0x8c00.   Definition FS_FLAGS5_LEN : Z := 0x200.
Definition FS_FRAMES0 : Z := 0x9000.   Definition FS_FRAMES_LEN : Z := 0x100000.
Definition FS_FRAMES5 : Z := 0x509000.
Definition FS_SHFRAMES_LEN : Z := 0x20000.   (* [comment removed for export] *)

(* [comment removed for export] *)
Record as_abi : Type := AA {
  aa_entry : Z;              (* [comment removed for export] *)
  aa_gfool : Z;              (* [comment removed for export] *)
  aa_depth : Z;              (* [comment removed for export] *)
  aa_tp    : Z;              (* [comment removed for export] *)
  aa_tsdv  : Z;              (* [comment removed for export] *)
  aa_dtv   : Z;              (* [comment removed for export] *)
  aa_ro    : list (Z * Z);   (* [comment removed for export] *)
  aa_c64   : list (Z * Z);   (* [comment removed for export] *)
  aa_c32   : list (Z * Z);   (* [comment removed for export] *)
  aa_c8    : list (Z * Z);   (* [comment removed for export] *)
  aa_r64   : list Z;         (* [comment removed for export] *)
  aa_shb   : list (Z * Z)    (* [comment removed for export] *)
}.

Definition asan_abi : as_abi := AA
  0x7fee8 0x5d9240 3584 0x5d9b70 0x5faf18 0x5d9b90
  [(0x20d00, 0x20f20); (0x10338, 0x10340)]%Z
  [ (0x9eaf0, 0xa6bb8); (0xa6bb8, AS_SB);          (* [comment removed for export] *)
    (0x9eb48, 0xa6bc0);                              (* [comment removed for export] *)
    (0x9eb10, 0xa0950); (0xa0950, 0x98220);        (* [comment removed for export] *)
    (0xa0948, 0x97e1c);                              (* [comment removed for export] *)
    (0x9f658, 0xa7899);                              (* [comment removed for export] *)
    (0xa0888, 0x98a10);                              (* [comment removed for export] *)
    (0x9f7d0, 1); (0x9f7d8, 0xfffffffffffff800);     (* [comment removed for export] *)
    (0x9eaf8, 0xa78a8); (0xa78a8, 0);               (* [comment removed for export] *)
    (0x9eb00, 0xa78b0);                              (* [comment removed for export] *)
    (0x9eb08, 0xa78a0); (0xa78a0, 0x7fffffffffff);  (* [comment removed for export] *)
    (0x9eae0, 0x1386e8);                              (* [comment removed for export] *)
    (0x9eb40, 0x136658);                              (* [comment removed for export] *)
    (0x9f7e0, 0x8);                                   (* [comment removed for export] *)
    (0x5d9b68, 0x5d9b90); (0x5d9b98, 0x5da370);        (* [comment removed for export] *)
    (0x5d9b18, 0x5faf18) ]%Z                           (* [comment removed for export] *)
  [ (0xa6bc0, 1);                                     (* [comment removed for export] *)
    (0xa6424, 0);                                     (* [comment removed for export] *)
    (0x136658, 0) ]%Z                                  (* [comment removed for export] *)
  [ (0xa7898, 1);                                     (* [comment removed for export] *)
    (0xa7899, 1);                                     (* [comment removed for export] *)
    (0xa6420, 1);                                     (* [comment removed for export] *)
    (0x138771, 1) ]%Z                                  (* [comment removed for export] *)
  [ 0xa78b0 ]%Z
  [ (0x7fffc1d4, 0); (0x7fffc1d5, 0); (0x7fffc1d6, 4) ]%Z.   (* [comment removed for export] *)

Section WithSegs.
Variable segs : list Segment.

(* [comment removed for export] *)
Definition acell (mem : word -> option byte) (a : Z) (w : nat) (v : Z) : Prop :=
  rdn segs mem (Z_to_bv 64 a) w = Some (word_to_le_bytes w (Z_to_bv 64 v)).
Definition acellw (mem : word -> option byte) (a : Z) (v : word) : Prop :=
  rdn segs mem (Z_to_bv 64 a) 8 = Some (word_to_le_bytes 8 v).
Definition areadable (mem : word -> option byte) (a : Z) (w : nat) : Prop :=
  exists bs, rdn segs mem (Z_to_bv 64 a) w = Some bs.
(* [comment removed for export] *)
Definition azero (mem : word -> option byte) (lo n : Z) : Prop :=
  forall i, (0 <= i < n)%Z -> mem (Z_to_bv 64 (lo + i)) = Some (Z_to_bv 8 0).
Definition awritable (mem : word -> option byte) (lo n : Z) : Prop :=
  RiscvSemantics.store_ok segs mem (Z_to_bv 64 lo) (Z.to_nat n) = true.

(* [comment removed for export] *)
Definition as_shad_byte (x d n : Z) : Z :=
  if Z.leb ((x / 8 + 1) * 8) (d + n) then 0 else ((d + n) mod 8).
Definition ashdata (mem : word -> option byte) (d n : Z) : Prop :=
  forall g, (d / 8 <= g)%Z -> (8 * g < d + n)%Z ->
    mem (Z_to_bv 64 (AS_SB + g)) = Some (Z_to_bv 8 (as_shad_byte (8 * g) d n)).

(* [comment removed for export] *)
Definition heap_cell_ok (ceil a fs : Z) : Prop :=
  appm a 8 /\ (a + 8 <= ceil)%Z /\ (a + 8 <= fs \/ fs + FS_SIZE <= a)%Z.

(* [comment removed for export] *)
Definition as_mod (A : as_abi) (sp fs : Z) : list (word * Z) :=
  [ (Z_to_bv 64 (sp - aa_depth A), aa_depth A);
    (Z_to_bv 64 (aa_gfool A), 4);
    (Z_to_bv 64 (fs + FS_HINT0), 8); (Z_to_bv 64 (fs + FS_HINT5), 8);
    (Z_to_bv 64 (fs + FS_FLAGS0), FS_FLAGS0_LEN); (Z_to_bv 64 (fs + FS_FLAGS5), FS_FLAGS5_LEN);
    (Z_to_bv 64 (fs + FS_FRAMES0), FS_FRAMES_LEN); (Z_to_bv 64 (fs + FS_FRAMES5), FS_FRAMES_LEN);
    (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES0) / 8), FS_SHFRAMES_LEN);
    (Z_to_bv 64 (AS_SB + (fs + FS_FRAMES5) / 8), FS_SHFRAMES_LEN) ]%Z.

Definition as_fuzz_contract (A : as_abi) : Prop :=
  forall (FP : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte)
         (ret sp data : word) (n : Z) (bs : list byte)
         (fs : Z) (h0 h5 ctx thr t48 t56 dtls v24 : word) (ceil : Z),
    let tp := aa_tp A in let D := aa_depth A in
    (* [comment removed for export] *)
    getr regs 1 = ret -> ret_ok ret ->
    getr regs 2 = sp -> getr regs 4 = Z_to_bv 64 tp ->
    getr regs 10 = data -> getr regs 11 = Z_to_bv 64 n ->
    (* [comment removed for export] *)
    (0 <= n < 2 ^ 26)%Z -> Z.of_nat (length bs) = n ->
    (bv_unsigned sp mod 16 = 0)%Z -> (bv_unsigned data mod 16 = 0)%Z ->
    (AS_STKLO <= ceil)%Z -> (ceil <= bv_unsigned sp - D)%Z -> (bv_unsigned sp < 2 ^ 47)%Z ->
    ((0 < n)%Z -> appm (bv_unsigned data) n /\ (bv_unsigned data + n <= ceil
            /\ (bv_unsigned data + n <= fs \/ fs + FS_SIZE <= bv_unsigned data))%Z) ->
    appm fs FS_SIZE -> (fs + FS_SIZE <= ceil)%Z -> (fs mod 4096 = 0)%Z ->
    (* [comment removed for export] *)
    (forall i, (0 <= i < n)%Z ->
       mem (Z_to_bv 64 (bv_unsigned data + i)) = Some (nth (Z.to_nat i) bs (Z_to_bv 8 0))) ->
    ashdata mem (bv_unsigned data) n ->
    (* [comment removed for export] *)
    awritable mem (bv_unsigned sp - D) D ->
    (forall i, (bv_unsigned sp - D <= i < bv_unsigned sp)%Z ->
       Forall (fun seg => (i < Z.of_N (seg_base seg) \/ Z.of_N (seg_base seg) + Z.of_N (seg_size seg) <= i)%Z) segs) ->
    azero mem (AS_SB + (bv_unsigned sp - D) / 8) (D / 8) ->
    (* [comment removed for export] *)
    awritable mem (aa_gfool A) 4 -> areadable mem (aa_gfool A) 4 ->
    (* [comment removed for export] *)
    (forall lo hi i, In (lo, hi) (aa_ro A) -> (lo <= i < hi)%Z -> mem (Z_to_bv 64 i) = None) ->
    (* [comment removed for export] *)
    (forall a v, In (a, v) (aa_c64 A) -> acell mem a 8 v) ->
    (forall a v, In (a, v) (aa_c32 A) -> acell mem a 4 v) ->
    (forall a v, In (a, v) (aa_c8 A) -> acell mem a 1 v) ->
    (forall a, In a (aa_r64 A) -> areadable mem a 8) ->
    (forall a v, In (a, v) (aa_shb A) -> mem (Z_to_bv 64 a) = Some (Z_to_bv 8 v)) ->
    (* [comment removed for export] *)
    acellw mem (aa_tsdv A) ctx -> heap_cell_ok ceil (bv_unsigned ctx + 152) fs ->
    acellw mem (bv_unsigned ctx + 152) thr ->
    heap_cell_ok ceil (bv_unsigned thr + 48) fs -> heap_cell_ok ceil (bv_unsigned thr + 56) fs ->
    acellw mem (bv_unsigned thr + 48) t48 -> acellw mem (bv_unsigned thr + 56) t56 ->
    acellw mem (tp + 0x8) dtls -> (0 < bv_unsigned dtls < 2 ^ 64 - 1)%Z ->
    heap_cell_ok ceil (bv_unsigned dtls + 24) fs ->
    acellw mem (bv_unsigned dtls + 24) v24 -> (bv_unsigned v24 <> 0)%Z ->
    (* [comment removed for export] *)
    acell mem (tp + 0) 8 fs ->
    acellw mem (fs + FS_HINT0) h0 -> acellw mem (fs + FS_HINT5) h5 ->
    acell mem (fs + FS_SSL) 8 20 -> acell mem (fs + FS_NEEDSGC) 1 0 ->
    azero mem (fs + FS_FLAGS0) FS_FLAGS0_LEN -> azero mem (fs + FS_FLAGS5) FS_FLAGS5_LEN ->
    awritable mem (fs + FS_HINT0) 8 -> awritable mem (fs + FS_HINT5) 8 ->
    awritable mem (fs + FS_FLAGS0) FS_FLAGS0_LEN -> awritable mem (fs + FS_FLAGS5) FS_FLAGS5_LEN ->
    awritable mem (fs + FS_FRAMES0) FS_FRAMES_LEN -> awritable mem (fs + FS_FRAMES5) FS_FRAMES_LEN ->
    awritable mem (AS_SB + (fs + FS_FRAMES0) / 8) FS_SHFRAMES_LEN ->
    awritable mem (AS_SB + (fs + FS_FRAMES5) / 8) FS_SHFRAMES_LEN ->
    (* [comment removed for export] *)
    exists (FP' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte),
      msteps segs (mkst (FP:=FP) regs (Z_to_bv 64 (aa_entry A)) mem rom)
                  (mkst (FP:=FP') regs' ret mem' rom)
      /\ getr regs' 10 = Z_to_bv 64 0
      /\ (forall r, In r fuzz_kept -> getr regs' r = getr regs r)
      /\ frame_mod mem mem' (as_mod A (bv_unsigned sp) fs)
      /\ azero mem' (fs + FS_FLAGS0) FS_FLAGS0_LEN
      /\ azero mem' (fs + FS_FLAGS5) FS_FLAGS5_LEN.

End WithSegs.
