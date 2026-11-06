(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Require Import OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.PropExec OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatExec
               OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.CatSim OSSVerify.Proofs.coturn.FuzzStunClient.lib.Common.StoreOk
               OSSVerify.Proofs.coturn.FuzzStunClient.lib.Frame.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Existing Instance PropExec.fx0.  (* [comment removed for export] *)
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Record FAParams := mkFA {
  fa_entry  : Z;               (* [comment removed for export] *)
  fa_ret    : Z;               (* [comment removed for export] *)
  fa_tp     : Z;               (* [comment removed for export] *)
  fa_frame  : Z;               (* [comment removed for export] *)
  fa_shoff  : Z;               (* [comment removed for export] *)
  fa_prng   : Z;               (* [comment removed for export] *)
  fa_errno  : Z;               (* [comment removed for export] *)
  fa_tsd    : Z;               (* [comment removed for export] *)
  fa_pristine : list (Z * Z);  (* [comment removed for export] *)
  fa_kcells : list (Z * Z * Z);(* [comment removed for export] *)
  fa_gsh    : list (Z * Z * Z);(* [comment removed for export] *)
  fa_nmax   : Z;               (* [comment removed for export] *)
  fa_imgend : Z                (* [comment removed for export] *)
}.

(* [comment removed for export] *)
Definition FS_LEN      : Z := 11571200.          (* [comment removed for export] *)
Definition FS_HINTS    : Z := 88.                (* [comment removed for export] *)
Definition FS_SSL      : Z := 88.                (* [comment removed for export] *)
Definition FS_NEEDSGC  : Z := 96.                (* [comment removed for export] *)
Definition FS_FLAGS    : Z := 4096.              (* [comment removed for export] *)
Definition FS_FLAGS_LEN: Z := 32768.
Definition FS_FRAMES   : Z := 36864.             (* [comment removed for export] *)
Definition FS_FRAMES_LEN : Z := 5 * 2^20.

(* [comment removed for export] *)
Definition HIGHMEM_LO : Z := 0x10007fff8000.
(* [comment removed for export] *)
Definition LOWMEM_TOP : Z := 0x7fff7000.
Definition VA_HI      : Z := 2^47.

(* [comment removed for export] *)
Definition F_SPLO : Z := 0x7fff80000000 - 4096.
Definition F_SPHI : Z := 0x800000000000.

(* [comment removed for export] *)
Definition ekept : list reg := [1; 2; 3; 4; 8; 9; 18; 19; 20; 21; 22; 23; 24; 25; 26; 27]%bv.
Definition ekeeps (regs regs' : bvmap 5 word) : Prop :=
  forall r : reg, In r ekept -> getr regs' r = getr regs r.


Section WithFA.
  Variable SEGS : list Segment.
  Variable P : FAParams.

  Definition pristine (mem : word -> option byte) (lo hi : Z) : Prop :=           (* [comment removed for export] *)
    forall a : word, lo <= bv_unsigned a < hi -> mem a = None.

  (* [comment removed for export] *)
  Definition readable (mem : word -> option byte) (a n : Z) : Prop :=
    forall i, 0 <= i < n -> exists b, rdn SEGS mem (Z_to_bv 64 (a + i)) 1 = Some [b].
  (* [comment removed for export] *)
  Definition writable (mem : word -> option byte) (a n : Z) : Prop :=
    forall i, 0 <= i < n -> store_ok SEGS mem (Z_to_bv 64 (a + i)) 1 = true.
  (* [comment removed for export] *)
  Definition zeroes (mem : word -> option byte) (a n : Z) : Prop :=
    forall i, 0 <= i < n -> rdn SEGS mem (Z_to_bv 64 (a + i)) 1 = Some [Z_to_bv 8 0].
  (* [comment removed for export] *)
  Definition filled (mem : word -> option byte) (a n c : Z) : Prop :=
    forall i, 0 <= i < n -> rdn SEGS mem (Z_to_bv 64 (a + i)) 1 = Some [Z_to_bv 8 c].
  (* [comment removed for export] *)
  Definition cell (mem : word -> option byte) (a w v : Z) : Prop :=
    rdn SEGS mem (Z_to_bv 64 a) (Z.to_nat w) = Some (word_to_le_bytes (Z.to_nat w) (Z_to_bv 64 v)).

  Definition shadow (a : Z) : Z := fa_shoff P + a / 8.
  (* [comment removed for export] *)
  Definition rd8 (x : Z) : Z := x - x mod 8.

  (* [comment removed for export] *)
  Definition FA_writes (sp fs : Z) : list (Z * Z) :=
    [ (sp - fa_frame P, fa_frame P)                                   (* [comment removed for export] *)
    ; (shadow (sp - fa_frame P), fa_frame P / 8)                      (* [comment removed for export] *)
    ; (fs, FS_HINTS)                                                  (* [comment removed for export] *)
    ; (fs + FS_FLAGS, FS_FLAGS_LEN)                                   (* [comment removed for export] *)
    ; (fs + FS_FRAMES, FS_FRAMES_LEN)                                 (* [comment removed for export] *)
    ; (shadow (fs + FS_FRAMES), FS_FRAMES_LEN / 8)                    (* [comment removed for export] *)
    ; (fa_prng P, 8)                                                  (* [comment removed for export] *)
    ; (fa_errno P, 4) ].                                              (* [comment removed for export] *)
  Definition FA_footprint (sp fs : Z) : list (word * Z) :=
    map (fun r => (Z_to_bv 64 (fst r), snd r)) (FA_writes sp fs).

  (* [comment removed for export] *)
  Definition FA_reads (sp data n fs ctx thr db : Z) : list (Z * Z) :=
    [ (data, n); (shadow data - 2, n / 8 + 6); (rd8 (shadow data), n / 8 + 16)   (* [comment removed for export] *)
    ; (shadow (sp - fa_frame P) - 8, 8); (shadow sp, 10); (sp, 16)    (* [comment removed for export] *)
    ; (shadow (fs + FS_FRAMES) - 8, 8); (shadow (fs + FS_FRAMES) + FS_FRAMES_LEN / 8, 8)
    ; (fs + FS_SSL, 8); (fs + FS_NEEDSGC, 1)
    ; (fa_tp P, 8); (fa_tp P + 0x8, 8); (fa_tsd P, 8); (ctx + 0x98, 8); (thr + 0x30, 16); (db + 0x18, 8) ]
    ++ map (fun c => (fst (fst c), snd (fst c))) (fa_kcells P)
    ++ map (fun c => (fst (fst c), snd (fst c))) (fa_gsh P).

  (* [comment removed for export] *)
  Definition apart_writes (sp fs a w : Z) : Prop :=
    Forall (fun r => a + w <= fst r \/ fst r + snd r <= a) (FA_writes sp fs ++ [(sp, 16); (shadow sp, 2)]).
    (* [comment removed for export] *)

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
  Definition F_contract_asan : Prop :=
    forall (regs : bvmap 5 word) (mem rom : word -> option byte) (sp data : word) (n fs ctx thr db : Z),
      let usp := bv_unsigned sp in let ud := bv_unsigned data in
      (* [comment removed for export] *)
      getr regs 1 = Z_to_bv 64 (fa_ret P) ->
      getr regs 2 = sp ->
      getr regs 4 = Z_to_bv 64 (fa_tp P) ->
      getr regs 10 = data ->
      getr regs 11 = Z_to_bv 64 n ->
      (* [comment removed for export] *)
      0 <= n < fa_nmax P ->
      ud <> 0 ->                                                                   (* [comment removed for export] *)
      ud + n < 2 ^ 63 ->                                                           (* [comment removed for export] *)
      ud mod 16 = 0 ->                                                             (* [comment removed for export] *)
      (0 < n -> (ud + n <= LOWMEM_TOP \/ HIGHMEM_LO <= ud) /\ ud + n <= VA_HI - 64) ->   (* [comment removed for export] *)
      usp mod 16 = 0 ->                                                            (* [comment removed for export] *)
      F_SPLO <= usp -> usp + 16 <= F_SPHI ->                                       (* [comment removed for export] *)
      fs mod 4096 = 0 -> (fs + FS_LEN <= LOWMEM_TOP \/ HIGHMEM_LO <= fs) -> fs + FS_LEN <= VA_HI ->   (* [comment removed for export] *)
      fa_imgend P <= fs ->                                                         (* [comment removed for export] *)
      (* [comment removed for export] *)
      (ud + n + 4096 <= usp - fa_frame P \/ usp + 4112 <= ud) ->                   (* [comment removed for export] *)
      (fs + FS_LEN + 4096 <= usp - fa_frame P \/ usp + 4112 <= fs) ->              (* [comment removed for export] *)
      (fs + FS_LEN + 4096 <= ud \/ ud + n <= fs) ->                                (* [comment removed for export] *)
      (* [comment removed for export] *)
      readable mem ud n ->
      (0 < n -> forall g, 0 <= 8 * g < n ->
         rdn SEGS mem (Z_to_bv 64 (shadow ud + g)) 1
         = Some [Z_to_bv 8 (if 8 * g + 8 <=? n then 0 else n - 8 * g)]) ->
      (0 < n -> readable mem (shadow ud - 2) (n / 8 + 6)) ->                     (* [comment removed for export] *)
      (0 < n -> readable mem (rd8 (shadow ud)) (rd8 (shadow (ud + n - 1)) + 8 - rd8 (shadow ud))) ->  (* [comment removed for export] *)
      (* [comment removed for export] *)
      writable mem (usp - fa_frame P) (fa_frame P + 16) -> readable mem usp 16 ->   (* [comment removed for export] *)
      zeroes   mem (shadow (usp - fa_frame P)) (fa_frame P / 8) ->
      writable mem (shadow (usp - fa_frame P)) (fa_frame P / 8 + 2) ->          (* [comment removed for export] *)
      readable mem (shadow (usp - fa_frame P) - 8) 8 -> readable mem (shadow usp) 10 ->   (* [comment removed for export] *)
      (* [comment removed for export] *)
      readable mem fs FS_HINTS -> writable mem fs FS_HINTS ->
      cell mem (fs + FS_SSL) 8 20 ->
      cell mem (fs + FS_NEEDSGC) 1 0 ->
      zeroes mem (fs + FS_FLAGS) FS_FLAGS_LEN -> writable mem (fs + FS_FLAGS) FS_FLAGS_LEN ->
      readable mem (fs + FS_FRAMES) FS_FRAMES_LEN -> writable mem (fs + FS_FRAMES) FS_FRAMES_LEN ->
      readable mem (shadow (fs + FS_FRAMES) - 8) (FS_FRAMES_LEN / 8 + 16) ->
      writable mem (shadow (fs + FS_FRAMES)) (FS_FRAMES_LEN / 8) ->
      (* [comment removed for export] *)
      cell mem (fa_tp P) 8 fs ->                                                   (* [comment removed for export] *)
      cell mem (fa_tp P + 0x8) 8 db ->                                            (* [comment removed for export] *)
      cell mem (db + 0x18) 8 (fa_tp P) ->                                          (* [comment removed for export] *)
      cell mem (fa_tsd P) 8 ctx ->                                                 (* [comment removed for export] *)
      cell mem (ctx + 0x98) 8 thr ->                                               (* [comment removed for export] *)
      readable mem (thr + 0x30) 16 ->                                              (* [comment removed for export] *)
      ctx <> 0 -> thr <> 0 -> 0 < db -> db + 32 <= 2^64 -> 0 <= ctx -> ctx + 160 <= 2^64 -> 0 <= thr -> thr + 64 <= 2^64 ->  (* [comment removed for export] *)
      apart_writes usp fs (db + 0x18) 8 -> apart_writes usp fs (ctx + 0x98) 8 -> apart_writes usp fs (thr + 0x30) 16 ->
      (* [comment removed for export] *)
      Forall (fun c => cell mem (fst (fst c)) (snd (fst c)) (snd c)) (fa_kcells P) ->
      Forall (fun r => filled mem (fst (fst r)) (snd (fst r)) (snd r)) (fa_gsh P) ->
      Forall (fun r => pristine mem (fst r) (snd r)) (fa_pristine P) ->
      readable mem (fa_prng P) 8 -> writable mem (fa_prng P) 8 ->
      readable mem (fa_errno P) 4 -> writable mem (fa_errno P) 4 ->
      (* [comment removed for export] *)
      exists regs' mem',
        msteps SEGS (mkst regs (Z_to_bv 64 (fa_entry P)) mem rom)
                    (mkst regs' (Z_to_bv 64 (fa_ret P)) mem' rom)
        /\ ekeeps regs regs'                                                       (* [comment removed for export] *)
        /\ getr regs' 10 = Z_to_bv 64 0                                            (* [comment removed for export] *)
        /\ frame_mod mem mem' (FA_footprint usp fs)                                (* [comment removed for export] *)
        /\ zeroes mem' (shadow (usp - fa_frame P)) (fa_frame P / 8)               (* [comment removed for export] *)
        /\ zeroes mem' (fs + FS_FLAGS) FS_FLAGS_LEN.                               (* [comment removed for export] *)
End WithFA.
