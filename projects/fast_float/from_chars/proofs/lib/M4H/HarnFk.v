(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import PropExec.
From OSSVerify.Proofs.fast_float.from_chars.lib.Common Require Import FxLin FxCore FxSound FxMem FxRgs FxFacts FxStep FxSubst FxEnt FxDrv FxCall FxGenA.
From OSSVerify.Proofs.fast_float.from_chars.lib.HXH Require Import HxBaseH.
From OSSVerify.Proofs.fast_float.from_chars.lib.AAC Require Import AcCarve AcSteps AcMALp AcCarveP.
From OSSVerify.Proofs.fast_float.from_chars.lib.M4H Require Import HarnLoop HarnSite.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition fk_flo (k : Z) : Z := 0x1000 + Z.shiftl (Z.shiftl (Z.shiftr 1023 (10 - k)) (10 - k)) 5.   (* [comment removed for export] *)
Definition fk_nfr (k : Z) : Z := 2 ^ (14 - k).                                                    (* [comment removed for export] *)
Definition fk_aro (k : Z) : Z := 0x9000 + k * 2 ^ 20.
Definition fk_fsz (k : Z) : Z := 64 * 2 ^ k.
Definition HINTof (S : sst) (k : Z) : lin := match cell S (laddc (FSof S) (8 * k)) with Some l => l | None => lconst 0 end.

(* [comment removed for export] *)
Fixpoint cut_k (i : nat) (b : lin) (c : tree bval) (k0 : rkind) (z : Z) (ps : list (Z * rkind)) : list rstep :=
  match ps with
  | [] => []
  | (d, k1) :: ps' =>
      match ps' with
      | [] => []
      | [(_, k2)] => [RSplit i (RG b (lconst d) k1 (sub_cont c 0 d)) (RG (laddc b d) (lconst (z - d)) k2 (sub_cont c d (z - d))) d]
      | _ => RSplit i (RG b (lconst d) k1 (sub_cont c 0 d)) (RG (laddc b d) (lconst (z - d)) k0 (sub_cont c d (z - d))) d ::
             cut_k (Datatypes.S i) (laddc b d) (sub_cont c d (z - d)) k0 (z - d) ps'
      end
  end.
Definition cut_at (S : sst) (a : lin) (z : Z) (ps : list (Z * rkind)) : option (list rstep) :=
  match find_idx (s_rgs S) a 0 with
  | Some (i, 0) => match nth_error (s_rgs S) i with
                   | Some R => if lin_eqb (rg_size R) (lconst z) then Some (cut_k i (rg_base R) (rg_cont R) (rg_kind R) z ps) else None
                   | None => None
                   end
  | _ => None
  end.

(* [comment removed for export] *)
Definition isolate_k (a : lin) (n : Z) (k : rkind) (S : sst) : option (list rstep) :=
  match find_idxc (s_rgs S) a n 0 with
  | Some (i, o) => match nth_error (s_rgs S) i with
                   | Some R => match is_const (rg_size R) with
                               | Some z =>
                                   if (Z.eqb o 0 && Z.eqb n z)%bool then Some []
                                   else Some (cut_k i (rg_base R) (rg_cont R) (rg_kind R) z
                                                ((if Z.eqb o 0 then [] else [(o, rg_kind R)]) ++ [(n, k)] ++
                                                 (if Z.eqb (o + n) z then [] else [(z - o - n, rg_kind R)])))
                               | None => None
                               end
                   | None => None
                   end
  | None => None
  end.
(* [comment removed for export] *)
Definition SBH : Z := 0x7fff8000.
Definition RT_WINS (S : sst) : list (lin * Z * rkind) :=
  let CTX := match cell S (lconst 0x639328) with Some l => l | None => lconst 0 end in
  [ (lconst 0xe461c, 12, RW); (lconst 0xe4db8, 12, RW); (lconst 0xe5a98, 2, RW); (lconst 0xe5aa0, 24, RW);
    (lconst 0x174858, 4, RW); (lconst 0x176971, 1, RW);
    (lconst 0x617f28, 8, RW); (lconst 0x617f78, 56, RW); (lconst 0x639328, 8, RW);
    (CTX, 160, RW); (THRof S, 80, RW); (BLKof S, 32, RW);
    (lconst (SBH + 0x2060), 0x30, RZ); (lconst (SBH + 0x44fe), 32, RZ); (lconst (SBH + 0x4538), 1302, RZ);
    (lconst (SBH + 0x4a50), 20, RZ); (lconst (SBH + 0x4a68), 32, RZ); (lconst (SBH + 0x4a89), 0x2e, RZ);
    (lconst (SBH + 0x4ab8), 0x12, RZ); (lconst (SBH + 0x4aca), 0x66, RZ) ].
Definition rt_win (j : nat) (S : sst) : option (list rstep) :=
  match nth_error (RT_WINS S) j with Some (a, n, k) => isolate_k a n k S | None => None end.
Definition RT_NWINS : nat := 20.
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fk_cut_fsh (p : sst -> lin) (S : sst) : option (list rstep) :=
  cut_at S (p S) 32 [(8, RZ); (8, RZ); (8, RZ); (8, RZ)].

(* [comment removed for export] *)
Definition fk_prep_lo (S : sst) : option (list rstep) :=
  cut_at S (FSof S) 0x209000 [(0x1000, RW); (0x7000, RZ); (0x800, RZ); (0x400, RZ); (0x200, RZ); (0x200, RZ); (0x1ff000, RZ); (0x1000, RW)].
Definition fk_prep_mrg (S : sst) : option (list rstep) := mergecc_at S (laddc (FSof S) 0x208000).
(* [comment removed for export] *)
Definition fk_prep_all (S : sst) : option (list rstep) :=
  cut_at S (FSof S) 0xb09000 [(0x1000, RW); (0x7000, RZ); (0x800, RZ); (0x400, RZ); (0x200, RZ); (0x200, RZ); (0x1ff000, RZ); (0x101000, RW);
                              (0x100000, RZ); (0x100000, RW); (0x100000, RW); (0x500000, RZ)].
Definition fk_prep_hi (S : sst) : option (list rstep) :=
  cut_at S (laddc (FSof S) 0x309000) 0x800000 [(0x100000, RZ); (0x100000, RW); (0x100000, RW); (0x500000, RZ)].
Definition fk_prep_sh (S : sst) : option (list rstep) :=
  cut_at S (oshadow (FSof S)) 0x161200 [(0x41000, RZ); (0x20200, RW); (0x20000, RW); (0x20000, RW); (0x20000, RW); (0xa0000, RZ)].

(* [comment removed for export] *)
Definition fk_flag (S : sst) (k : Z) (Y : lin) : lin := ladd (laddc (FSof S) (fk_flo k)) Y.
Definition fk_slot (S : sst) (k : Z) (Y : lin) : lin := ladd (laddc (FSof S) (fk_aro k)) (lscale (fk_fsz k) Y).
Definition fk_carve_fl (k : Z) (Y : sst -> lin) (S : sst) : option (nat * lin * lin) := split_at S (fk_flag S k (Y S)) (lconst 1).
Definition fk_carve_ar (k : Z) (Y : sst -> lin) (S : sst) : option (nat * lin * lin) := split_at S (fk_slot S k (Y S)) (lconst (fk_fsz k)).
Definition fk_carve_sh (k : Z) (Y : sst -> lin) (S : sst) : option (nat * lin * lin) :=
  split_at S (oshadow (fk_slot S k (Y S))) (lconst (fk_fsz k / 8)).

(* [comment removed for export] *)
Definition idx_at (S : sst) (p : lin) : option nat := find_base (s_rgs S) p 0.
Definition prev_idx (S : sst) (p : lin) : option nat := match idx_at S p with Some (Datatypes.S i) => Some i | _ => None end.
Definition fk_unz (fl : sst -> lin) (S : sst) : option nat := idx_at S (fl S).
Definition fk_drop (p : sst -> lin) (S : sst) : option (list rstep) := match idx_at S (p S) with Some i => Some [RDrop i] | None => None end.
(* [comment removed for export] *)
Definition fk_mrg3 (p : sst -> lin) (S : sst) : option (nat * nat) := match prev_idx S (p S) with Some i => Some (i, 3%nat) | None => None end.

(* [comment removed for export] *)
Definition Y4 (S : sst) : lin := hidx (HINTof S 4) 10.
(* [comment removed for export] *)
Fixpoint find_piece (rgs : list region) (a0 : lin) (sz : Z) (i : nat) : option nat :=
  match rgs with
  | [] => None
  | R :: rs => let d := lsub (rg_base R) a0 in
               if (lin_eqb (rg_size R) (lconst sz) && Z.eqb (l_c d) 0 && match l_t d with [] => false | _ => true end)%bool then Some i
               else find_piece rs a0 sz (Datatypes.S i)
  end.
Definition fk_mrg3_at (a0 : sst -> lin) (sz : Z) (S : sst) : option (nat * nat) :=
  match find_piece (s_rgs S) (a0 S) sz 0 with Some (Datatypes.S i) => Some (i, 3%nat) | _ => None end.
Definition fk4_fl0 (S : sst) : lin := laddc (FSof S) (fk_flo 4).
Definition fk4_ar0 (S : sst) : lin := laddc (FSof S) (fk_aro 4).
Definition fk4_sh0 (S : sst) : lin := oshadow (laddc (FSof S) (fk_aro 4)).
(* [comment removed for export] *)
Definition h4_cell (S : sst) : option (nat * Z) := match at_c S (laddc (FSof S) 32) 8 with Some (i, o, _) => Some (i, o) | None => None end.
Definition h5_cell (S : sst) : option (nat * Z) := match at_c S (laddc (FSof S) 40) 8 with Some (i, o, _) => Some (i, o) | None => None end.
Definition h4_dec (S : sst) : option (nat * Z * Z) := match h4_cell S with Some (i, o) => Some (i, o, 10) | None => None end.
Definition h4_lo (S : sst) : option (nat * Z * lin) := match h4_cell S with Some (i, o) => Some (i, o, hbase (HINTof S 4) 10) | None => None end.
Definition h4_hi (S : sst) : option (nat * Z * lin) := match h4_cell S with Some (i, o) => Some (i, o, laddc (hbase (HINTof S 4) 10) 1023) | None => None end.
