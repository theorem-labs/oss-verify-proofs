(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From OSSVerify.Proofs.glaze.binary_reflection.lib Require BvWfKernel.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require WdZS.
(* [comment removed for export] *)
Require Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.glaze.binary_reflection.images.AsanUbsan OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Module BoAllocFRun3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3.
Import OSSVerify.glaze.binary_reflection.images.AsanUbsan.
Import ListNotations.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.AmLia.
Import OSSVerify.Proofs.glaze.binary_reflection.lib.HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac am_inner ::= tryif noncert_goal_has_var then (Zify.zify; xlia zchecker) else first [ solve [noncert_clear_all; Zify.zify; xlia zchecker] | Zify.zify; xlia zchecker ].
#[local] Ltac lia ::= ha_first_lia.   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fr_PS (M12 : word -> option byte) (S p : word) (T n n8 : Z) : word -> option byte :=
  wbytes (ps_frame M12 (at_ S (-2208)) (Z_to_bv 64 0x50ae4) (Z_to_bv 64 (0x10ab58 + 728)) (at_ (Z_to_bv 64 T) 80) (Z_to_bv 64 n)
                   (at_ S (-2128)) (at_ (Z_to_bv 64 T) 208) (at_ p (-16)))
         (Z_to_bv 64 (shad p)) (repeat (MemsetLibF.cbyte (Z_to_bv 64 253)) (Z.to_nat (shlen (Z_to_bv 64 n8)))).
Definition fr_P3 (memD : word -> option byte) (S p x22 : word) (T n n8 id last cnt bsz qb : Z) : word -> option byte :=
  let M12 := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T in
  let M13 := fr_PS M12 S p T n n8 in
  fr_c2 M13 S p T n last cnt bsz qb.
Hint Unfold fr_PS fr_P3 : asfr.

Section RUN3.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last cnt bsz qb len : Z) (cpm : byte) (midend : word).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x10ab58.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gcnt : (1 <= cnt < 1021)%Z.
  Hypothesis Gbsz : (0 <= bsz < 2 ^ 40)%Z.
  Hypothesis Gqb : (0 <= qb /\ qb + n <= 2 ^ 20)%Z.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok BSEGS memD p 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 (T + 80)) 32 = true.
  Hypothesis Okb : store_ok BSEGS memD (Z_to_bv 64 last) (Z.to_nat 8192) = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn BSEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).
  Hypothesis C_q1 : rdn BSEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn BSEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn BSEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).
  Hypothesis C_q4 : rdn BSEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn BSEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_i0 : rdn BSEGS memD (at_ S (-8)) 8 = Some (LE8 ra0).
  Hypothesis C_i1 : rdn BSEGS memD (at_ S (-16)) 8 = Some (LE8 s0v).
  Hypothesis C_i2 : rdn BSEGS memD (at_ S (-24)) 8 = Some (LE8 s1v).
  Hypothesis C_i3 : rdn BSEGS memD (at_ S (-32)) 8 = Some (LE8 s2v).
  Hypothesis C_i4 : rdn BSEGS memD (at_ S (-40)) 8 = Some (LE8 s3v).
  Hypothesis C_i5 : rdn BSEGS memD (at_ S (-48)) 8 = Some (LE8 s4v).
  Hypothesis C_i6 : rdn BSEGS memD (at_ S (-56)) 8 = Some (LE8 s5v).
  Hypothesis C_nhi : rdn BSEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn BSEGS memD (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn BSEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_len : rdn BSEGS memD (Z_to_bv 64 (T + 80)) 8 = Some (LE8 (Z_to_bv 64 len)).
  Hypothesis C_last : rdn BSEGS memD (Z_to_bv 64 (T + 96)) 8 = Some (LE8 (Z_to_bv 64 last)).
  Hypothesis C_qb : rdn BSEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_bsz : rdn BSEGS memD (Z_to_bv 64 (last + 8)) 8 = Some (LE8 (Z_to_bv 64 bsz)).
  Hypothesis C_cnt : rdn BSEGS memD (Z_to_bv 64 (last + 16)) 8 = Some (LE8 (Z_to_bv 64 cnt)).

End RUN3.
End FPGen.
End BoAllocFRun3.
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32 OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF. Import OSSVerify.Proofs.glaze.binary_reflection.lib.Common.PropExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec OSSVerify.Proofs.glaze.binary_reflection.lib.Common.CatExec.CatSim OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare.SeqExec OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.StepTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.Hoare OSSVerify.Proofs.glaze.binary_reflection.lib.Common.StoreOk OSSVerify.Proofs.glaze.binary_reflection.lib.Common.WalkTac OSSVerify.Proofs.glaze.binary_reflection.lib.Common.MmapSim OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.RefMemcpyLib OSSVerify.Proofs.glaze.binary_reflection.lib.Mh32.LibMaskBits OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF.MemSplit.
Require OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4. Import OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtLib OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab.AsanAcct OSSVerify.Proofs.glaze.binary_reflection.lib.AsVocab OSSVerify.Proofs.glaze.binary_reflection.lib.AsIface3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtUnwindT OSSVerify.Proofs.glaze.binary_reflection.lib.MemsetLibF OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtRegion OSSVerify.Proofs.glaze.binary_reflection.lib.AsRtPoison OSSVerify.Proofs.glaze.binary_reflection.lib.BoRtPoisonI OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocFTac OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF3 BoAllocFRun3 OSSVerify.Proofs.glaze.binary_reflection.lib.BoAllocF4.
From OSSVerify.glaze.binary_reflection.images Require Import AsanUbsan.
Import ListNotations.
From OSSVerify.Proofs.glaze.binary_reflection.lib Require Import HsAtom.
#[local] Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
#[local] Ltac ha_prev := tryif noncert_goal_has_var then (Zify.zify; (xlia zchecker)) else (first [ solve [ noncert_clear_all; Zify.zify; (xlia zchecker) ] | Zify.zify; (xlia zchecker) ]).
#[local] Ltac lia ::= first [ solve [ ha_tiers ltac:(ha_lia0) ] | ha_prev ].   (* [comment removed for export] *)
Open Scope bv_scope.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

Abbreviation BSEGS := AsanUbsan.M.loaded_segments.
#[local] Abbreviation U := bv_unsigned.
#[local] Abbreviation LE8 v := (word_to_le_bytes 8 v).
#[local] Abbreviation LE4 z := (word_to_le_bytes 4 (Z_to_bv 64 z)).

(* [comment removed for export] *)

Section FPGen.
Context {fx : FPState}.

(* [comment removed for export] *)
Definition fr_P3e (memD : word -> option byte) (S p x22 : word) (T n n8 id cnt24 k ba qb : Z) (bst bcs : list byte) : word -> option byte :=
  let M12 := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T in
  let M13 := fr_PS M12 S p T n n8 in
  fr_e1e M13 S p T n cnt24 k ba qb bst bcs.
Definition fr_P3f (memD : word -> option byte) (S p x22 : word) (T n n8 id cnt24 k ba qb last len : Z) (bst bcs : list byte) : word -> option byte :=
  let M12 := fr_c1 memD S p (Z_to_bv 64 0x6eea4) (Z_to_bv 64 1) (at_ S (-2128)) (at_ S (-81)) x22 id T in
  let M13 := fr_PS M12 S p T n n8 in
  fr_e1f M13 S p T n cnt24 k ba qb last len bst bcs.

Section RUN3N.
  Variables (memD rom : word -> option byte) (rD : bvmap 5 word).
  Variables (S p ra0 tp x22 s0v s1v s2v s3v s4v s5v : word) (T n n8 id fl last qb len cnt24 k spb ba : Z) (cpm : byte) (midend : word) (bst bcs : list byte).
  #[local] Abbreviation thr := (Z_to_bv 64 T).
  (* [comment removed for export] *)
  Hypothesis D1 : getr rD 2 = at_ S (-2176).
  Hypothesis D8 : getr rD 8 = at_ p (-16).
  Hypothesis D9 : getr rD 9 = at_ S (-2128).
  Hypothesis D10 : getr rD 10 = Z_to_bv 64 id.
  Hypothesis D18 : getr rD 18 = Z_to_bv 64 0x10ab58.
  Hypothesis D19 : getr rD 19 = Z_to_bv 64 0.
  Hypothesis D20 : getr rD 20 = thr.
  Hypothesis D21 : getr rD 21 = at_ S (-81).
  Hypothesis D22 : getr rD 22 = x22.
  Hypothesis D4 : getr rD 4 = tp.
  (* [comment removed for export] *)
  Hypothesis GS : (2 ^ 32 + 4096 <= U S /\ U S + 16 <= 2 ^ 47 /\ U S mod 16 = 0)%Z.
  Hypothesis Gp : (AIMGHI + 16 <= U p /\ (PSIDE (U p) n8 /\ U p + n8 <= U S - 3584) /\ U p mod 16 = 0)%Z.
  Hypothesis GT : (4096 <= T /\ (TSIDE T /\ T + 4096 <= U S - 3584))%Z.
  Hypothesis GpT : (U p + n8 <= T \/ T + 4096 <= U p - 16)%Z.
  Hypothesis Gn : (1 <= n <= 2 ^ 28)%Z.
  Hypothesis Gn8 : AsRtRegion.down8 (n + 7) = n8 /\ (n <= n8 <= n + 7)%Z /\ (n8 mod 8 = 0)%Z /\ (8 <= n8)%Z.
  Hypothesis Gid : (0 <= id < 2 ^ 32)%Z.
  Hypothesis Gfl : (0 <= fl /\ fl + 4096 <= AIMGHI)%Z.
  Hypothesis Glast : (0x10007fff8000 <= last /\ last + 8192 <= U S - 3584)%Z.
  Hypothesis GlastT : (last + 8192 <= T \/ T + 4096 <= last)%Z.
  Hypothesis Glastp : (last + 8192 <= U p - 16 \/ U p + n8 <= last)%Z.
  Hypothesis Gqb : (0 <= qb /\ qb + n + 8192 <= 2 ^ 20)%Z.
  Hypothesis GT16 : (T mod 16 = 0)%Z.
  Hypothesis Gcnt24 : (1 <= cnt24 <= 16)%Z.
  Hypothesis Gk : (0 <= k < 2 ^ 32)%Z.
  Hypothesis Gspb : (0 <= spb)%Z.
  Hypothesis Gbak : (spb + 3 * 2 ^ 35 + 16 * k)%Z = ba.
  Hypothesis Gba : (0x10007fff8000 <= ba /\ ba + 8192 <= U S - 3584)%Z.
  Hypothesis GbaT : (ba + 8192 <= T \/ T + 4096 <= ba)%Z.
  Hypothesis Gbap : (ba + 8192 <= U p - 16 \/ U p + n8 <= ba)%Z.
  Hypothesis Gbalast : (last + 8192 <= ba \/ ba + 8192 <= last)%Z.
  Hypothesis Lbst : length bst = 8%nat.
  Hypothesis Lbcs : length bcs = 8%nat.
  Hypothesis Glen : (1 <= len < 2 ^ 40)%Z.
  Hypothesis Gmid : (U midend < 2 ^ 64)%Z.
  Hypothesis Hret : ret_ok ra0.
  (* [comment removed for export] *)
  Hypothesis Hstk : store_ok BSEGS memD (at_ S (-2304)) 2304 = true.
  Hypothesis Okp : store_ok BSEGS memD p 8 = true.
  Hypothesis Oksh : store_ok BSEGS memD (Z_to_bv 64 (shad p)) (Z.to_nat (n8 / 8)) = true.
  Hypothesis OkT : store_ok BSEGS memD (Z_to_bv 64 T) (Z.to_nat 4096) = true.
  Hypothesis Okba : store_ok BSEGS memD (Z_to_bv 64 ba) 32 = true.
  (* [comment removed for export] *)
  Hypothesis C_q0 : rdn BSEGS memD (at_ S (-2136)) 8 = Some (LE8 (Z_to_bv 64 0x6ef14)).
  Hypothesis C_q1 : rdn BSEGS memD (at_ S (-2144)) 8 = Some (LE8 S).
  Hypothesis C_q2 : rdn BSEGS memD (at_ S (-2152)) 8 = Some (LE8 p).
  Hypothesis C_q3 : rdn BSEGS memD (at_ S (-2160)) 8 = Some (LE8 (Z_to_bv 64 0x6eea4)).
  Hypothesis C_q4 : rdn BSEGS memD (at_ S (-2168)) 8 = Some (LE8 (Z_to_bv 64 1)).
  Hypothesis C_q5 : rdn BSEGS memD (at_ S (-2176)) 8 = Some (LE8 (at_ S (-2128))).
  Hypothesis C_i0 : rdn BSEGS memD (at_ S (-8)) 8 = Some (LE8 ra0).
  Hypothesis C_i1 : rdn BSEGS memD (at_ S (-16)) 8 = Some (LE8 s0v).
  Hypothesis C_i2 : rdn BSEGS memD (at_ S (-24)) 8 = Some (LE8 s1v).
  Hypothesis C_i3 : rdn BSEGS memD (at_ S (-32)) 8 = Some (LE8 s2v).
  Hypothesis C_i4 : rdn BSEGS memD (at_ S (-40)) 8 = Some (LE8 s3v).
  Hypothesis C_i5 : rdn BSEGS memD (at_ S (-48)) 8 = Some (LE8 s4v).
  Hypothesis C_i6 : rdn BSEGS memD (at_ S (-56)) 8 = Some (LE8 s5v).
  Hypothesis C_nhi : rdn BSEGS memD (at_ p (-14)) 2 = Some (word_to_le_bytes 2 (Z_to_bv 64 (n / 2 ^ 32))).
  Hypothesis C_nlo : rdn BSEGS memD (at_ p (-12)) 4 = Some (LE4 (n mod 2 ^ 32)).
  Hypothesis C_mcs : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 808)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 20))).
  Hypothesis C_msz : rdn BSEGS memD (Z_to_bv 64 (0x10ab58 + 792)) 8 = Some (LE8 (Z_to_bv 64 (2 ^ 28))).
  Hypothesis C_gfl : rdn BSEGS memD (Z_to_bv 64 0x105f10) 8 = Some (LE8 (Z_to_bv 64 fl)).
  Hypothesis C_mff : rdn BSEGS memD (Z_to_bv 64 (fl + 48)) 4 = Some (LE4 0).
  Hypothesis C_gsh : rdn BSEGS memD (Z_to_bv 64 0x105f18) 8 = Some (LE8 (Z_to_bv 64 0x10e1b8)).
  Hypothesis C_sh : rdn BSEGS memD (Z_to_bv 64 0x10e1b8) 8 = Some (LE8 (Z_to_bv 64 0x7fff8000)).
  Hypothesis C_gmb : rdn BSEGS memD (Z_to_bv 64 0x105f20) 8 = Some (LE8 (Z_to_bv 64 0x10eea8)).
  Hypothesis C_mb : rdn BSEGS memD (Z_to_bv 64 0x10eea8) 8 = Some (LE8 (Z_to_bv 64 0)).
  Hypothesis C_gme : rdn BSEGS memD (Z_to_bv 64 0x105f28) 8 = Some (LE8 (Z_to_bv 64 0x10eeb0)).
  Hypothesis C_me : rdn BSEGS memD (Z_to_bv 64 0x10eeb0) 8 = Some (LE8 midend).
  Hypothesis C_ghe : rdn BSEGS memD (Z_to_bv 64 0x105f30) 8 = Some (LE8 (Z_to_bv 64 0x10eea0)).
  Hypothesis C_he : rdn BSEGS memD (Z_to_bv 64 0x10eea0) 8 = Some (LE8 (Z_to_bv 64 0x7fffffffffff)).
  Hypothesis C_grm : rdn BSEGS memD (Z_to_bv 64 0x105f38) 8 = Some (LE8 (Z_to_bv 64 0x107e58)).
  Hypothesis C_rm : rdn BSEGS memD (Z_to_bv 64 0x107e58) 8 = Some (LE8 (Z_to_bv 64 0xfc38c)).
  Hypothesis C_cpm : rdn BSEGS memD (Z_to_bv 64 0x10da1c) 1 = Some [cpm].
  Hypothesis C_cpm1 : U cpm <> 0%Z.
  Hypothesis C_qb : rdn BSEGS memD (Z_to_bv 64 (T + 104)) 8 = Some (LE8 (Z_to_bv 64 qb)).
  Hypothesis C_cnt24 : rdn BSEGS memD (Z_to_bv 64 (T + 2128)) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 cnt24)).
  Hypothesis C_cs : rdn BSEGS memD (Z_to_bv 64 (T + 2136)) 8 = Some bcs.
  Hypothesis C_k : rdn BSEGS memD (Z_to_bv 64 (T + 2144 + 4 * (cnt24 - 1))) 4 = Some (word_to_le_bytes 4 (Z_to_bv 64 k)).
  Hypothesis C_st : rdn BSEGS memD (Z_to_bv 64 (T + 2784)) 8 = Some bst.
  Hypothesis C_spb : rdn BSEGS memD (Z_to_bv 64 0x10ab78) 8 = Some (LE8 (Z_to_bv 64 spb)).



End RUN3N.

End FPGen.
