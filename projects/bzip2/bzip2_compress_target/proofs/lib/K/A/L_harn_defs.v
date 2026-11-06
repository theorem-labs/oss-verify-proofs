(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Shadow.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Layout RT_iface R_unwind_chain D_libiface L_hkit.
Module TwinB__.
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Shadow.
Import OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.Layout.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.RT_iface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.R_unwind_chain.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.D_libiface.TwinB__ OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A.L_hkit.TwinB__.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition B2BC_COST : Z := 2^29.
Definition B2BD_COST : Z := 2^29.
Definition B2B_LIVE : Z := 8.
Definition B2B_FRAMES : nat := 8.
Definition B2B_STACK : Z := FUZZ_STACK - 256.
Definition RA_B2BC : Z := 0x814a4.         (* [comment removed for export] *)
Definition RA_B2BD : Z := 0x814e4.         (* [comment removed for export] *)
Definition RA_HARN : Z := 0x81200.         (* [comment removed for export] *)

Section HarnStmt.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.

(* [comment removed for export] *)
Definition harn_record (m : mem) (sp s0 : word) : Prop := uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) [RA_HARN].

(* [comment removed for export] *)
Definition b2bc_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (zb dl d : Z) (bs junk : list byte) (lo : Z),
  let len := Z.of_nat (length bs) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 zb -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 len -> a4 = Z_to_bv 64 (bs_of len) -> a5 = Z_to_bv 64 0 ->
  a6 = Z_to_bv 64 (wf_of len) -> tp = Z_to_bv 64 0x6094d8 -> ra = Z_to_bv 64 RA_B2BC ->
  len < 2^26 -> 0 < d < 2^64 -> bytes_at bsegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + len <= p + n /\ (p, n) <> (zb, nZ_of len)) \/ bs = []) ->
  In (zb, nZ_of len) (rt_live RT Σ) -> rw_cells bsegs m zb [CB (Z.to_nat (nZ_of len)) junk] ->
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= dl /\ dl + 4 <= f + fs_size k - 8) ->
  rw_cells bsegs m dl [C4 (Z_to_bv 64 (nZ_of len))] -> dl mod 8 = 0 -> ro_cells bsegs m (shad dl) [C1 (Z_to_bv 8 4)] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->      (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) + B2B_LIVE <= LIVE_MAX -> (length (rt_frames RT Σ) + B2B_FRAMES <= FRAMES_MAX)%nat -> B2BC_COST <= rt_credit RT Σ ->
  harn_record m sp s0 ->
  LIB m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + B2B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_b2bc m)))
    (fun c => exists (Σ' : rts RT) (rc dlv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rc) m' ms
          /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(zb, zb + nZ_of len); (dl, dl + 4)] m m'
          /\ rw_cells bsegs m' dl [C4 (Z_to_bv 64 dlv)] /\ LIB m'
          /\ ((rc = 0 /\ exists str, enc_ok bs (bs_of len) (wf_of len) str /\ dlv = Z.of_nat (length str) /\ dlv <= nZ_of len
               /\ bytes_at bsegs m' zb str)
              \/ (-9 <= rc < 0))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - B2BC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition b2bd_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (ob dl zb cap ocap zcap : Z) (z junk : list byte) (sm : bool) (lo : Z),
  let zlen := Z.of_nat (length z) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 ob -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 zb -> a3 = Z_to_bv 64 zlen -> a4 = Z_to_bv 64 (if sm then 1 else 0) -> a5 = Z_to_bv 64 0 ->
  tp = Z_to_bv 64 0x6094d8 -> ra = Z_to_bv 64 RA_B2BD ->
  0 <= cap < 2^27 -> zlen <= zcap -> zcap < 2^27 -> bytes_at bsegs m zb z ->
  In (zb, zcap) (rt_live RT Σ) -> In (ob, ocap) (rt_live RT Σ) -> cap <= ocap -> ob <> zb -> rw_cells bsegs m ob [CB (Z.to_nat cap) junk] ->
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= dl /\ dl + 4 <= f + fs_size k - 8) ->
  rw_cells bsegs m dl [C4 (Z_to_bv 64 cap)] -> dl mod 8 = 0 -> ro_cells bsegs m (shad dl) [C1 (Z_to_bv 8 4)] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->      (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) + B2B_LIVE <= LIVE_MAX -> (length (rt_frames RT Σ) + B2B_FRAMES <= FRAMES_MAX)%nat -> B2BD_COST <= rt_credit RT Σ ->
  harn_record m sp s0 ->
  LIB m -> ART RT Σ m -> mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + B2B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps bsegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_b2bd m)))
    (fun c => exists (Σ' : rts RT) (rc dlv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rc) m' ms
          /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(ob, ob + cap); (dl, dl + 4)] m m'
          /\ rw_cells bsegs m' dl [C4 (Z_to_bv 64 dlv)] /\ LIB m'
          /\ ((rc = 0 /\ exists out, dec_ok z sm cap out /\ dlv = Z.of_nat (length out) /\ dlv <= cap /\ bytes_at bsegs m' ob out)
              \/ (rc <> 0 /\ -9 <= rc <= 4))) c      (* [comment removed for export] *)
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - B2BD_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition round_trip_weak : Prop :=
  forall bs k w str sm cap out, Z.of_nat (length bs) <= cap -> enc_ok bs k w str -> dec_ok str sm cap out -> out = bs.

End HarnStmt.
End TwinB__.
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.AS Require Import ShapeAlg AsanAcct.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.Lib Require Import PropExec MState Mem Frame Cells Step Arr Exec ImageA RzCPS.
From OSSVerify.Proofs.bzip2.bzip2_compress_target.lib.K.A Require Import Layout Shadow RT_iface R_unwind_chain D_libiface L_hkit.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition B2BC_COST : Z := 2^29.
Definition B2BD_COST : Z := 2^29.
Definition B2B_LIVE : Z := 8.
Definition B2B_FRAMES : nat := 8.
Definition B2B_STACK : Z := FUZZ_STACK - 256.
Definition RA_B2BC : Z := 0x81a58.         (* [comment removed for export] *)
Definition RA_B2BD : Z := 0x81a98.         (* [comment removed for export] *)
Definition RA_HARN : Z := 0x817b4.         (* [comment removed for export] *)

Section HarnStmt.
Variable RT : rt_sig.
Variable LIB : mem -> Prop.
Variable enc_ok : list byte -> Z -> Z -> list byte -> Prop.
Variable dec_ok : list byte -> bool -> Z -> list byte -> Prop.

(* [comment removed for export] *)
Definition harn_record (m : mem) (sp s0 : word) : Prop := uw_chain USTACK_TOP m (bv_unsigned sp) (bv_unsigned s0) [RA_HARN].

(* [comment removed for export] *)
Definition b2bc_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (zb dl d : Z) (bs junk : list byte) (lo : Z),
  let len := Z.of_nat (length bs) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 zb -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 d -> a3 = Z_to_bv 64 len -> a4 = Z_to_bv 64 (bs_of len) -> a5 = Z_to_bv 64 0 ->
  a6 = Z_to_bv 64 (wf_of len) -> tp = Z_to_bv 64 0x5fc0d8 -> ra = Z_to_bv 64 RA_B2BC ->
  len < 2^26 -> 0 < d < 2^64 -> bytes_at asegs m d bs ->
  ((exists p n, In (p, n) (rt_live RT Σ) /\ p <= d /\ d + len <= p + n /\ (p, n) <> (zb, nZ_of len)) \/ bs = []) ->
  In (zb, nZ_of len) (rt_live RT Σ) -> rw_cells asegs m zb [CB (Z.to_nat (nZ_of len)) junk] ->
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= dl /\ dl + 4 <= f + fs_size k - 8) ->
  rw_cells asegs m dl [C4 (Z_to_bv 64 (nZ_of len))] -> dl mod 8 = 0 -> ro_cells asegs m (shad dl) [C1 (Z_to_bv 8 4)] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->      (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) + B2B_LIVE <= LIVE_MAX -> (length (rt_frames RT Σ) + B2B_FRAMES <= FRAMES_MAX)%nat -> B2BC_COST <= rt_credit RT Σ ->
  harn_record m sp s0 ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + B2B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_b2bc m)))
    (fun c => exists (Σ' : rts RT) (rc dlv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rc) m' ms
          /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(zb, zb + nZ_of len); (dl, dl + 4)] m m'
          /\ rw_cells asegs m' dl [C4 (Z_to_bv 64 dlv)] /\ LIB m'
          /\ ((rc = 0 /\ exists str, enc_ok bs (bs_of len) (wf_of len) str /\ dlv = Z.of_nat (length str) /\ dlv <= nZ_of len
               /\ bytes_at asegs m' zb str)
              \/ (-9 <= rc < 0))) c
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - B2BC_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition b2bd_cps : Prop :=
  forall (Σ : rts RT) PMc (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         F fc (m : mem) (ob dl zb cap ocap zcap : Z) (z junk : list byte) (sm : bool) (lo : Z),
  let zlen := Z.of_nat (length z) in
  fdfs_only PMc -> mat_stable PMc ->
  a0 = Z_to_bv 64 ob -> a1 = Z_to_bv 64 dl -> a2 = Z_to_bv 64 zb -> a3 = Z_to_bv 64 zlen -> a4 = Z_to_bv 64 (if sm then 1 else 0) -> a5 = Z_to_bv 64 0 ->
  tp = Z_to_bv 64 0x5fc0d8 -> ra = Z_to_bv 64 RA_B2BD ->
  0 <= cap < 2^27 -> zlen <= zcap -> zcap < 2^27 -> bytes_at asegs m zb z ->
  In (zb, zcap) (rt_live RT Σ) -> In (ob, ocap) (rt_live RT Σ) -> cap <= ocap -> ob <> zb -> rw_cells asegs m ob [CB (Z.to_nat cap) junk] ->
  (exists f k, In (f, k) (rt_frames RT Σ) /\ f <= dl /\ dl + 4 <= f + fs_size k - 8) ->
  rw_cells asegs m dl [C4 (Z_to_bv 64 cap)] -> dl mod 8 = 0 -> ro_cells asegs m (shad dl) [C1 (Z_to_bv 8 4)] ->
  (forall p n, In (p, n) (rt_live RT Σ) -> 0 < n) ->      (* [comment removed for export] *)
  Z.of_nat (length (rt_live RT Σ)) + B2B_LIVE <= LIVE_MAX -> (length (rt_frames RT Σ) + B2B_FRAMES <= FRAMES_MAX)%nat -> B2BD_COST <= rt_credit RT Σ ->
  harn_record m sp s0 ->
  LIB m -> ART RT Σ m -> mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> rt_sp0 RT Σ - STACK_WIN <= lo -> lo + B2B_STACK <= bv_unsigned sp ->
  bv_unsigned sp + 16 <= USTACK_TOP -> bv_unsigned sp mod 16 = 0 -> bv_unsigned sp <= rt_sp0 RT Σ ->
  cps asegs (ASTA RT Σ PMc (eq (entry_st ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                                         t3 t4 t5 t6 F fc e_b2bd m)))
    (fun c => exists (Σ' : rts RT) (rc dlv : Z),
       ASTA RT Σ' PMc (fun ms => exists m', ret_st ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 (Z_to_bv 64 rc) m' ms
          /\ rt_after_f RT Σ' (bv_unsigned sp) lo m m'
          /\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (bv_unsigned sp) [(ob, ob + cap); (dl, dl + 4)] m m'
          /\ rw_cells asegs m' dl [C4 (Z_to_bv 64 dlv)] /\ LIB m'
          /\ ((rc = 0 /\ exists out, dec_ok z sm cap out /\ dlv = Z.of_nat (length out) /\ dlv <= cap /\ bytes_at asegs m' ob out)
              \/ (rc <> 0 /\ -9 <= rc <= 4))) c      (* [comment removed for export] *)
       /\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
       /\ rt_credit RT Σ - B2BD_COST <= rt_credit RT Σ').

(* [comment removed for export] *)
Definition round_trip_weak : Prop :=
  forall bs k w str sm cap out, Z.of_nat (length bs) <= cap -> enc_ok bs k w str -> dec_ok str sm cap out -> out = bs.

End HarnStmt.
