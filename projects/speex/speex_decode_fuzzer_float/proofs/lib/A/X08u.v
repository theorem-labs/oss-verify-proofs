(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05l X09f X069 X09e X082 X08y
X091 X08x.

From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B Require X12c X14x X0r0 X0ra X0v9 X0wl X0x2 X0yt X0zq X0zp.
Module B_TWIN.

Import OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X12c OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X14x OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0r0 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0ra OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0v9 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0wl OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0x2 OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0yt OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zq OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.B.X0zp.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NBD_CALLEE_STACK : Z := 8192.

Definition NBD_EH_CREDIT : Z := 5.

Section NbdCps.
Variable RT : rt_sig.
Context {ptr : Type}.

Definition nbsig (Σ : rts RT) (X : @nbinvA ptr) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat) : Prop :=
rt_frames RT Σ = (x_ff X, NBD_FCLASS) :: fr0
/\ In (x_st X, NBSTATE_SIZEOF) (rt_live RT Σ)
/\ In (PD, ND) (rt_live RT Σ) /\ PD <= x_D X /\ x_D X + x_dsz X <= PD + ND /\ PD <> x_st X
/\ In (fh, kh) fr0
/\ fh <= x_out X /\ x_out X + 4 * Z.of_nat (x_nout X) <= fh + fs_size kh - 8
/\ fh <= x_A X /\ x_A X + BITS_SIZEOF <= fh + fs_size kh - 8
/\ fh <= x_stereo X /\ x_stereo X + 8 <= fh + fs_size kh - 8
/\ pois_above (rt_pois RT Σ) (x_usp X - NBD_FRAME)
/\ rt_sp0 RT Σ - STACK_WIN <= x_lo X /\ x_lo X + RT_STACK + NBD_CALLEE_STACK <= x_usp X - NBD_FRAME /\ x_usp X + 16 <= USTACK_TOP.

Definition nbacc (X : @nbinvA ptr) (m : mem) : Prop :=
acc bsegs m (x_out X) (4 * Z.of_nat (x_nout X)) /\ acc bsegs m (x_A X) BITS_SIZEOF /\ acc bsegs m (x_stereo X) 8.

Definition nbW_EH (X : @nbinvA ptr) : list (Z * Z) :=
[(x_st X, x_st X + NBSTATE_SIZEOF); (x_out X, x_out X + 4 * Z.of_nat (x_nout X)); (x_A X, x_A X + BITS_SIZEOF);
(x_ff X, x_ff X + 2048); (x_sf X, x_sf X + 256); (x_usp X - NBD_FRAME, x_usp X)].

Definition nbd_EH_cps : Prop :=
forall (Σ : rts RT) PMc (X : @nbinvA ptr) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat) (r : smrec) (mo olp : Z) (st : nb_state ptr) (b : bits_st ptr) (ms : machine_state),
fdfs_only PMc -> mat_stable PMc -> x_tp X = Z_to_bv 64 0x638c98 ->
nbx_ok X -> at_E_A X r mo olp 40 0 st b ms ->
nbsig Σ X fr0 PD ND fh kh -> nbacc X (ms_mem ms) -> ART RT Σ (ms_mem ms) ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> NBD_EH_CREDIT <= rt_credit RT Σ ->
sm_ltp_unquant (smr_sm r) <> None -> sm_innovation_unquant (smr_sm r) <> None ->
match subframes_pure 4 0 (smr_sm r) olp st b with
| Some (st', b') =>
cps bsegs (ASTA RT Σ PMc (eq ms))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms' => at_X_A X 0 (nb_end st') b' ms' /\ ART RT Σ' (ms_mem ms') /\ nbacc X (ms_mem ms')
/\ wmono bsegs (ms_mem ms) (ms_mem ms')
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (x_usp X - NBD_FRAME) (nbW_EH X) (ms_mem ms) (ms_mem ms')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - NBD_EH_CREDIT <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ)
| None => True
end.
End NbdCps.
End B_TWIN.

Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Definition NBD_CALLEE_STACK : Z := 8192.

Definition NBD_EH_CREDIT : Z := 4.

Section NbdCps.
Variable RT : rt_sig.
Context {ptr : Type}.

Definition nbsig (Σ : rts RT) (X : @nbinvA ptr) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat) : Prop :=
rt_frames RT Σ = (x_ff X, NBD_FCLASS) :: fr0
/\ In (x_st X, NBSTATE_SIZEOF) (rt_live RT Σ)
/\ In (PD, ND) (rt_live RT Σ) /\ PD <= x_D X /\ x_D X + x_dsz X <= PD + ND /\ PD <> x_st X
/\ In (fh, kh) fr0
/\ fh <= x_out X /\ x_out X + 4 * Z.of_nat (x_nout X) <= fh + fs_size kh - 8
/\ fh <= x_A X /\ x_A X + BITS_SIZEOF <= fh + fs_size kh - 8
/\ fh <= x_stereo X /\ x_stereo X + 8 <= fh + fs_size kh - 8
/\ pois_above (rt_pois RT Σ) (x_usp X - NBD_FRAME)
/\ rt_sp0 RT Σ - STACK_WIN <= x_lo X /\ x_lo X + RT_STACK + NBD_CALLEE_STACK <= x_usp X - NBD_FRAME /\ x_usp X + 16 <= USTACK_TOP.

Definition nbacc (X : @nbinvA ptr) (m : mem) : Prop :=
acc asegs m (x_out X) (4 * Z.of_nat (x_nout X)) /\ acc asegs m (x_A X) BITS_SIZEOF /\ acc asegs m (x_stereo X) 8.

Definition nbW_EH (X : @nbinvA ptr) : list (Z * Z) :=
[(x_st X, x_st X + NBSTATE_SIZEOF); (x_out X, x_out X + 4 * Z.of_nat (x_nout X)); (x_A X, x_A X + BITS_SIZEOF);
(x_ff X, x_ff X + 2048); (x_sf X, x_sf X + 256); (x_usp X - NBD_FRAME, x_usp X)].

Definition nbd_EH_cps : Prop :=
forall (Σ : rts RT) PMc (X : @nbinvA ptr) (fr0 : list (Z * nat)) (PD ND fh : Z) (kh : nat) (r : smrec) (mo olp : Z) (st : nb_state ptr) (b : bits_st ptr) (ms : machine_state),
fdfs_only PMc -> mat_stable PMc -> x_tp X = Z_to_bv 64 0x630458 ->
nbx_ok X -> at_E_A X r mo olp 40 0 st b ms ->
nbsig Σ X fr0 PD ND fh kh -> nbacc X (ms_mem ms) -> ART RT Σ (ms_mem ms) ->
(length (rt_frames RT Σ) < FRAMES_MAX)%nat -> NBD_EH_CREDIT <= rt_credit RT Σ ->
sm_ltp_unquant (smr_sm r) <> None -> sm_innovation_unquant (smr_sm r) <> None ->
match subframes_pure 4 0 (smr_sm r) olp st b with
| Some (st', b') =>
cps asegs (ASTA RT Σ PMc (eq ms))
(fun c => exists (Σ' : rts RT),
ASTA RT Σ' PMc (fun ms' => at_X_A X 0 (nb_end st') b' ms' /\ ART RT Σ' (ms_mem ms') /\ nbacc X (ms_mem ms')
/\ wmono asegs (ms_mem ms) (ms_mem ms')
/\ rt_pres_fp (rt_live RT Σ) (rt_frames RT Σ) (x_usp X - NBD_FRAME) (nbW_EH X) (ms_mem ms) (ms_mem ms')) c
/\ rt_live RT Σ' = rt_live RT Σ /\ rt_frames RT Σ' = rt_frames RT Σ /\ rt_sp0 RT Σ' = rt_sp0 RT Σ
/\ rt_credit RT Σ - NBD_EH_CREDIT <= rt_credit RT Σ' <= rt_credit RT Σ /\ rt_pois RT Σ' = rt_pois RT Σ)
| None => True
end.
End NbdCps.
