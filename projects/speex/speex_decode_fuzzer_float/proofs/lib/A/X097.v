(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType Fs State Monad Specs Run.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.AS Require Import X0mx X0k2.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.LibA Require Import X1di X1cs X1da X1dg X1ck.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.Spec Require Import X1r2 X1nt X1rh X1re.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X0bp X0j9 X0ec X001 X00b X04b X07z X05o X05s X05l X05m X09f X069 X09e
X082 X08y X091 X08x X08u.
From OSSVerify.Proofs.speex.speex_decode_fuzzer_float.lib.A Require Import X09c.
Import ListNotations.
Open Scope Z_scope.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Section NbEHd.
Variable RT : rt_sig.
Variable PMc : Model -> Prop.
Variable X : @nbinvA bptr.
Variables (Σ0 : rts RT) (mE : mem).
Variables (r : smrec) (mo olp : Z).
Local Notation ST := (x_st X). Local Notation OUT := (x_out X). Local Notation A := (x_A X). Local Notation FF := (x_ff X). Local Notation SF := (x_sf X).
Local Notation usp := (x_usp X).

Definition nbEH_sig (Σ : rts RT) (cr : Z) : Prop :=
rt_live RT Σ = rt_live RT Σ0 /\ rt_frames RT Σ = rt_frames RT Σ0 /\ rt_sp0 RT Σ = rt_sp0 RT Σ0 /\ rt_credit RT Σ = cr /\ rt_pois RT Σ = rt_pois RT Σ0.

Definition nbEH_mem (Σ : rts RT) (m : mem) : Prop :=
ART RT Σ m /\ nbacc X m /\ wmono asegs mE m /\ rt_pres_fp (rt_live RT Σ0) (rt_frames RT Σ0) (usp - NBD_FRAME) (nbW_EH X) mE m.

Definition at_ELc (bp sub : Z) (st : nb_state bptr) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT), ASTA RT Σ PMc (fun ms => at_EL X r mo olp bp sub st b ms /\ nbEH_mem Σ (ms_mem ms)) c /\ nbEH_sig Σ (rt_credit RT Σ0).

Definition R_EX (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) : bvmap 5 word :=
mkR xra (Z_to_bv 64 (usp + -544)) (x_gp X) (x_tp X) t0 t1 t2 (Z_to_bv 64 usp) (Z_to_bv 64 (usp + -544)) a0 a1 a2 a3 a4 a5 a6 a7
(Z_to_bv 64 SF) (Z_to_bv 64 0) (Z_to_bv 64 (FF + 928)) (Z_to_bv 64 (ST + 2944)) (Z_to_bv 64 (ST + 2936)) (Z_to_bv 64 40)
(Z_to_bv 64 olp) (Z_to_bv 64 (ST + 2940)) (Z_to_bv 64 SHB) (Z_to_bv 64 (ST + 2032)) t3 t4 t5 t6.
Definition at_EXc (bp : Z) (st : nb_state bptr) (b : bits_st bptr) : config -> Prop :=
fun c => exists (Σ : rts RT) (Fx : bvmap 5 word) (fc : bv 32) (m : mem) (xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word)
(j : nb_junk) (ows sws : list word) (s : nbslots) (ff : nbff),
ASTA RT Σ PMc (eq (MS (R_EX xra t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6) Fx (Z_to_bv 64 NBE_PC_EXIT) fc None m (seg_rom asegs))) c
/\ frm0 fc /\ nbctx X m st b j ows sws s ff SC_E /\ slots_EL ST OUT A FF bp 4 s /\ v72 s = Z_to_bv 64 (Z.shiftr (ST + 2208) 3 + SHB)
/\ smrec_at mo = Some r /\ nb_submodeID st = mo /\ 17 <= bp <= 144
/\ nbEH_mem Σ m /\ nbEH_sig Σ (rt_credit RT Σ0).
End NbEHd.
