(* Copied from proofs/omx-clap-core/fuzz_manifest/lib/A/RT_pf_bz.v; relocated to plugin-hostd/fuzz_command.asan by the GXA address relocator (target fuzz_command.asan): module paths changed; 0 address numerals moved (address checker 0767e70e074a, predict mode, fm.asan -> fuzz_command.asan, symbol + offset; the relocator's table for this file). *)
(* printf_common's call contract at fuzz_manifest.asan, in the Bz vocabulary: the same statements as
   plugin-hostd/fuzz_reply's lib/A/RT_pf_bz.v pcom_pre and pcom_call, at fm's printf_common
   (RT_pf_Tbl.v PF_PRINTF_COMMON); the interceptor cells (fuzz_reply's sni_cells / vfi_cells) are not here, they belong
   to the interceptor chain.

   This file proves no new function. `pcom_call` is the shared ASan runtime's printf_common walk (lib/A/Bz/A/I_pcxlist.v
   pcom_genx_spec, relocated onto fuzz_manifest from fuzz_state 840c4afa7e2) with its section hypothesis rip_stmt
   discharged by R_isPoisoned.v rip_proof; what it adds is the stack bookkeeping that lets a caller with a deeper floor
   lo call it: pcom_genx_spec is used at the floor sp - PCOM_DEPTH (its own window), and the part of the caller's stack
   below that floor is carried across the call untouched (stk_split / stk_merge).

   pcom_pre is pcom_genx_spec's premises over the memory, bundled at that floor. Its argument list (Bz's
   I_pcxgram.parg) and its format check (pcomx_ok, printf_common's own grammar) are the caller's to compute; for a
   fixed format both are closed computations. *)
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import Shadow.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pck I_pcbits I_pchead.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.A Require Import I_pcxgram I_pcxlist R_isPoisoned.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A.Bz.K Require Import I_vprintfw.
From OSSVerify.Proofs.reac_pw.fuzz_segconf.lib.A Require Import RT_pf_Tbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* the measured window is the walk's *)
Lemma pf_pcom_depth : PF_PCOM_DEPTH = PCOM_DEPTH.
Proof. reflexivity. Qed.

(* pcom_genx_spec's premises over memory m, for a call with sp = q, format A and va_list ap, at the floor
   q - PCOM_DEPTH. *)
Definition pcom_pre (A ap q : Z) (m : mem) : Prop :=
  exists (body : list Z) (args : list parg) (cin : list (option Z)) (slots : list word),
    pcomx_ok (body ++ [0]) args = true /\ Forall (fun c => 0 < c < 256) body /\ (1 <= length body)%nat
    /\ bytes_at asegs m A (zb8 (body ++ [0])) /\ A + Z.of_nat (length body) + 3 <= q - PCOM_DEPTH /\ 1 <= A
    /\ (forall i w a, nth_error slots i = Some w -> nth_error args i = Some a -> sarg a ->
          ro_cells asegs m (ap + 8 * Z.of_nat i) [C8 w]
          /\ (ap + 8 * Z.of_nat i + 8 <= q - PCOM_DEPTH \/ q <= ap + 8 * Z.of_nat i))
    /\ 0 <= ap /\ ap + 8 * Z.of_nat (length slots) + 16 < 2^63
    /\ ck_args m (q - PCOM_DEPTH) q slots args (pcx_covs (length (body ++ [0])) (body ++ [0]) args cin)
    /\ chk_ok m A (Z.of_nat (length body) + 1) /\ pctx m.

(* printf_common's call contract for a caller whose stack floor lo is at or below the call's own window. *)
Lemma pcom_call : forall (A ap lo : Z)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 (F : bvmap 5 word) fc (m : mem),
  a1 = Z_to_bv 64 A -> a2 = Z_to_bv 64 ap ->
  stk asegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - PCOM_DEPTH -> kHighShadowEnd + 8 <= lo ->
  bv_unsigned sp <= 2^47 -> bv_unsigned sp mod 16 = 0 -> pcom_pre A ap (bv_unsigned sp) m -> mem_inv asegs m ->
  evt asegs (pcom_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 PF_PRINTF_COMMON) fc None m (seg_rom asegs)).
Proof.
  intros until m. intros EA1 EA2 ST LO LOLO SPH S16 PRE MI.
  destruct PRE as (body & args & cin & slots & OK & FB & L1 & BY & AB & A1 & VS & AP0 & APH & CKA & CHK & PCX).
  destruct (stk_split asegs m lo (bv_unsigned sp - PCOM_DEPTH) (bv_unsigned sp) ST ltac:(lia)) as (STa & STb).
  unfold PF_PRINTF_COMMON.
  eapply evt_mono.
  { apply (pcom_genx_spec rip_proof A body args cin ap (bv_unsigned sp - PCOM_DEPTH) slots);
      first [ exact EA1 | exact EA2 | exact OK | exact FB | exact L1 | exact BY | exact AB | exact A1 | exact VS
            | exact AP0 | exact APH | exact CKA | exact STb | exact CHK | exact PCX | exact MI | exact S16 | exact SPH
            | lia | (unfold kHighShadowEnd in *; lia) ]. }
  intros ms (u0 & u1 & u2 & d0 & d1 & d2 & d3 & d4 & d5 & d6 & d7 & u3 & u4 & u5 & u6 & m' & E & MU & WM & MI' & ST').
  unfold pcom_post. exists u0, u1, u2, d0, d1, d2, d3, d4, d5, d6, d7, u3, u4, u5, u6, m'.
  split; [exact E|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI'|].
  apply (stk_merge asegs m' lo (bv_unsigned sp - PCOM_DEPTH) (bv_unsigned sp)); [| exact ST' | lia].
  apply (stk_transport_disjoint asegs [(bv_unsigned sp - PCOM_DEPTH, bv_unsigned sp)] m m' lo _ STa MU WM).
  cbn [disjoint_from]. split; [lia | exact I].
Qed.
