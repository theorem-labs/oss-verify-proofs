(* Image B twin of lib/A/RT_pf_bz.v at d49bd1db505: module paths lib.A -> lib.B; 4 image numerals moved to fuzz_reply.asan-ubsan by symbol + offset, each checked against that image (CHAINB-numerals.tsv sha256 3cedf5e564f7; internal record). *) (* The Bz-vocabulary pieces of fuzz_reply.asan-ubsan's snprintf interceptor chain (RT_pf_stmt.v): the runtime cells the
   interceptors read, printf_common's start premise, and printf_common's call contract at any stack floor.

   This file proves no new function.  `pcom_call` is a Theorem Labs lane's printf_common walk (lib/A/Bz/A/I_pcxlist.v
   pcom_genx_spec, relocated by R4Printf) with its section hypothesis rip_stmt discharged by R_isPoisoned.v rip_proof;
   what it adds is the stack bookkeeping that lets a caller with a deeper floor lo call it: pcom_genx_spec is used at
   the floor sp - PCOM_DEPTH (its own window, as the donor's Prog/vsnprintf_wrap_front.v:193 does), and the part of
   the caller's stack below that floor is carried across the call untouched (stk_split / stk_merge).

   pcom_pre is pcom_genx_spec's premises over the memory, bundled at that floor.  Its argument list (Bz's
   I_pcxgram.parg) and its format check (pcomx_ok, printf_common's own grammar) are NOT GXA's printf_model: relating
   the two for a format is the caller's obligation (for a fixed format such as fuzz_reply's "%s %d " both are closed
   computations). *)
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz Require BvWfKernel.
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import Shadow.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_ikit.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import I_pck I_pcbits I_pchead.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.A Require Import I_pcxgram I_pcxlist R_isPoisoned.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B.Bz.K Require Import I_vprintfw I_vfprintfw I_vsnprintfw.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.B Require Import RT_pf_Tbl.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* ---- the runtime cells ---- *)

(* What ___interceptor_snprintf and ___interceptor_vsnprintf read: asan_inited = 1 (TryAsanInitFromRtl), the GOT word
   of common_flags and its check_printf byte = 1 (so printf_common runs), and REAL(vsnprintf) = musl vsnprintf.
   All four hold in fuzz_reply.asan-ubsan's collected start-up state (lib/B/YF0m.v Tfib_const_abs: z1 0xa7318 0x1,
   z1 0x1381bc 0x1, the GOT word of common_flags) - the values every Bz interceptor walk was relocated with. *)
Definition sni_cells (m : mem) : Prop :=
  rw_cells asegs m PF_ASAN_INITED [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m PF_GOT_COMMON_FLAGS [C8 (Z_to_bv 64 PF_COMMON_FLAGS)]
  /\ ro_cells asegs m PF_CHECK_PRINTF [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m PF_REAL_VSNPRINTF [C8 (Z_to_bv 64 PF_MUSL_VSNPRINTF)].

(* What ___interceptor_vfprintf reads: the same three, and REAL(vfprintf) = musl vfprintf (YF0m: z8 0x9fce8 0x93288). *)
Definition vfi_cells (m : mem) : Prop :=
  rw_cells asegs m PF_ASAN_INITED [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m PF_GOT_COMMON_FLAGS [C8 (Z_to_bv 64 PF_COMMON_FLAGS)]
  /\ ro_cells asegs m PF_CHECK_PRINTF [C1 (Z_to_bv 8 1)]
  /\ ro_cells asegs m PF_REAL_VFPRINTF [C8 (Z_to_bv 64 PF_MUSL_VFPRINTF)].

Lemma sni_cells_walk : forall m, sni_cells m -> vsnpfcells m /\ vsncells m.
Proof. intros m (C1 & C2 & C3 & C4). split; [exact (conj C1 (conj C2 C3)) | exact C4]. Qed.

(* ---- printf_common ---- *)

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
