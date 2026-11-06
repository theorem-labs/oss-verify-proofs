(* GXA's interceptor call contracts for memcpy and memset (lib/CJ/RL/GXA/CopyCall.v:29-41 memcpy_stack_contract,
   SetCall.v:28-37 memset_stack_contract), discharged at the ASan instance A_img (RT_IImgA.v) on the pinned
   fuzz_reply.asan, and memset's also at musl vsnprintf's instance A_img_vsn (a corollary of the A_img proof).
   The twin of RT_gxa_calls.v (strnlen), in the same shape; the statements, ready predicates and intro lemmas are
   word for word fuzz_manifest's lib/A/FMgxa_mem.v (a Theorem Labs lane), so a unit can take either by relocation.

   This file proves no new function.  It composes walks that are already in the tree, relocated from
   origin/cold/c-asan-rt-stateio-n 840c4afa7e2 (proofs/omx-clap-core/fuzz_state/lib) by code pairing
   (RT_gxa_mem_Tbl.v holds the table, the counts and the stack measurement):
   - memcpy: the Bz walk of ___interceptor_memcpy 0x53464 (lib/A/Bz/A/I_memcpy.v imemcpy_spec, over I_memcpyw.v /
     I_memcpyw2.v), with its two Section hypotheses rip_stmt (R_isPoisoned.v rip_proof) and memcpy_stmt (musl
     memcpy 0x964cc: RT_mem_bz.v mc_proof, from the c-libc walks lib/A/Prog/memcpy.v and memcpy_same.v).
     I_amemcpy.v (the walk of __asan_memcpy, the body BELOW the interceptor) is in the tree only because it states
     memcpy_stmt; it is not used for this contract.
   - memset: the Bz walk of ___interceptor_memset 0x53174 (lib/A/Bz/A/I_imemset.v imemset_spec, over I_memsetw.v),
     with rip_stmt and memset_callZ_stmt (musl memset 0x96900: RT_mem_bz.v ms_callZ_proof, from lib/A/Prog/memset.v).
   - the CJ / Bz vocabulary bridge and the strnlen kit of RT_gxa_calls.v (bz_cj_evt, mem_inv_cj_bz, mem_inv_bz_cj,
     chk_ok_of_pf_rng).
   What it adds is glue only: the two trampolines (one `j` each, under A_img GXA's call targets `sym 0x21334` and
   `sym 0x21738`, RT_IImgA.v:57-58), the CB-cell conversion between the two trees (an Inductive in each), and the
   two ready predicates.
   The ready predicates are exactly what the interceptor walks ask beyond the contracts' own premises, with the
   walk's stack floor lo := sp - DEPTH (GXA's depths equal the walks', RT_gxa_mem_Tbl.v):
   - copy_ready m sp d s n: the stack window lies above ASan's high shadow and below 2^63; both ranges end at or
     below 2^47; the destination is off the walk's stack window (the source is already, by the contract); both
     ranges pass the interceptor's range check (chk_ok); ASan's mem-to-shadow cells (m2s_cells) and the cells the
     memcpy interceptor reads (icells: the GOT words of the shadow cell and of the replace_intrin flag, the flag
     byte = 1, the shadow offset 0x7fff8000, and REAL(memcpy) = musl memcpy).
   - set_ready m sp d n: the same for the one destination range, with icells_ms (REAL(memset) = musl memset).
   copy_ready_intro / set_ready_intro prove them from GXA's own ASan vocabulary (AsanFacts.v pf_rng / shadow_rw),
   the stack placement and ASan's runtime cells, as RT_gxa_calls.v's strn_ready_intro does.
   Image numerals: none here; the entries are RT_gxa_mem_Tbl.v's MC_TRAMP / MC_ICPT / MS_TRAMP / MS_ICPT. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_memcpyw I_memcpyw2 I_amemcpy I_memcpy I_memsetw F_memset I_imemset.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_mem_Tbl.
Require OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_mem_bz.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Frame.
Module BzCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.Lib.Step.
Module BzRIP := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.Bz.A.R_isPoisoned.
Module CJS := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.MState.
Module CJM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Frame.
Module CJCl := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Cells.
Module CJSt := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.Lib.Step.
Module CJR := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.Reloc.RStep.
Module GXC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.SetCall.
Module GXF := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_IImgA.
Module RGC := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_calls.
Module TBL := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_gxa_mem_Tbl.
Module RMB := OSSVerify.Proofs.plugin_hostd.fuzz_reply.lib.A.RT_mem_bz.

(* ---- the trampolines: one `j` each, in the Bz tree's words ---- *)

(* __interceptor_trampoline_memcpy 0x52724: `j 53464 <___interceptor_memcpy>` (5410006f) *)
Lemma memcpy_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MC_ICPT) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MC_TRAMP) fc None m (seg_rom asegs)).
Proof. unfold TBL.MC_ICPT, TBL.MC_TRAMP. intros until m. intros H. lstep. exact H. Qed.

(* __interceptor_trampoline_memset 0x52720: `j 53174 <___interceptor_memset>` (2550006f) *)
Lemma memset_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MS_ICPT) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MS_TRAMP) fc None m (seg_rom asegs)).
Proof. unfold TBL.MS_ICPT, TBL.MS_TRAMP. intros until m. intros H. lstep. exact H. Qed.

(* GXA's call targets under A_img: the trampolines (RT_IImgA.v:57-58) *)
Lemma A_sym_memcpy : @CJR.sym RTA.A_img 0x21334 = TBL.MC_TRAMP.
Proof. vm_compute. reflexivity. Qed.

Lemma A_sym_memset : @CJR.sym RTA.A_img 0x21738 = TBL.MS_TRAMP.
Proof. vm_compute. reflexivity. Qed.

(* musl vsnprintf's instance has the same memset row (RT_IImgA.v:105-109: A_img_vsn differs only at 0x7f000400) *)
Lemma A_sym_vsn_memset : @CJR.sym RTA.A_img_vsn 0x21738 = TBL.MS_TRAMP.
Proof. vm_compute. reflexivity. Qed.

(* ---- the CB cell, an Inductive in each tree ---- *)

Lemma rw_cb_cj_bz : forall m a k bs,
  @CJSt.rw_cells (@CJR.img_segs RTA.A_img) m a [CJCl.CB k bs] -> BzSt.rw_cells asegs m a [BzCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Lemma rw_cb_bz_cj : forall m a k bs,
  BzSt.rw_cells asegs m a [BzCl.CB k bs] -> @CJSt.rw_cells (@CJR.img_segs RTA.A_img) m a [CJCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

(* ---- memcpy ---- *)

Definition copy_ready (m : word -> option byte) (sp d s n : Z) : Prop :=
  kHighShadowEnd < sp - GXC.COPY_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47 /\ s + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d)
  /\ chk_ok m s n /\ chk_ok m d n
  /\ m2s_cells m /\ icells m.

Theorem memcpy_stack_contract_A : @GXC.memcpy_stack_contract RTA.A_img copy_ready.
Proof.
  unfold GXC.memcpy_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m src junk
    SRC LEN DST OV SEPS MI ST (LOLO & SPH & DH & SH & SEPD & CS & CD & M2S & IC).
  unfold GXC.COPY_DEPTH in *.
  rewrite A_sym_memcpy.
  apply RGC.bz_cj_evt.
  pose proof (bv_unsigned_in_range 64 a0) as D0. pose proof (bv_unsigned_in_range 64 a1) as S0.
  pose proof (bv_unsigned_in_range 64 a2) as N0. change (bv_modulus 64) with (2 ^ 64) in D0, S0, N0.
  assert (LENZ : Z.of_nat (length src) = bv_unsigned a2) by (rewrite LEN; apply Z2Nat.id; lia).
  apply (BzE.evt_mono asegs (imemcpy_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            (bv_unsigned a0) (bv_unsigned a1) src (bv_unsigned sp - 2240) m)).
  - rewrite RGC.ms_cj_bz, RGC.mkR_cj_bz, RGC.seg_rom_cj_bz.
    apply memcpy_tramp_step.
    assert (EA0 : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA2 : a2 = Z_to_bv 64 (Z.of_nat (length src))) by (rewrite LENZ; symmetry; apply Z_to_bv_bv_unsigned).
    assert (STb : stk asegs m (bv_unsigned sp - 2240) (bv_unsigned sp)) by exact ST.
    assert (SRCb : bytes_at asegs m (bv_unsigned a1) src) by exact SRC.
    assert (DSTb : BzSt.rw_cells asegs m (bv_unsigned a0) [BzCl.CB (length src) junk])
      by (rewrite LEN; exact (rw_cb_cj_bz m _ _ _ DST)).
    rewrite <- LENZ in DH, SH, SEPD, CS, CD, OV, SEPS.
    unfold TBL.MC_ICPT.
    exact (imemcpy_spec BzRIP.rip_proof RMB.mc_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0) (bv_unsigned a1) src junk (bv_unsigned sp - 2240)
             EA0 EA1 EA2 STb ltac:(lia) LOLO SPH ltac:(lia) ltac:(lia) DH SH ltac:(lia) ltac:(lia) SEPD
             SRCb DSTb CS CD M2S IC (RGC.mem_inv_cj_bz m MI)).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & MI' & ST' & RW & SRC').
    rewrite Z_to_bv_bv_unsigned in E. rewrite LENZ in MU.
    unfold GXC.memcpy_stack_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|].
    split; [exact (RGC.mem_inv_bz_cj m' MI')|]. split; [exact ST'|].
    split; [rewrite <- LEN; exact (rw_cb_bz_cj m' _ _ _ RW) | exact SRC'].
Qed.

(* copy_ready from what GXA's caller holds at a memcpy call (sn_write_ready, CopyCall.v:46-51: the stack placement,
   the destination inside the caller's buffer and the source inside a range GXA calls addressable), a readable
   shadow and ASan's runtime cells. *)
Lemma copy_ready_intro : forall (m : word -> option byte) sp d s n Ld Ls,
  kHighShadowEnd < sp - GXC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.A_img m d Ld -> @GXF.pf_rng RTA.A_img m s Ls -> @GXF.shadow_rw RTA.A_img m ->
  n <= Ld -> n <= Ls ->
  m2s_cells m -> icells m ->
  copy_ready m sp d s n.
Proof.
  intros m sp d s n Ld Ls H1 H2 N0 SEPD PD PS SRW HD HS C1 C2.
  split; [exact H1|]. split; [exact H2|].
  split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [destruct PS as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [exact SEPD|].
  split; [exact (RGC.chk_ok_of_pf_rng m s Ls n PS SRW HS)|].
  split; [exact (RGC.chk_ok_of_pf_rng m d Ld n PD SRW HD)|].
  exact (conj C1 C2).
Qed.

(* ---- memset ---- *)

(* Asked only when 0 <= n, as a Theorem Labs lane's FMgxa_mem.v:222-223 since 3899f140f93: GXA's pc_guard
   (G_printf_core_common.v:156) asks set_ready at every D + N + 8 <= q with N unbounded below, where sp < 2 ^ 63
   cannot follow, so without the premise the clause cannot hold (a Theorem Labs lane proved pc_guard_set_false against the
   old form; FMgxaSeamReady.v header).  The contract applies set_ready only at bv_unsigned a2 (SetCall.v:35). *)
Definition set_ready (m : word -> option byte) (sp d n : Z) : Prop :=
  0 <= n ->
  kHighShadowEnd < sp - GXM.SET_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d)
  /\ chk_ok m d n
  /\ m2s_cells m /\ icells_ms m.

Theorem memset_stack_contract_A : @GXM.memset_stack_contract RTA.A_img set_ready.
Proof.
  unfold GXM.memset_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    DST MI ST G.
  pose proof (bv_unsigned_in_range 64 a2) as N0. change (bv_modulus 64) with (2 ^ 64) in N0.
  destruct (G (proj1 N0)) as (LOLO & SPH & DH & SEPD & CD & M2S & IC). clear N0.
  unfold GXM.SET_DEPTH in *.
  rewrite A_sym_memset.
  apply RGC.bz_cj_evt.
  pose proof (bv_unsigned_in_range 64 a0) as D0. pose proof (bv_unsigned_in_range 64 a1) as C0.
  pose proof (bv_unsigned_in_range 64 a2) as N0. change (bv_modulus 64) with (2 ^ 64) in D0, C0, N0.
  apply (BzE.evt_mono asegs (imemset_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
            (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) (bv_unsigned sp - 2224) m)).
  - rewrite RGC.ms_cj_bz, RGC.mkR_cj_bz, RGC.seg_rom_cj_bz.
    apply memset_tramp_step.
    assert (EA0 : a0 = Z_to_bv 64 (bv_unsigned a0)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA1 : a1 = Z_to_bv 64 (bv_unsigned a1)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (EA2 : a2 = Z_to_bv 64 (bv_unsigned a2)) by (symmetry; apply Z_to_bv_bv_unsigned).
    assert (STb : stk asegs m (bv_unsigned sp - 2224) (bv_unsigned sp)) by exact ST.
    pose proof (rw_cb_cj_bz m _ _ _ DST) as DSTb.
    unfold TBL.MS_ICPT.
    exact (imemset_spec BzRIP.rip_proof RMB.ms_callZ_proof
             ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m
             (bv_unsigned a0) (bv_unsigned a1) (bv_unsigned a2) junk (bv_unsigned sp - 2224)
             EA0 EA1 EA2 STb ltac:(lia) LOLO SPH ltac:(lia) ltac:(lia) DH ltac:(lia) SEPD
             DSTb CD M2S IC (RGC.mem_inv_cj_bz m MI)).
  - intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                E & MU & WM & MI' & ST' & RW).
    rewrite Z_to_bv_bv_unsigned in E.
    unfold GXM.memset_stack_post.
    exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', m'.
    split; [exact E|]. split; [exact MU|]. split; [exact WM|].
    split; [exact (RGC.mem_inv_bz_cj m' MI')|]. split; [exact ST'|].
    exact (rw_cb_bz_cj m' _ _ _ RW).
Qed.

(* musl vsnprintf's instance (RT_IImgA.v:107), whose memset call G_vsnprintf.v:143 takes as SPEC_memset.  The memset
   contract reads the image record only through its segments and its memset row (SetCall.v:14-37), and set_ready
   reads it not at all, so it moves between any two images that agree on those two: no walk is re-run.
   The transfer is stated over abstract images on purpose: A_img and A_img_vsn are never compared as terms (they
   differ at 0x7f000400), only their segments and memset rows are, each by evaluation. *)
Lemma memset_contract_transfer : forall (I1 I2 : CJR.RImg) (R : (word -> option byte) -> Z -> Z -> Z -> Prop),
  @CJR.img_segs I1 = @CJR.img_segs I2 -> @CJR.sym I1 0x21738 = @CJR.sym I2 0x21738 ->
  @GXM.memset_stack_contract I1 R -> @GXM.memset_stack_contract I2 R.
Proof.
  intros [segs1 sym1] [segs2 sym2] R ES EY H. cbn [CJR.img_segs CJR.sym] in ES, EY. subst segs2.
  unfold GXM.memset_stack_contract, GXM.memset_stack_post in *. cbn [CJR.img_segs CJR.sym] in *.
  rewrite <- EY. exact H.
Qed.

Lemma A_vsn_img_segs : @CJR.img_segs RTA.A_img_vsn = @CJR.img_segs RTA.A_img.
Proof. unfold RTA.A_img_vsn, RTA.A_img. cbn [CJR.img_segs]. reflexivity. Qed.

Theorem memset_stack_contract_Avsn : @GXM.memset_stack_contract RTA.A_img_vsn set_ready.
Proof.
  apply (memset_contract_transfer RTA.A_img RTA.A_img_vsn set_ready).
  - symmetry. exact A_vsn_img_segs.
  - rewrite A_sym_memset, A_sym_vsn_memset. reflexivity.
  - exact memset_stack_contract_A.
Qed.

(* set_ready from what GXA's caller holds at a memset call: the stack placement, the destination inside a range GXA
   calls addressable, a readable shadow and ASan's runtime cells. *)
Lemma set_ready_intro : forall (m : word -> option byte) sp d n Ld,
  kHighShadowEnd < sp - GXM.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.A_img m d Ld -> @GXF.shadow_rw RTA.A_img m -> n <= Ld ->
  m2s_cells m -> icells_ms m ->
  set_ready m sp d n.
Proof.
  intros m sp d n Ld H1 H2 N0 SEPD PD SRW HD C1 C2 _.
  split; [exact H1|]. split; [exact H2|].
  split; [destruct PD as (_ & (_ & _ & Hpn & _) & _); unfold GXF.APPMEM_END in Hpn; lia|].
  split; [exact SEPD|].
  split; [exact (RGC.chk_ok_of_pf_rng m d Ld n PD SRW HD)|].
  exact (conj C1 C2).
Qed.
