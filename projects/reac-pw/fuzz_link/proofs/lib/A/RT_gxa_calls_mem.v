(* Copied from a working branch 86b50358d34 proofs/plugin-hostd/fuzz_reply/lib/A/RT_gxa_calls_mem.v; changed: module path fuzz_reply -> fuzz_disco, instance RT_IImgA.A_img -> RecAsanA.N_img_asan, the bridge module RT_gxa_calls -> RT_gxa_bridge, comments dropped; set_ready asked only when 0 <= n, as fm a working branch 3899f140f93 (memset_stack_contract and set_ready_intro re-proved for it). *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib Require Import Tac ImageA SysStep.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Spec Require Import StrFun.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib Require Import StoreFast.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.P Require Import Str_tac Startup_glue.
From OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A Require Import Shadow R_small R_m2s R_thread I_consts I_qck X_atexit D_kit I_memcpyw I_memcpyw2 I_amemcpy I_memcpy I_memsetw F_memset I_imemset.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_isPoisoned.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Cells.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RStep.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I.RecAsanA.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_mem_Tbl.
Require OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_mem_bz.
Import ListNotations.
Open Scope Z_scope.

Module BzE := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Exec.
Module BzM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Mem.
Module BzF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Frame.
Module BzCl := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Cells.
Module BzSt := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.Lib.Step.
Module BzRIP := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.Bz.A.R_isPoisoned.
Module CJS := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.MState.
Module CJM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Mem.
Module CJF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Frame.
Module CJCl := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Cells.
Module CJSt := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.Lib.Step.
Module CJR := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.Reloc.RStep.
Module GXC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.CopyCall.
Module GXM := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.SetCall.
Module GXF := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.GXA.AsanFacts.
Module RTA := OSSVerify.Proofs.reac_pw.fuzz_link.lib.CJ.RL.I.RecAsanA.
Module RGC := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_bridge.
Module TBL := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_gxa_mem_Tbl.
Module RMB := OSSVerify.Proofs.reac_pw.fuzz_link.lib.A.RT_mem_bz.

Lemma memcpy_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MC_ICPT) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MC_TRAMP) fc None m (seg_rom asegs)).
Proof. unfold TBL.MC_ICPT, TBL.MC_TRAMP. intros until m. intros H. lstep. exact H. Qed.

Lemma memset_tramp_step : forall (Q : machine_state -> Prop)
    ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem),
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MS_ICPT) fc None m (seg_rom asegs)) ->
  evt asegs Q (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
      F (Z_to_bv 64 TBL.MS_TRAMP) fc None m (seg_rom asegs)).
Proof. unfold TBL.MS_ICPT, TBL.MS_TRAMP. intros until m. intros H. lstep. exact H. Qed.

Lemma A_sym_memcpy : @CJR.sym RTA.N_img_asan 0x21334 = TBL.MC_TRAMP.
Proof. vm_compute. reflexivity. Qed.

Lemma A_sym_memset : @CJR.sym RTA.N_img_asan 0x21738 = TBL.MS_TRAMP.
Proof. vm_compute. reflexivity. Qed.

Lemma rw_cb_cj_bz : forall m a k bs,
  @CJSt.rw_cells (@CJR.img_segs RTA.N_img_asan) m a [CJCl.CB k bs] -> BzSt.rw_cells asegs m a [BzCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Lemma rw_cb_bz_cj : forall m a k bs,
  BzSt.rw_cells asegs m a [BzCl.CB k bs] -> @CJSt.rw_cells (@CJR.img_segs RTA.N_img_asan) m a [CJCl.CB k bs].
Proof. intros m a k bs [[Hwf Hb] Hw]. split; [split|]; [exact Hwf | exact Hb | exact Hw]. Qed.

Definition copy_ready (m : word -> option byte) (sp d s n : Z) : Prop :=
  kHighShadowEnd < sp - GXC.COPY_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47 /\ s + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d)
  /\ chk_ok m s n /\ chk_ok m d n
  /\ m2s_cells m /\ icells m.

Theorem memcpy_stack_contract_A : @GXC.memcpy_stack_contract RTA.N_img_asan copy_ready.
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

Lemma copy_ready_intro : forall (m : word -> option byte) sp d s n Ld Ls,
  kHighShadowEnd < sp - GXC.COPY_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXC.COPY_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.N_img_asan m d Ld -> @GXF.pf_rng RTA.N_img_asan m s Ls -> @GXF.shadow_rw RTA.N_img_asan m ->
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

Definition set_ready (m : word -> option byte) (sp d n : Z) : Prop :=
  0 <= n ->
  kHighShadowEnd < sp - GXM.SET_DEPTH /\ sp < 2 ^ 63
  /\ d + n <= 2 ^ 47
  /\ (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d)
  /\ chk_ok m d n
  /\ m2s_cells m /\ icells_ms m.

Theorem memset_stack_contract_A : @GXM.memset_stack_contract RTA.N_img_asan set_ready.
Proof.
  unfold GXM.memset_stack_contract.
  intros ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m junk
    DST MI ST G.
  unfold GXM.SET_DEPTH in *.
  rewrite A_sym_memset.
  apply RGC.bz_cj_evt.
  pose proof (bv_unsigned_in_range 64 a0) as D0. pose proof (bv_unsigned_in_range 64 a1) as C0.
  pose proof (bv_unsigned_in_range 64 a2) as N0. change (bv_modulus 64) with (2 ^ 64) in D0, C0, N0.
  destruct (G (proj1 N0)) as (LOLO & SPH & DH & SEPD & CD & M2S & IC).
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

Lemma set_ready_intro : forall (m : word -> option byte) sp d n Ld,
  kHighShadowEnd < sp - GXM.SET_DEPTH -> sp < 2 ^ 63 -> 0 <= n ->
  (n = 0 \/ d + n <= sp - GXM.SET_DEPTH \/ sp <= d) ->
  @GXF.pf_rng RTA.N_img_asan m d Ld -> @GXF.shadow_rw RTA.N_img_asan m -> n <= Ld ->
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
