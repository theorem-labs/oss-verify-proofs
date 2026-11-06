(* lib/A/Prog/Seg/R19F_on.v -- route (C) (a Theorem Labs lane 09:20Z; wave lead a Theorem Labs lane): the `_on` twins of lib/A/Prog/Seg/R19F.v's (not in this delivery) two
   footprint runs, r19_run_F_on and r19_evt_F_on (WORKLIST.md row L2 (a working note, not in this delivery) run (Seg) lib/A/Prog/Seg/R19F.v (not in this delivery)).
   Written by a Theorem Labs lane with the R19F.v (not in this delivery) owner's consent (a Theorem Labs lane, 12:52Z, relayed by a Theorem Labs lane):
   a NEW file; Seg/R19F.v (an earlier version, blob 14257b56dec, not in this delivery) stays byte-identical (the same on a working branch 1502cba0417 and on a Theorem Labs lane's fold
   a working branch 4bae33fdf54).  rule 24: no function proved (kind: segment run lemma, a mechanical
   re-run of R19F.v's (not in this delivery) two scripts under the callee's narrowed contract).

   WHAT CHANGES against R19F.v's (not in this delivery) r19_run_F / r19_evt_F (and nothing else; the pattern is a Theorem Labs lane's r19_run_on /
   r19_evt_on, Seg/R19.v (a version not in this delivery; written on a working branch 1b5bd4f4555)):
   - the callee premise bcmp_wrap_contract_F -> bcmp_wrap_contract_F_on (lib/A/Prog/bcmp_wrap_c_on.v, a Theorem Labs lane's
     leaf, blob ca2f37ea2b6; its proof bcmp_wrap_holds_F_on is in lib/A/Prog/bcmp_wrap_on.v, blob defebf6ef6f, both
     at a working branch b1fad972898);
   - the premise `shadow_rw m` -> `shadow_rw_on (bcmp_wrap_shadow_R (phi + 18) s2a 32) m`: the shadow bytes the run
     reads are only the wrapper's, at the call 0x818e4 where a0 = s11 = phi + 18, a1 = s2 = s2a and a2 = 32 (the five
     instructions before the call touch no memory).  This is the R of a Theorem Labs lane's WORKLIST.md:1383-1384 (a working note, not in this delivery) rows;
   - in r19_run_F_on the callee's post is bcmp_wrap_post_on (same conjunct count; its shadow conjunct is unused here);
   - in r19_evt_F_on the shadow premise crosses MemNorm's mem_rel by ShadowRwOnT.shadow_rw_on_rel (the one-direction shadow_rw_on form of
     B3Norm's b3n_rel_sw, as a Theorem Labs lane's r19_evt_on (not in this delivery) does).
   The seven rng premises and the conclusions are R19F.v's, character for character.

   CLOSURE: R19F.v's Requires, plus bcmp_wrap_c_on (leaf: Definitions only), A.ShadowRwOn and A.ShadowRwOnT.  Seg/R19F.v
   itself is not Required (both lemmas are re-run, not derived from it). *)
From Stdlib Require Import ZArith List Bool Lia Permutation.
From LinuxProcessSemantics.LinuxProcessSem Require Import
BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable Require Import YK11 YM05 YK0o YK0s YK15 YP09 YO0f YO0d YO09
  YL00 YL0g YL0i YI14 YI16 YL01 YM06.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame Step Cells Tac.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Regs6ss RegisterBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require AsanRTInv.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Spec Require Import StrFun.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import memcmp_c bcmp_wrap_c.
(* The callee's narrowed contract (leaf) and the shadow-region forms. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import bcmp_wrap_c_on.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require ShadowRwOn ShadowRwOnT.
(* R19.v's second require block (the one its r19_evt is stated and proved under). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot B3FrCl B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import R19.
(* rng_bytes (the callee contract's forall-footprint premise) and the evtF form of MemNorm.evt_normalize. *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import RngBytes.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require MemNormF.
(* Last: StepF's step / if_true_by (evtF goals) shadow Step's and Tac's (evt goals). *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import ExecF StepF.
Import ListNotations.
(* Qualified, as R19.v does after BzBridge: a bare `Import YK11` would be the image-independent lib/Reusable one,
   whose getr / mkst / FPState are not the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module MNF := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.MemNormF.
Module SRO := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOn.
Module SROT := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.ShadowRwOnT.

(* ---- r19_run_F_on: R19F.r19_run_F under bcmp_wrap_contract_F_on, with the wrapper's shadow region in place of
   shadow_rw (same script). *)
Lemma r19_run_F_on : bcmp_wrap_contract_F_on ->
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi s2a vd v lo : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s11 = Z_to_bv 64 (phi + 18) -> s2 = Z_to_bv 64 s2a -> a0 = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= s2a -> s2a + 32 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m s2a rs -> memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m (phi + 18) 32 -> addressable m s2a 32 ->
    end_in_app (phi + 18) 32 -> end_in_app s2a 32 -> app_mem (phi + 18 + 7) -> app_mem (s2a + 7) ->
    (phi + 18 + 32 <= spv - BCMP_WRAP_K \/ spv <= phi + 18) -> (s2a + 32 <= spv - BCMP_WRAP_K \/ spv <= s2a) ->
    stk rsegs m lo spv -> lo + BCMP_WRAP_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (bcmp_wrap_shadow_R (phi + 18) s2a 32) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (spv - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (phi + 18) 32 ->
    rng RNG (8 * (shadow_addr (phi + 18) / 8))
            (8 * (shadow_addr (phi + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (phi + 18) / 8)) ->
    rng RNG s2a 32 ->
    rng RNG (8 * (shadow_addr s2a / 8))
            (8 * (shadow_addr (s2a + 32 - 1) / 8) + 8 - 8 * (shadow_addr s2a / 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x818e8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x818e8) fc None m' (seg_rom rsegs) /\
         munch [(spv - BCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818d0) fc None m (seg_rom rsegs)).
Proof.
  intros BCF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi s2a vd v lo ls rs -> -> -> -> Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
    HL HR HM MI AL AR EL ER PL PR RL RR ST HK Hlo Hsp AC SW RB RM GC C254 C255
    RBY Rimg Rstk RngL RngLs RngR RngRs.
  step. if_true_by (r19_neqb0 vd ltac:(lia)).
  step. step. step. step.
  eapply evtF_cut.
  { eapply BCF with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: cbv zeta.
    all: rewrite ?unsigned_lit by lia.
    all: try (change (Z.to_nat 32) with 32%nat).
    all: first [ exact HL | exact HR | exact HM | exact MI | exact AL | exact AR | exact EL | exact ER
               | exact RL | exact RR | exact ST | exact HK | exact Hlo | exact Hsp
               | exact AC | exact SW | exact RB | exact RM | exact GC | exact C254 | exact C255
               | exact RBY | exact Rimg | exact Rstk | exact RngL | exact RngR
               | (right; exact RngLs) | (right; exact RngRs)
               | (right; exact PL) | (right; exact PR) | lia ]. }
  intros ms' PO. unfold bcmp_wrap_post_on in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & HBL & HBR).
  subst ms'.
  lazymatch goal with
  | |- evtF _ _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evtF_done. do 15 eexists. split; [reflexivity|].
  rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in ST' by lia.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI' | exact ST'].
Qed.

(* ---- r19_evt_F_on: R19F.r19_evt_F under bcmp_wrap_contract_F_on, with the wrapper's shadow region in place of
   shadow_rw (same script; the region premise crosses mem_rel by ShadowRwOnT.shadow_rw_on_rel). *)
Lemma r19_evt_F_on : bcmp_wrap_contract_F_on ->
  forall (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi s2a vd v lo : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s11 = Z_to_bv 64 (phi + 18) -> s2 = Z_to_bv 64 s2a -> a0 = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= s2a -> s2a + 32 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m s2a rs -> memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m (phi + 18) 32 -> addressable m s2a 32 ->
    end_in_app (phi + 18) 32 -> end_in_app s2a 32 -> app_mem (phi + 18 + 7) -> app_mem (s2a + 7) ->
    (phi + 18 + 32 <= spv - BCMP_WRAP_K \/ spv <= phi + 18) -> (s2a + 32 <= spv - BCMP_WRAP_K \/ spv <= s2a) ->
    stk rsegs m lo spv -> lo + BCMP_WRAP_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> SRO.shadow_rw_on (bcmp_wrap_shadow_R (phi + 18) s2a 32) m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    rng_bytes RNG ->
    rng RNG 0x10000 0x5ee000 ->
    rng RNG (spv - BCMP_WRAP_K) BCMP_WRAP_K ->
    rng RNG (phi + 18) 32 ->
    rng RNG (8 * (shadow_addr (phi + 18) / 8))
            (8 * (shadow_addr (phi + 18 + 32 - 1) / 8) + 8 - 8 * (shadow_addr (phi + 18) / 8)) ->
    rng RNG s2a 32 ->
    rng RNG (8 * (shadow_addr s2a / 8))
            (8 * (shadow_addr (s2a + 32 - 1) / 8) + 8 - 8 * (shadow_addr s2a / 8)) ->
    evtF rsegs RNG
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x818e8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x818e8) fc None m' (seg_rom rsegs) /\
         munch [(spv - BCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818d0) fc None m (seg_rom rsegs)).
Proof.
  intros BCF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi s2a vd v lo ls rs Esp Es11 Es2 Ea0 Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
    HL HRr HM HRO AL AR EL ER PL PR RL RR ST HK Hlo Hsp AC SW RB RM GC C254 C255
    RBY Rimg Rstk RngL RngLs RngR RngRs.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  eapply evtF_mono.
  { eapply (MNF.evtF_normalize_ro RNG _ _ _ _ _ _ _ _ HRO).
    exact (r19_run_F_on BCF RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
             t3 t4 t5 t6
             F fc (normalize rsegs m) spv phi s2a vd v lo ls rs Esp Es11 Es2 Ea0 Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) HL) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRr) HM
             (mem_inv_normalize rsegs m)
             (proj1 (b3n_rel_ad m _ _ _ REL) AL) (proj1 (b3n_rel_ad m _ _ _ REL) AR) EL ER PL PR RL RR
             (proj1 (b3n_rel_stk m _ lo spv REL ltac:(lia) ltac:(lia)) ST) HK Hlo Hsp
             (proj1 (b3n_rel_cells m _ REL) AC)
             (SROT.shadow_rw_on_rel (bcmp_wrap_shadow_R (phi + 18) s2a 32) m _ REL SW)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) RB) (proj1 (bytes_at_rel rsegs m _ _ _ REL) RM)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) GC)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) C254) (proj1 (bytes_at_rel rsegs m _ _ _ REL) C255)
             RBY Rimg Rstk RngL RngLs RngR RngRs). }
  intros ms' (s0' & PO & HREL & HROS).
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m0' &
                  E & MU0 & WM0 & _ & ST0).
  subst s0'.
  destruct HREL as (ERg & EF & EP & ES & EV & EC & ERo & HMR).
  cbn [ms_regs ms_fregs ms_pc_val ms_svc_pending ms_resv ms_fcsr ms_rom ms_mem MS] in ERg, EF, EP, ES, EV, EC, ERo,
    HMR.
  pose proof (b3n_ms_eta ms' ES) as Ems.
  rewrite ERg, EF, EP, EC, EV, ERo in Ems.
  remember (ms_mem ms') as mf eqn:Emf. clear Emf.
  assert (MUf : munch [(spv - BCMP_WRAP_K, spv)] m mf) by exact (b3n_rel_munch _ m _ mf m0' REL HMR MU0 HROS).
  exists t0', t1', t2', a1', a2', a3', a4', a5', a6', a7', t3', t4', t5', t6', mf.
  split; [exact Ems|].
  split; [exact MUf|].
  split.
  { apply (b3n_rel_wmono [(spv - BCMP_WRAP_K, spv)] m _ mf m0' REL HMR MUf WM0).
    intros x E0. apply (b3n_W_ro _ x); [|exact E0].
    intros p [<-|[]]. cbn [fst]. lia. }
  split; [exact (ro_agree_same rsegs m mf HRO HROS)|].
  exact (proj2 (b3n_rel_stk mf m0' lo spv HMR ltac:(lia) ltac:(lia)) ST0).
Qed.
