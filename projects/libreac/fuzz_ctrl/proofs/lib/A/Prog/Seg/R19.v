(* Segment R19 of fuzz_ctrl LLVMFuzzerTestOneInput (asan, image A): [0x818d0, 0x818e4], Inv_A818d0 -> Inv_A818e8.
   b-th round trip: the declaration_of result a0 is nonzero (the branch 0x818d0 -> 0x818d4 is not taken), then
   a2 := 32, a0 := s11 = Phi_r + 18, a1 := s2 = decl_slot fr and the call of wrapper_bcmp at 0x818e4 (BCMP_WRAP).
   The wrapper checks that the 32 bytes at a0 and the 32 bytes at a1 are addressable, compares them and writes only
   its stack scratch [sp - BCMP_WRAP_K, sp).  r19_run is the Lib-level run of [0x818d0, 0x818e8) with the wrapper's
   contract; r19_evt is the same run from ro_agree (push 5b: FRA carries no mem_inv, so the run goes on the
   normalized memory, MemNorm.evt_normalize, with the B3Norm transports); seg_R19s is the full segment lemma
   (sl_run_lib + b3_fr_cl + sl_fra_move, the R8 recipe) from the official entry cut Inv_A818d0_at to the official
   exit cut Inv_A818e8_at (SlotInv.v push 6c); seg_R19 is the same statement. *)
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
Import ListNotations.
Import YK11.
Open Scope Z_scope.

Lemma r19_neqb0 : forall x, 0 < x < 2 ^ 64 -> negb (bv_eqb (Z_to_bv 64 x) (Z_to_bv 64 0)) = true.
Proof.
  intros x Hx. unfold bv_eqb. rewrite !unsigned_lit by lia.
  rewrite (proj2 (Z.eqb_neq x 0)) by lia. reflexivity.
Qed.

(* The run on a memory with mem_inv (the wrapper contract's premise); r19_evt below reaches it from ro_agree. *)
Lemma r19_run : bcmp_wrap_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi s2a vd v lo : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s11 = Z_to_bv 64 (phi + 18) -> s2 = Z_to_bv 64 s2a -> a0 = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= s2a -> s2a + 32 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m s2a rs -> memcmp_model ls rs 32 = Some v ->
    mem_inv rsegs m -> addressable m (phi + 18) 32 -> addressable m s2a 32 ->
    end_in_app (phi + 18) 32 -> end_in_app s2a 32 -> app_mem (phi + 18 + 7) -> app_mem (s2a + 7) ->
    (phi + 18 + 32 <= spv - BCMP_WRAP_K \/ spv <= phi + 18) -> (s2a + 32 <= spv - BCMP_WRAP_K \/ spv <= s2a) ->
    stk rsegs m lo spv -> lo + BCMP_WRAP_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x818e8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x818e8) fc None m' (seg_rom rsegs) /\
         munch [(spv - BCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\
         mem_inv rsegs m' /\ stk rsegs m' lo spv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818d0) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi s2a vd v lo ls rs -> -> -> -> Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
    HL HR HM MI AL AR EL ER PL PR RL RR ST HK Hlo Hsp AC SW RB RM GC C254 C255.
  step. if_true_by (r19_neqb0 vd ltac:(lia)).
  step. step. step. step.
  eapply evt_cut.
  { eapply BC with (ls := ls) (rs := rs) (v := v) (lo := lo).
    all: cbv zeta.
    all: rewrite ?unsigned_lit by lia.
    all: try (change (Z.to_nat 32) with 32%nat).
    all: first [ exact HL | exact HR | exact HM | exact MI | exact AL | exact AR | exact EL | exact ER
               | exact RL | exact RR | exact ST | exact HK | exact Hlo | exact Hsp
               | exact AC | exact SW | exact RB | exact RM | exact GC | exact C254 | exact C255
               | (right; exact PL) | (right; exact PR) | lia ]. }
  intros ms' PO. unfold bcmp_wrap_post in PO.
  destruct PO as (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  E & MU & WM & MI' & ST' & AC' & SW' & HBL & HBR).
  subst ms'.
  lazymatch goal with
  | |- evt _ _ (MS _ _ (ret_pc (Z_to_bv 64 ?k)) _ _ _ _) =>
      replace (ret_pc (Z_to_bv 64 k)) with (Z_to_bv 64 k) by (symmetry; apply ret_pc_even; [ lia | reflexivity ])
  end.
  apply evt_done. do 15 eexists. split; [reflexivity|].
  rewrite ?unsigned_lit in MU by lia. rewrite ?unsigned_lit in ST' by lia.
  split; [exact MU|]. split; [exact WM|]. split; [exact MI' | exact ST'].
Qed.

(* One byte of a byte run. *)
Lemma r19_byte : forall m a bs k x, bytes_at rsegs m a bs -> nth_error bs k = Some x ->
  bytes_at rsegs m (a + Z.of_nat k) [x].
Proof.
  intros m a bs k x (Ha & Hl & H) E.
  assert (Hk : (k < length bs)%nat) by (apply nth_error_Some; congruence).
  split; [lia|]. split; [cbn [length]; lia|].
  intros i Hi. cbn [length] in Hi. assert (Hi0 : i = 0%nat) by lia. subst i.
  change (Z.of_nat 0) with 0. rewrite Z.add_0_r. rewrite (H k Hk). rewrite E. reflexivity.
Qed.

(* The five image cells the wrapper reads, from the runtime invariant's cell lists (RT_REALS holds (REAL_BCMP, BCMP)
   and (REAL_MEMCMP, MEMCMP); the flag bytes CF + 254 / CF + 255 are bytes 14 / 15 of the run at RT_CF + 240). *)
Lemma r19_cells : forall m, asan_cf_cells m -> asan_real_cells m ->
  bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) /\ bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) /\
  bytes_at rsegs m GOT_CF (le8 (wa CF)) /\
  bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] /\ bytes_at rsegs m (CF + 255) [Z_to_bv 8 1].
Proof.
  intros m HCF HR.
  destruct HCF as (HCF1 & _ & _ & _ & _ & _ & HCF7 & _).
  split; [exact (AsanRTInv.real_cell_of m REAL_BCMP BCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact (AsanRTInv.real_cell_of m REAL_MEMCMP MEMCMP HR ltac:(vm_compute; reflexivity))|].
  split; [exact HCF1|].
  split.
  - replace (CF + 254) with (RT_CF + 240 + Z.of_nat 14) by (unfold CF, RT_CF; lia).
    exact (r19_byte m (RT_CF + 240) _ 14%nat (Z_to_bv 8 1) HCF7 eq_refl).
  - replace (CF + 255) with (RT_CF + 240 + Z.of_nat 15) by (unfold CF, RT_CF; lia).
    exact (r19_byte m (RT_CF + 240) _ 15%nat (Z_to_bv 8 1) HCF7 eq_refl).
Qed.

(* A byte of [A0, A0 + 312) with Z_to_bv 64 A0 = Z_to_bv 64 A (s1 = A, the spill base) lies outside any range
   [lo, hi) with 0 <= lo and hi <= A, for every representative A0 of A. *)
Lemma r19_wrap_out : forall A A0 lo hi x, Z_to_bv 64 A = Z_to_bv 64 A0 -> 0 <= A -> A + 312 <= 2 ^ 64 ->
  0 <= lo -> hi <= A -> A0 <= x < A0 + 312 -> ~ (lo <= x < hi).
Proof.
  intros A A0 lo hi x E H0 H1 Hlo Hhi Hx.
  assert (Ew : A mod 2 ^ 64 = A0 mod 2 ^ 64) by (rewrite <- !unsigned_lit_wrap; rewrite E; reflexivity).
  rewrite (Z.mod_small A (2 ^ 64)) in Ew by lia.
  pose proof (Z.div_mod A0 (2 ^ 64) ltac:(lia)) as Hdm. rewrite <- Ew in Hdm.
  remember (A0 / 2 ^ 64) as q eqn:Eq. clear Eq.
  change (2 ^ 64) with 18446744073709551616 in *. lia.
Qed.

(* memcmp of a list with itself over n <= length bytes is 0. *)
Lemma r19_memcmp_refl : forall l n, (n <= length l)%nat -> memcmp_model l l n = Some 0.
Proof.
  induction l as [|a l IH]; intros [|n] Hn; cbn [memcmp_model length] in *; try reflexivity; try lia.
  rewrite Z.eqb_refl. apply IH. lia.
Qed.

(* ---- Full wrapper seg_R19 (B3 recipe, as R8). ---- *)
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Import AsanRTInv AsanRTFacts PContract MemNorm AsanLift BzBridge.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A Require Contract FrameAPI.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require RcDecl RcFrag.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import SlotModel SlotInv RcAsanFPLib.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog Require Import MemMono.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require Import Tac_rt_b2 Tac_rt2_b2 Tac_slot B3FrCl B3Norm.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Prog.Seg Require B3Rtm.
(* Qualified: the BzBridge import above loads the image-independent lib/Reusable/YK11, after which a bare
   `Import YK11` is that one, whose getr / mkst / FPState are not the ones the cuts are built over. *)
Import OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Reusable.YK11.
Open Scope Z_scope.

Module ACw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Contract.
Module AFw := OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.FrameAPI.

(* r19_run from ro_agree in place of mem_inv: the run goes on the normalized memory (MemNorm.evt_normalize), which
   has mem_inv (mem_inv_normalize); the premises cross mem_rel forward and the post crosses it back (B3Norm; the
   wrapper's write set [sp - BCMP_WRAP_K, sp) lies above the image). *)
Lemma r19_evt : bcmp_wrap_contract ->
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (spv phi s2a vd v lo : Z) (ls rs : list byte),
    sp = Z_to_bv 64 spv -> s11 = Z_to_bv 64 (phi + 18) -> s2 = Z_to_bv 64 s2a -> a0 = Z_to_bv 64 vd ->
    vd <> 0 -> 0 <= vd < 2 ^ 64 ->
    0 <= phi -> phi + 50 <= 2 ^ 64 -> 0 <= s2a -> s2a + 32 <= 2 ^ 64 -> 0 <= spv -> spv < 2 ^ 64 ->
    bytes_at rsegs m (phi + 18) ls -> bytes_at rsegs m s2a rs -> memcmp_model ls rs 32 = Some v ->
    ro_agree rsegs m -> addressable m (phi + 18) 32 -> addressable m s2a 32 ->
    end_in_app (phi + 18) 32 -> end_in_app s2a 32 -> app_mem (phi + 18 + 7) -> app_mem (s2a + 7) ->
    (phi + 18 + 32 <= spv - BCMP_WRAP_K \/ spv <= phi + 18) -> (s2a + 32 <= spv - BCMP_WRAP_K \/ spv <= s2a) ->
    stk rsegs m lo spv -> lo + BCMP_WRAP_K <= spv -> HIGHMEM_BEG <= lo -> spv <= APPMEM_END ->
    asan_cells m -> shadow_rw m ->
    bytes_at rsegs m REAL_BCMP (le8 (wa BCMP)) -> bytes_at rsegs m REAL_MEMCMP (le8 (wa MEMCMP)) ->
    bytes_at rsegs m GOT_CF (le8 (wa CF)) ->
    bytes_at rsegs m (CF + 254) [Z_to_bv 8 1] -> bytes_at rsegs m (CF + 255) [Z_to_bv 8 1] ->
    evt rsegs
      (fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : word -> option byte),
         ms' = MS (mkR (Z_to_bv 64 0x818e8) sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 v)
                       a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                  F (Z_to_bv 64 0x818e8) fc None m' (seg_rom rsegs) /\
         munch [(spv - BCMP_WRAP_K, spv)] m m' /\ wmono rsegs m m' /\
         ro_agree rsegs m' /\ stk rsegs m' lo spv)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x818d0) fc None m (seg_rom rsegs)).
Proof.
  intros BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    F fc m spv phi s2a vd v lo ls rs Esp Es11 Es2 Ea0 Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
    HL HRr HM HRO AL AR EL ER PL PR RL RR ST HK Hlo Hsp AC SW RB RM GC C254 C255.
  assert (HHB : HIGHMEM_BEG = 0x10007fff8000) by reflexivity.
  pose proof (mem_rel_normalize rsegs m HRO) as REL.
  eapply evt_mono.
  { eapply (evt_normalize rsegs _ _ _ _ _ _ _ _ wx_apart_asan HRO).
    exact (r19_run BC ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
             F fc (normalize rsegs m) spv phi s2a vd v lo ls rs Esp Es11 Es2 Ea0 Hvd Hvdb Hp0 Hpa Hs0 Hsa Hsp0 Hsp1
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) HL) (proj1 (bytes_at_rel rsegs m _ _ _ REL) HRr) HM
             (mem_inv_normalize rsegs m)
             (proj1 (b3n_rel_ad m _ _ _ REL) AL) (proj1 (b3n_rel_ad m _ _ _ REL) AR) EL ER PL PR RL RR
             (proj1 (b3n_rel_stk m _ lo spv REL ltac:(lia) ltac:(lia)) ST) HK Hlo Hsp
             (proj1 (b3n_rel_cells m _ REL) AC) (proj1 (b3n_rel_sw m _ REL) SW)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) RB) (proj1 (bytes_at_rel rsegs m _ _ _ REL) RM)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) GC)
             (proj1 (bytes_at_rel rsegs m _ _ _ REL) C254) (proj1 (bytes_at_rel rsegs m _ _ _ REL) C255)). }
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

Section R19W.
Context {fx : FPState} {LS : lib_shape} {rc : RunCeil}.
Variable B : malloc_syms.
Variable APIf : forall rc : RunCeil, ACw.AsanAllocAPI ACw.ASYMS AsanRTInv.RT.
Context {SH : sink_head} {SK : sink_syms}.
Variables ra empty : Z.
Hypothesis FF : frame_facts B APIf LS SH SK ra empty.
Hypothesis BC : bcmp_wrap_contract.

(* The allocator laws whose inner lists this file takes apart (Contract.v, a Theorem Labs lane's v1.9 generation), each restated
   once here, so that a law that gains or moves a conjunct breaks this one proof and no use site (a Theorem Labs lane 15:32Z). *)
Local Notation law_AH := (ACw.aa_AH ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_own := (ACw.aa_owned ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_lo := (ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc)).
Local Notation law_hi := (ACw.aa_stkhi ACw.ASYMS AsanRTInv.RT (APIf rc)).

Lemma r19_law_blocks : forall H mem md p n, law_AH H mem md -> In (p, n) H ->
  p mod 16 = 0 /\ 4096 <= p /\ p + n <= law_lo mem md /\ end_in_app p n /\
  forall a, p <= a < p + n -> app_mem a /\ writable_at rsegs mem a /\ ~ ACw.a_in_img a /\ ~ ACw.a_on_img_page a /\
    ~ ACw.a_in_fs ACw.ASYMS mem a.
Proof. exact (ACw.a_laws_blocks _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r19_law_fs_place : forall H mem md b, law_AH H mem md -> word_mem rsegs mem (ACw.as_tp ACw.ASYMS) b -> 0 <= b < 2 ^ 64 ->
  ACw.GT <= b /\ b + ACw.FS_SIZE <= law_lo mem md /\ b mod 4096 = 0 /\ forall a, b <= a < b + ACw.FS_SIZE -> app_mem a.
Proof. exact (ACw.a_laws_fs_place _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

Lemma r19_law_store : forall H mem mem' md, law_AH H mem md ->
  (forall a, 0 <= a < 2 ^ 64 -> ~ ACw.a_store_ok H (law_lo mem md) a -> mem' (Z_to_bv 64 a) = mem (Z_to_bv 64 a)) ->
  (forall a, 0 <= a < 2 ^ 64 -> writable_at rsegs mem a -> writable_at rsegs mem' a) ->
  law_AH H mem' md /\ (forall a, law_own H mem' md a <-> law_own H mem md a) /\ law_lo mem' md = law_lo mem md /\
  law_hi mem' md = law_hi mem md.
Proof. exact (ACw.a_laws_store _ _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))). Qed.

(* The entry cut of R19 is the official Inv_A818d0_at: it carries HB(Phi_r, n_b), the bound 0 <= vd < 2^64, the
   32-byte length of the declaration and the 32 bytes at decl_slot fr addressable (with b = 0).  The rest of what
   the wrapper needs is FRA's: app_mem (decl_slot fr + 32) from fra_app (decl_slot fr + 32 = fr + 2592 is a frame
   byte), the window's addressability, the window [sp - BCMP_WRAP_K, sp) in application memory from
   sp <= A <= S < APPMEM_END, the frame apart from that window from fra_frame at K = BCMP_WRAP_K <= FN_STACK, and
   the wrapper's mem_inv premise inside the run (r19_evt, from FRA's ro_agree). *)

(* The run of R19 from the facts at 0x818d0 (shared by seg_R19 and seg_R19s): the wrapper call on the 32 bytes ls at
   Phi_r + 18 and the declaration at decl_slot fr (memcmp value v).  The continuation gets FRA and HB at 0x818e8,
   a0 = v, s5/s6/s7/s8/s9 kept, every byte run inside the frame, the block [Phi_r, Phi_r + n_b) or a block of the
   entry heap kept (a live block ends at or below stklo, so below the wrapper's window), every spill [s1 + off]
   with 0 <= off <= 304 kept (the wrapper writes only below sp <= s1) and every addressable range kept (the
   wrapper writes no shadow byte). *)
Lemma r19_core : forall (g : ghost) (b : nat) (phi vd : Z) (regs : bvmap 5 word) (mem : word -> option byte)
    (md : Model) (fr : Z) (ls : list byte) (v : Z),
  FRA B APIf ra g fr (hb1 phi (rnb g b)) regs mem md ->
  ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem md ->
  RFb g fr b (RID (g_in g) b) (RFG (g_in g) b) phi regs mem ->
  rg regs 10 vd -> vd <> 0 -> 0 <= vd < 2 ^ 64 -> rg regs 27 (phi + 18) -> rg regs 18 (decl_slot fr) ->
  bytes_at rsegs mem (decl_slot fr) (RcDecl.decl (rt_mb (g_in g))) ->
  HB mem phi (rnb g b) -> addressable mem (decl_slot fr) 32 ->
  bytes_at rsegs mem (phi + 18) ls -> memcmp_model ls (RcDecl.decl (rt_mb (g_in g))) 32 = Some v ->
  (forall regs'' mem' md',
     FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md' ->
     ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem' md' -> HB mem' phi (rnb g b) ->
     (forall a bs, bytes_at rsegs mem a bs ->
        (forall x, a <= x < a + Z.of_nat (length bs) ->
           fr <= x < fr + FRAME_BYTES \/ phi <= x < phi + rnb g b \/ ACw.in_blocks (g_H g) x) ->
        bytes_at rsegs mem' a bs) ->
     getr regs'' 10 = Z_to_bv 64 v -> getr regs'' 22 = getr regs 22 -> getr regs'' 23 = getr regs 23 ->
     getr regs'' 24 = getr regs 24 -> getr regs'' 25 = getr regs 25 -> getr regs'' 21 = getr regs 21 ->
     (forall off vv, 0 <= off -> off + 8 <= 312 -> spill regs mem off vv -> spill regs'' mem' off vv) ->
     (forall p n, addressable mem p n -> addressable mem' p n) ->
     SR (ms_segs B) (mkCfg (mkst regs'' (Z_to_bv 64 0x818e8) mem' (seg_rom (ms_segs B))) md') (Post B APIf ra g)) ->
  SR (ms_segs B) (mkCfg (mkst regs (Z_to_bv 64 0x818d0) mem (seg_rom (ms_segs B))) md) (Post B APIf ra g).
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g b phi vd regs mem md fr ls v HFRA HENT HRF H10 Hvd Hvdb H27 H18 HDB HHB HAD
    HLS Hv Hk.
  pose proof (proj1 FF) as SEGS.
  (* the frame is apart from the wrapper's window [sp - BCMP_WRAP_K, sp) (fra_frame, BCMP_WRAP_K <= FN_STACK) *)
  pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HFP & _ & _ & _).
  pose proof (HFP BCMP_WRAP_K ltac:(unfold FN_STACK, AFw.SLOT_STACK, BCMP_WRAP_K; lia)) as HSEPf.
  clear HFP.
  (* every frame byte is application memory (fra_app), so the declaration slot's end is *)
  pose proof (fra_app B APIf ra g fr (hb1 phi (rnb g b)) regs mem md HFRA) as (HGTfr & Happfr).
  assert (HAPd : app_mem (decl_slot fr + 32)) by (apply Happfr; unfold decl_slot; lia).
  pose proof HFRA as HFRA2.
  destruct HFRA2 as (A & sp & s5 & HRT & HAH & Hro & Hsn & Hhalt & Hgimg & Hr2 & Hspm & Haspz &
    Hstklo & Hr4 & Hr8 & Hr9 & Hr3 & Hr19 & Hr26 & Hfrm & Hs5 & HAm & HAS & Hspa & Hfa & HA416 & HS4 & HAPP &
    Hspill & Hsel & Hfr24 & Hloc & Hhdr1 & Hhdr2 & Hsh & Hwin & Hsaved & Herrno & HAG & HWA &
    HSHI1 & HSHI2 & HSHI3 & Hhb & Hlive).
  rewrite Haspz in HSEPf.
  (* the wrapper's window is application memory: sp <= A <= S < APPMEM_END *)
  assert (HSPa : sp <= APPMEM_END) by lia.
  assert (Hspb : 0 <= sp < 2 ^ 64).
  { pose proof Haspz as Hs. unfold ACw.aspZ in Hs. rewrite Hr2, OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit_wrap in Hs.
    rewrite <- Hs. apply Z.mod_pos_bound. lia. }
  (* the real stack is in high application memory (a_laws_stack_high), so the window [sp - K, sp) is too *)
  pose proof (ACw.a_laws_stack_high ACw.ASYMS _ _ _ _ (ACw.aa_laws ACw.ASYMS AsanRTInv.RT (APIf rc))
                _ mem md HAH) as Hhigh.
  assert (HHI : HIGHMEM_BEG <= sp - BCMP_WRAP_K) by (unfold AFw.SLOT_STACK, BCMP_WRAP_K in *; lia).
  destruct HRT as (HAC & HSW & _ & HCF & _ & HREAL & _).
  destruct (r19_cells mem HCF HREAL) as (RB & RM & GC & C254 & C255).
  pose proof HRF as (_ & Hnz & _ & _).
  destruct (a_rtn (g_in g) (Z.of_nat b) Hnz) as (_ & Hnb & _).
  change (rt_n (g_in g) (Z.of_nat b)) with (rnb g b) in Hnb.
  pose proof (a_hb B APIf ra g fr phi (rnb g b) regs mem md HFRA) as (_ & _ & Hphistk & _ & _).
  pose proof HHB as (Hphinz & HAphi0).
  assert (Hsz : ACw.a_size (rnb g b) = rnb g b) by (unfold ACw.a_size; lia).
  pose proof HAphi0 as HAphi. rewrite Hsz in HAphi.
  (* the wrapper's premises *)
  assert (HA18 : addressable mem (phi + 18) 32) by (apply (addressable_sub mem phi (rnb g b) 18 32 HAphi); lia).
  pose proof HAphi as (Hp0 & _ & HpE & _).
  pose proof HAD as (Hd0 & _ & HdE & _).
  pose proof (addressable_app mem _ _ HAphi) as Happ_phi.
  pose proof (addressable_app mem _ _ HAD) as Happ_d.
  assert (Hphi50 : phi + 50 <= 2 ^ 64) by (unfold APPMEM_END in HpE; lia).
  assert (Hd32 : decl_slot fr + 32 <= 2 ^ 64) by (unfold APPMEM_END in HdE; lia).
  assert (PL : app_mem (phi + 18 + 7)) by (apply Happ_phi; lia).
  assert (EL : end_in_app (phi + 18) 32) by (unfold end_in_app; right; apply Happ_phi; lia).
  assert (PR : app_mem (decl_slot fr + 7)) by (apply Happ_d; lia).
  assert (ER : end_in_app (decl_slot fr) 32) by (unfold end_in_app; right; exact HAPd).
  assert (RL : phi + 18 + 32 <= sp - BCMP_WRAP_K \/ sp <= phi + 18)
    by (left; unfold AFw.SLOT_STACK, BCMP_WRAP_K in *; lia).
  assert (RR : decl_slot fr + 32 <= sp - BCMP_WRAP_K \/ sp <= decl_slot fr) by (unfold decl_slot; lia).
  assert (HST : stk rsegs mem (sp - BCMP_WRAP_K) sp).
  { destruct Hwin as (W0 & W1 & W2). split; [unfold HIGHMEM_BEG in HHI; lia|]. split; [lia|].
    intros a Ha. apply W2. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *; lia. }
  rewrite SEGS.
  eapply (sl_run_lib regs (Z_to_bv 64 0x818d0) mem md
    (fun R pc' mem' => pc' = Z_to_bv 64 0x818e8 /\
       getr R 2 = getr regs 2 /\ getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = getr regs 8 /\
       getr R 9 = getr regs 9 /\ getr R 19 = getr regs 19 /\ getr R 21 = getr regs 21 /\
       getr R 22 = getr regs 22 /\
       getr R 23 = getr regs 23 /\ getr R 24 = getr regs 24 /\ getr R 25 = getr regs 25 /\
       getr R 26 = getr regs 26 /\ getr R 10 = Z_to_bv 64 v /\
       OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.munch [(sp - BCMP_WRAP_K, sp)] mem mem' /\ OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.wmono rsegs mem mem' /\
       ro_agree rsegs mem' /\ stk rsegs mem' (sp - BCMP_WRAP_K) sp)
    (Post B APIf ra g)).
  - exact Hhalt.
  - unfold RegisterBridge.canonical_register_state; cbn [Regs6ss.mkR_of YK11.mkst].
    unfold rg in H10, H27, H18.
    eapply evt_mono.
    + apply (r19_evt BC) with (spv := sp) (phi := phi) (s2a := decl_slot fr) (vd := vd) (v := v)
        (lo := sp - BCMP_WRAP_K) (ls := ls) (rs := RcDecl.decl (rt_mb (g_in g))).
      all: try assumption.
      all: lia.
    + intros ms' (t0' & t1' & t2' & a1' & a2' & a3' & a4' & a5' & a6' & a7' & t3' & t4' & t5' & t6' & m' &
                  Hms & MUq & WMq & ROq & STq).
      do 3 eexists. split; [exact Hms|].
      split; [reflexivity|].
      do 13 (split; [reflexivity|]).
      split; [exact MUq|]. split; [exact WMq|]. split; [exact ROq | exact STq].
  - intros R pc' mem' regs'' md'
      (Hpc & K2 & K3 & K4 & K8 & K9 & K19 & K21 & K22 & K23 & K24 & K25 & K26 & K10 & MU & WM & HRO' & STk) Hreg
      Hmat.
    subst pc'.
    (* AH and the real-stack bottom are kept: the wrapper writes only [sp - K, sp), real-stack bytes above stklo,
       so every byte outside a_store_ok is unchanged (a_laws_store). *)
    pose proof (r19_law_store
                  (hb1 phi (rnb g b) ++ g_H g) mem mem' md HAH) as HLW.
    lapply HLW; [clear HLW; intros HLW|].
    2:{ intros a Ha Hns. apply MU. rewrite OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.MState.unsigned_lit by lia. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I].
        intros Hin. apply Hns. unfold ACw.a_store_ok. right. left. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *. lia. }
    lapply HLW; [clear HLW; intros HLW|].
    2:{ intros a _ Hw. exact (WM _ Hw). }
    destruct HLW as (HAH' & HOWN' & HSTK' & HSTKHI').
    (* ENT across the wrapper's store: it writes only [sp - BCMP_WRAP_K, sp), which is inside the slot window
       (sp <= A <= g_S g and g_S g - 4096 < sp), so no byte ENT speaks of changes (ent_store). *)
    assert (HENT1 : ENT (fx := fx) APIf g (hb1 phi (rnb g b)) mem' md).
    { eapply ent_store; [exact HENT | exact HFRA | exact MU | | | |].
      - intros x Hx. destruct (Z_le_gt_dec (sp - BCMP_WRAP_K) x) as [H1|H1].
        + destruct (Z_lt_ge_dec x sp) as [H2|H2].
          * right; left. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *. lia.
          * left. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [lia | exact I].
        + left. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [lia | exact I].
      - exact HSTK'.
      - exact HSTKHI'.
      - intros a _ Ho. exact (proj2 (HOWN' a) Ho). }
    assert (HRDM : rd_mono mem mem').
    { apply (rd_mono_list [(sp - BCMP_WRAP_K, sp)] mem mem' MU).
      constructor; [|constructor].
      cbn [fst snd]. intros y Hy. exact (rd_of_stk mem' (sp - BCMP_WRAP_K) sp STk y Hy). }
    assert (HAW : all_app [(sp - BCMP_WRAP_K, sp)]).
    { cbn [all_app]. split; [|exact I]. intros a Ha. unfold app_mem. right.
      unfold HIGHMEM_BEG, APPMEM_END, BCMP_WRAP_K in *. lia. }
    assert (HDJ : rt_disjoint [(sp - BCMP_WRAP_K, sp)]).
    { unfold rt_disjoint; cbn [disjoint_from].
      unfold RT_LO, RT_HI, RT_GOT_AF, RT_AF, RT_GOT_VERB, RT_VERB, RT_GOT_CF, RT_CF, RT_TSDI, RT_TSDK, RT_PGSZ,
        RT_TP, RT_TSDMAIN, RT_REAL_LO, RT_REAL_HI, RT_IMAP, RT_IMEM, RT_MUG, RT_AGLOB, RT_AGLOB_LEN,
        HIGHMEM_BEG, BCMP_WRAP_K in *.
      repeat split; left; lia. }
    assert (HWfr : forall x, fr <= x < fr + FRAME_BYTES -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. lia. }
    assert (HWphi : forall x, phi <= x < phi + rnb g b -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *. lia. }
    assert (HWlo : forall x, 0 <= x < 6283264 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. unfold HIGHMEM_BEG, BCMP_WRAP_K in *. lia. }
    assert (HWhdr : forall x, fr <= x < fr + 24 -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. apply HWfr. lia. }
    unfold rg in Hr9.
    pose proof Hspill as (HsA & HsB & _). rewrite length_le8 in HsB.
    assert (HWrng : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 <= x < A0 + 312 ->
                  OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros A0 E x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. rewrite Hr9 in E.
      apply (r19_wrap_out A A0 (sp - BCMP_WRAP_K) sp x E); [lia | lia | unfold HIGHMEM_BEG in HHI; lia | lia | lia]. }
    assert (HWspill : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 304 <= x < A0 + 312 ->
                      OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros A0 E x Hx. apply (HWrng A0 E). lia. }
    assert (HWsel : forall A0, getr regs 9 = Z_to_bv 64 A0 -> forall x, A0 + 16 <= x < A0 + 32 ->
                    OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros A0 E x Hx. apply (HWrng A0 E). lia. }
    assert (HWsaved : forall x, g_S g - 104 <= x < g_S g -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. lia. }
    (* the frame's shadow bytes lie below HIGHMEM_BEG + 56 (decl_slot fr + 32 <= APPMEM_END), the window above
       stklo + SLOT_STACK - K >= HIGHMEM_BEG + 1044016 *)
    assert (HWsh : forall x, Sfr fr <= x < Sfr fr + FRAME_SHADOW -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros x Hx. cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I].
      unfold Sfr, shadow_addr, ASAN_K in Hx. unfold decl_slot in HdE.
      unfold HIGHMEM_BEG, APPMEM_END, AFw.SLOT_STACK, BCMP_WRAP_K in *. lia. }
    (* the window is above stklo, the FakeStack below it (a_laws_fs_place): W meets no FakeStack byte *)
    assert (HWfs : forall FS x, word_mem rsegs mem (ACw.as_tp ACw.ASYMS) FS -> 0 <= FS < 2 ^ 64 ->
      FS <= x < FS + ACw.FS_SIZE -> ~ (fr + 24 <= x < fr + FRAME_BYTES) -> OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside [(sp - BCMP_WRAP_K, sp)] x).
    { intros FS x Hwtp HFS Hx _.
      pose proof (r19_law_fs_place
                    (hb1 phi (rnb g b) ++ g_H g) mem md FS HAH Hwtp HFS) as (_ & HFSstk & _ & _).
      cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *. lia. }
    assert (HFRAmd : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md).
    { apply (b3_fr_cl B APIf ra empty FF g fr (hb1 phi (rnb g b)) regs regs'' mem mem' md
        [(sp - BCMP_WRAP_K, sp)] HFRA MU WM HRO'
        HAW HDJ HAH' HSTK' HWlo HWhdr (fun A0 E _ => HWspill A0 E)
        (fun A0 E _ => HWsel A0 E)
        HWsaved HWsh HWfs HRDM);
        (rewrite Hreg; assumption). }
    assert (HFRA' : FRA B APIf ra g fr (hb1 phi (rnb g b)) regs'' mem' md').
    { apply (sl_fra_move B APIf ra g fr (hb1 phi (rnb g b)) regs'' regs'' mem' md md' HFRAmd);
        try reflexivity. exact Hmat. }
    rewrite <- SEGS. apply Hk.
    + exact HFRA'.
    + eapply ent_mat; [exact HENT1 | exact Hmat].
    + split; [exact Hphinz|].
      exact (sl_addr_keep mem mem' _ phi (ACw.a_size (rnb g b)) HAphi0 MU HAW).
    + intros a bs Hb Hin. apply (a_keep [(sp - BCMP_WRAP_K, sp)] mem mem' a bs MU); [|exact Hb].
      intros x Hx. destruct (Hin x Hx) as [Hf | [Hp | (qb & kb & Hqk & Hxq)]];
        [exact (HWfr x Hf) | exact (HWphi x Hp) |].
      destruct (r19_law_blocks
                  (hb1 phi (rnb g b) ++ g_H g) mem md qb kb HAH (in_or_app _ _ _ (or_intror Hqk)))
        as (_ & _ & Hqend & _ & _).
      assert (Hstkle : ACw.aa_stklo ACw.ASYMS AsanRTInv.RT (APIf rc) mem md <= g_S g - AFw.SLOT_STACK)
        by exact Hstklo.
      cbn [OSSVerify.Proofs.libreac.fuzz_ctrl.lib.A.Tk.UL.Frame.outside]. split; [|exact I]. unfold AFw.SLOT_STACK, BCMP_WRAP_K in *. lia.
    + rewrite Hreg. exact K10.
    + rewrite Hreg. exact K22.
    + rewrite Hreg. exact K23.
    + rewrite Hreg. exact K24.
    + rewrite Hreg. exact K25.
    + rewrite Hreg. exact K21.
    + intros off vv Hoff1 Hoff2 (A0 & HA0 & HQ). exists A0.
      split; [unfold rg in HA0 |- *; rewrite Hreg, K9; exact HA0|].
      unfold q64 in *. apply (a_keep [(sp - BCMP_WRAP_K, sp)] mem mem' (A0 + off) _ MU); [|exact HQ].
      rewrite length_le8. intros x Hx. apply (HWrng A0); [exact HA0 | lia].
    + intros p n Hp. exact (sl_addr_keep mem mem' _ p n Hp MU HAW).
Qed.

(* ---- seg_R19s: turn b = 0; the exit adds RFb and a0 = 0.  The wrapper returns 0 because the 32 bytes at
   Phi_r + 18 are X(0)[18 .. 50) = the declaration of row m (B3Rtm.a_rtm_X0). ---- *)

(* Both official cuts end in the same block of R21 / Inv_A815cc_at facts, PRO and the loop-carried RXS (R19XS, its
   exact text); the wrapper keeps s5, the spills [s1 + off], the frame cells (frame bytes, still writable by FRA's
   fra_frame), the input block (a block of the entry heap) and every addressable range, so the block moves across
   the call (r19_xs_keep). *)
Definition R19XS (g : ghost) (fr : Z) (regs : bvmap 5 word) (m : word -> option byte) : Prop :=
  spill regs m 128 (fr + 544) /\ PRO g fr regs m /\ spill regs m 104 0x21140 /\
  spill regs m 96 0x1234 /\ spill regs m 64 0xe38f0000 /\ rg regs 21 (fr + 2176) /\
  spill regs m 112 (mrow (g_in g)) /\
  spill regs m 144 (fr + 2688) /\ spill regs m 192 (fr + 2768) /\
  (exists idb, rw_cells rsegs m (fr + 2688) [CB 38 idb]) /\ (exists junk, rw_cells rsegs m (fr + 2768) [CB 72 junk]) /\
  spill regs m 280 (fr + 3040) /\ spill regs m 240 (fr + 3056) /\
  (exists jy, rw_cells rsegs m (fr + 3040) [CB 1 jy]) /\ (exists junk, rw_cells rsegs m (fr + 3056) [CB 32 junk]) /\
  spill regs m 152 (Sfr fr + 68) /\
  addressable m (fr + 2176) 38 /\ RXS g fr regs m.

(* RXS (push 10) across a run that keeps the spills [A + 0] .. [A + 224) and the fragment record's addressability. *)
Lemma r19_rxs_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 0 <= off <= 216 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2256) 72 -> addressable m' (fr + 2256) 72) ->
  RXS g fr regs m -> RXS g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha (H48 & H56 & H88 & H80 & H72 & H16 & H8 & H192 & H216 & HA).
  split; [exact (Hs 48 _ ltac:(lia) H48)|].
  split; [exact (Hs 56 _ ltac:(lia) H56)|].
  split; [exact (Hs 88 _ ltac:(lia) H88)|].
  split; [exact (Hs 80 _ ltac:(lia) H80)|].
  split; [exact (Hs 72 _ ltac:(lia) H72)|].
  split; [exact (Hs 8 _ ltac:(lia) H16)|].
  split; [exact (Hs 0 _ ltac:(lia) H8)|].
  split; [exact (Hs 200 _ ltac:(lia) H192)|].
  split; [exact (Hs 216 _ ltac:(lia) H216) | exact (Ha HA)].
Qed.

(* PRO (push 13B, push 14D) across a run that keeps the spills [A + 32] .. [A + 280), our[]'s 6 bytes addressable
   and the input block: its bytes, and its addressability when it is a live block of the entry heap. *)
Lemma r19_pro_keep : forall g fr regs regs' (m m' : word -> option byte),
  (forall off v, 32 <= off <= 272 -> spill regs m off v -> spill regs' m' off v) ->
  (addressable m (fr + 2624) 6 -> addressable m' (fr + 2624) 6) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (In (g_p g, g_n g) (g_H g) -> addressable m (g_p g) (g_n g) -> addressable m' (g_p g) (g_n g)) ->
  PRO g fr regs m -> PRO g fr regs' m'.
Proof.
  intros g fr regs regs' m m' Hs Ha6 Hb Hia
    (H40 & H120 & H136 & H160 & H168 & H176 & H200 & H248 & HA6 & HIN & HG & H184 & H256 & H264 & H272 & H32).
  split; [exact (Hs 40 _ ltac:(lia) H40)|].
  split; [exact (Hs 120 _ ltac:(lia) H120)|].
  split; [exact (Hs 136 _ ltac:(lia) H136)|].
  split; [exact (Hs 160 _ ltac:(lia) H160)|].
  split; [exact (Hs 168 _ ltac:(lia) H168)|].
  split; [exact (Hs 176 _ ltac:(lia) H176)|].
  split; [exact (Hs 208 _ ltac:(lia) H200)|].
  split; [exact (Hs 248 _ ltac:(lia) H248)|].
  split; [exact (Ha6 HA6)|].
  split; [exact (Hb (fun Hn => proj1 (HG Hn)) HIN)|].
  split; [intros Hn; destruct (HG Hn) as (HH & HA); split; [exact HH | exact (Hia HH HA)]|].
  split; [exact (Hs 184 _ ltac:(lia) H184)|].
  split; [exact (Hs 256 _ ltac:(lia) H256)|].
  split; [exact (Hs 264 _ ltac:(lia) H264)|].
  split; [exact (Hs 272 _ ltac:(lia) H272) | exact (Hs 32 _ ltac:(lia) H32)].
Qed.

Lemma r19_xs_keep : forall g fr regs regs' m m',
  (forall off v, 0 <= off -> off + 8 <= 312 -> spill regs m off v -> spill regs' m' off v) ->
  getr regs' 21 = getr regs 21 -> (forall p n, addressable m p n -> addressable m' p n) ->
  ((0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
     bytes_at rsegs m (g_p g) (g_in g) -> bytes_at rsegs m' (g_p g) (g_in g)) ->
  (forall a n bs, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
     rw_cells rsegs m a [CB n bs] -> rw_cells rsegs m' a [CB n bs]) ->
  R19XS g fr regs m -> R19XS g fr regs' m'.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros g fr regs regs' m m' Hs E21 Had Hinb Hrw
    (H128 & HPRO & H104 & H96 & H64 & H21 & H112 & H144 & H208 & (idb & Hidb) & (junk & Hjk) & H280 & H240 &
     (jy & Hjy) & (sc & Hsc) & H152 & H38 & HRXS).
  split; [exact (Hs 128 _ ltac:(lia) ltac:(lia) H128)|].
  split; [exact (r19_pro_keep g fr regs regs' m m' (fun off v Ho H => Hs off v ltac:(lia) ltac:(lia) H)
                  (Had _ _) Hinb (fun _ => Had _ _) HPRO)|].
  split; [exact (Hs 104 _ ltac:(lia) ltac:(lia) H104)|].
  split; [exact (Hs 96 _ ltac:(lia) ltac:(lia) H96)|].
  split; [exact (Hs 64 _ ltac:(lia) ltac:(lia) H64)|].
  split; [unfold rg in *; rewrite E21; exact H21|].
  split; [exact (Hs 112 _ ltac:(lia) ltac:(lia) H112)|].
  split; [exact (Hs 144 _ ltac:(lia) ltac:(lia) H144)|].
  split; [exact (Hs 192 _ ltac:(lia) ltac:(lia) H208)|].
  split; [exists idb; exact (Hrw (fr + 2688) 38%nat idb ltac:(lia) ltac:(lia) Hidb)|].
  split; [exists junk; exact (Hrw (fr + 2768) 72%nat junk ltac:(lia) ltac:(lia) Hjk)|].
  split; [exact (Hs 280 _ ltac:(lia) ltac:(lia) H280)|].
  split; [exact (Hs 240 _ ltac:(lia) ltac:(lia) H240)|].
  split; [exists jy; exact (Hrw (fr + 3040) 1%nat jy ltac:(lia) ltac:(lia) Hjy)|].
  split; [exists sc; exact (Hrw (fr + 3056) 32%nat sc ltac:(lia) ltac:(lia) Hsc)|].
  split; [exact (Hs 152 _ ltac:(lia) ltac:(lia) H152)|].
  split; [exact (Had _ _ H38)|].
  exact (r19_rxs_keep g fr regs regs' m m' (fun off v Ho H => Hs off v ltac:(lia) ltac:(lia) H) (Had _ _) HRXS).
Qed.

Lemma seg_R19s : forall b, Hat B APIf ra (Inv_A818e8_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A818d0_at (fx := fx) B APIf ra) b.
Proof.
  pose proof FRAME_BYTES_val as HFBv. pose proof FRAME_SHADOW_val as HFSv.
  intros b Hexit g c HInv.
  destruct HInv as (phi & vd & regs & mem & md & fr & Ec & HFRA & HENT &
    ((Hgn & HRF & HOUTA & H10 & Hvd & H27 & H18 & HDB) & Hb0 & HHB & Hvdb & HLD & HAD & HXS)).
  subst c. subst b.
  pose proof HRF as ((Hb6 & HCUR & HOUR & H23 & HIDB & HFGB) & Hnz & H24 & HF).
  destruct (a_rtn (g_in g) (Z.of_nat 0) Hnz) as (_ & Hnb & HLF).
  change (rt_n (g_in g) (Z.of_nat 0)) with (rnb g 0) in Hnb, HLF.
  change (Z.of_nat 0) with 0 in HLF, HF.
  assert (HLS : bytes_at rsegs mem (phi + 18) (firstn 32 (skipn 18 (rt_F (g_in g) 0)))).
  { pose proof HF as HF'. rewrite <- (firstn_skipn 18 (rt_F (g_in g) 0)) in HF'.
    apply bytes_at_app in HF' as [_ HF'].
    rewrite length_firstn, Nat.min_l in HF' by lia.
    rewrite <- (firstn_skipn 32 (skipn 18 (rt_F (g_in g) 0))) in HF'.
    apply bytes_at_app in HF' as [HF' _]. exact HF'. }
  assert (EX : firstn 32 (skipn 18 (rt_F (g_in g) 0)) = RcDecl.decl (rt_mb (g_in g))).
  { rewrite <- (B3Rtm.a_rtm_X0 (g_in g)). unfold RcFrag.bsl, rt_g, fr50.
    change (Z.to_nat 32) with 32%nat. change (Z.to_nat 18) with 18%nat.
    rewrite firstn_app. replace (50 - length (rt_F (g_in g) 0))%nat with 0%nat by lia.
    rewrite firstn_O, app_nil_r, skipn_firstn_comm, firstn_firstn. reflexivity. }
  rewrite EX in HLS.
  apply (r19_core g 0 phi vd regs mem md fr _ 0 HFRA HENT HRF H10 Hvd Hvdb H27 H18 HDB HHB HAD HLS
           (r19_memcmp_refl (RcDecl.decl (rt_mb (g_in g))) 32%nat ltac:(lia))).
  intros regs'' mem' md' HFRA' HENT' HHB' Hkeep K10 K22 K23 K24 K25 K21 Hspk Hadk.
  assert (HOUR' : OURb g fr mem').
  { unfold OURb in *. apply (Hkeep _ _ HOUR). rewrite OUR_length. intros x Hx. left. lia. }
  assert (HCUR' : CUR g 7 regs'').
  { destruct HCUR as (Hc0 & Hc22 & Hc25). unfold CUR, rg in *.
    split; [exact Hc0|]. split; [rewrite K22; exact Hc22 | rewrite K25; exact Hc25]. }
  assert (H23' : rg regs'' 23 (Z.of_nat 0)) by (unfold rg in *; rewrite K23; exact H23).
  apply Hexit. exists phi, regs'', mem', md', fr.
  split; [reflexivity|]. split; [exact HFRA'|]. split; [exact HENT'|].
  split.
  { split; [exact Hgn|]. split; [exact Hb6|]. split; [exact HHB'|]. split; [exact H23'|].
    split; [exact HOUR'|]. split; [exact (Hadk (fr + 544) 1492 HOUTA) | exact HCUR']. }
  split; [reflexivity|].
  split.
  { split.
    - split; [exact Hb6|]. split; [exact HCUR'|]. split; [exact HOUR'|]. split; [exact H23'|].
      split.
      + unfold IDBr in *. apply (Hkeep _ _ HIDB).
        assert (LI : length (RID (g_in g) 0) = 38%nat) by reflexivity.
        rewrite LI. intros x Hx. left. lia.
      + unfold FGBr in *. apply (Hkeep _ _ HFGB).
        assert (LF : length (RFG (g_in g) 0) = 72%nat) by reflexivity.
        rewrite LF. intros x Hx. left. lia.
    - split; [exact Hnz|]. split; [unfold rg in *; rewrite K24; exact H24|].
      apply (Hkeep _ _ HF). intros x Hx. right. left. rewrite HLF, Z2Nat.id in Hx by lia. exact Hx. }
  split; [unfold a0v, rg; exact K10|].
  (* the frame records: their bytes are frame bytes (kept), and every frame byte is writable at mem' (fra_frame) *)
  assert (HRWk : forall a n bs, fr <= a -> a + Z.of_nat n <= fr + FRAME_BYTES ->
            rw_cells rsegs mem a [CB n bs] -> rw_cells rsegs mem' a [CB n bs]).
  { intros a n bs Ha1 Ha2 ((Hwf & Hb) & Hw).
    pose proof (fra_frame B APIf ra g fr (hb1 phi (rnb g 0)) regs'' mem' md' HFRA') as (_ & _ & _ & Hfw).
    assert (Hlen : length bs = n) by (destruct Hwf as (Hl & _); exact Hl).
    split; [split; [exact Hwf|]|].
    - apply (Hkeep _ _ Hb). intros x Hx. left.
      cbn [cells_bytes cbytes] in Hx. rewrite app_nil_r, Hlen in Hx. lia.
    - destruct Hw as (Hw0 & Hw1 & _). split; [exact Hw0|]. split; [exact Hw1|].
      intros i Hi. cbn [cells_size csize] in Hi. exact (Hfw (a + i) ltac:(lia)). }
  (* PRO's input block is a block of the entry heap, which the wrapper keeps *)
  assert (HINk : (0 < g_n g -> In (g_p g, g_n g) (g_H g)) ->
            bytes_at rsegs mem (g_p g) (g_in g) -> bytes_at rsegs mem' (g_p g) (g_in g)).
  { intros Hin HIN. apply (Hkeep _ _ HIN). intros x Hx. rewrite <- g_n_len in Hx.
    right. right. exists (g_p g), (g_n g). split; [exact (Hin ltac:(lia)) | exact Hx]. }
  exact (r19_xs_keep g fr regs regs'' mem mem' Hspk K21 Hadk HINk HRWk HXS).
Qed.

(* seg_R19: the same segment; since push 6c the official cuts are the B3 bodies, so it is seg_R19s. *)
Lemma seg_R19 : forall b, Hat B APIf ra (Inv_A818e8_at (fx := fx) B APIf ra) b ->
  Hat B APIf ra (Inv_A818d0_at (fx := fx) B APIf ra) b.
Proof. exact seg_R19s. Qed.

End R19W.
