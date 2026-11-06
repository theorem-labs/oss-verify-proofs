(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Stdio_iface RDriverA_kit RDriverA_ctx RDriverA_main RF_mainA_A.
Import ListNotations.
Open Scope Z_scope.

Definition fuzz_entryA : Z := 0x86514.

Definition PARSER_STACK_A : Z := 69632.

Definition EMPTY_OBJ_A : Z := 0x5e5f60.

Notation MAX_INPUT_A := 67108864%Z (only parsing).

Definition FZ_NSEC : Z := 13552000.

Definition DRV_NSEC : Z := 1025.
Lemma nsec_total : DRV_NSEC + 4 * FZ_NSEC <= A0_NSEC_MAX.
Proof. unfold DRV_NSEC, FZ_NSEC, A0_NSEC_MAX. lia. Qed.

Section FZ.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Variable J : a0_judg FI AI.

  Variable PZ : mem -> Prop.
  Local Notation K := (am_K FI AI).
  Local Notation BL := (list (AllocIF.block K)).
  Local Notation PS := (aps FI AI).

  Definition pclient (LB : BL) (q a : Z) : Prop :=
    q <= a
    \/ (exists lo hi, am_static FI AI lo hi /\ lo <= a < hi /\ ~ (A0_ERRNO <= a < A0_ERRNO + 4))
    \/ in_block LB a
    \/ (exists b, In b LB /\ sh (blk_addr b) <= a < sh (blk_addr b) + Z.of_nat (length (block_shadow (blk_size b)))).
  Definition pkeep (LB : BL) (q : Z) (m m' : mem) : Prop :=
    forall a, 0 <= a < 2^64 -> pclient LB q a -> gkeep m m' (wa a) /\ (wview asegs m (wa a) <> None -> wview asegs m' (wa a) <> None).

  #[using="Type"] Lemma am_budget_short : forall (s : PS) (LB : BL) n, 0 <= n -> Z.of_nat (length LB) < 2^13 ->
    Forall (fun b : block (am_K FI AI) => 0 <= blk_size b) LB -> lb_bytes FI AI LB + n <= 2^31 ->
    am_nsec FI AI s + 1 <= A0_NSEC_MAX -> am_budget FI AI s LB n.
  Proof.
    intros s LB n Hn HL HF HB HN. apply (am_budget_of_length FI AI); [exact Hn| exact HL| | exact HN].
    pose proof (bl_sub_bytes FI AI _ _ HF (bl_sub_filter FI AI (fun b => a0_cls (blk_size b) =? 0) LB)) as X.
    unfold A0_SEC_BYTES, lb_cls. lia.
  Qed.

  #[using="Type"] Lemma ac_malloc_any : forall (AC : am_contracts FI AI J)
           (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (n lo : Z),
    RHEAP_A FI AI s LB m -> asan_env asegs m -> RFAKE FI st m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q <= alloc_ceiling + 2^23 ->
    mem_inv asegs m ->
    ~ valid_frame (am_stack_top FI AI) q (bv_unsigned s0) -> In [PC0_MALLOC; bv_unsigned ra] A0_TRACES ->
    a0 = Z_to_bv 64 n -> 0 <= n <= A0_MAXREQ -> am_budget FI AI s LB n ->
    AJ FI AI J (malloc_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s LB n lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (Z_to_bv 64 A0_malloc) fc None m (seg_rom asegs))
      s LB.
  Proof.
    intros AC. intros until lo. intros HR AE RF ST CLO LO QAL QLE MI NV TR -> Hn BUD.
    destruct (Z_lt_ge_dec (q + 16) (am_stack_top FI AI)) as [LT|GE].
    - eapply (ac_malloc FI AI J AC) with (ras := []); first [eassumption | reflexivity].
    - eapply (ac_malloc_top FI AI J AC); first [eassumption | reflexivity | lia].
  Qed.
  #[using="Type"] Lemma ac_free_any : forall (AC : am_contracts FI AI J)
           (ra : word) (q : Z) (gp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F_ : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI) (k : K) (A n lo : Z),
    RHEAP_A FI AI s LB m -> In (k, A, n) LB -> asan_env asegs m -> RFAKE FI st m ->
    stk asegs m lo q -> alloc_ceiling <= lo -> lo <= q - A0_RT_STACK -> q mod 16 = 0 -> q <= alloc_ceiling + 2^23 ->
    mem_inv asegs m ->
    ~ valid_frame (am_stack_top FI AI) q (bv_unsigned s0) -> In [PC0_FREE; bv_unsigned ra] A0_TRACES ->
    a0 = Z_to_bv 64 A ->
    AJ FI AI J (free_post_A FI AI ra q gp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F_ fc st s (lb_remove (am_K_eqb FI AI) k LB) lo m)
      (MS (mkR ra (Z_to_bv 64 q) gp (Z_to_bv 64 A0_TP) t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F_ (Z_to_bv 64 A0_free) fc None m (seg_rom asegs))
      s LB.
  Proof.
    intros AC. intros until lo. intros HR HIN AE RF ST CLO LO QAL QLE MI NV TR ->.
    destruct (Z_lt_ge_dec (q + 16) (am_stack_top FI AI)) as [LT|GE].
    - eapply (ac_free FI AI J AC) with (ras := []); first [eassumption | reflexivity].
    - eapply (ac_free_top FI AI J AC); first [eassumption | reflexivity | lia].
  Qed.

  #[using="Type"] Lemma pkeep_agree : forall LB q m m', pkeep LB q m m' -> gagree_on (pclient LB q) m m'.
  Proof. intros LB q m m' H a Ha Hc. exact (H a Ha Hc). Qed.
  #[using="Type"] Lemma apres_pkeep : forall LB q m m', apres FI AI LB q m m' -> pkeep LB q m m'.
  Proof.
    intros LB q m m' H a Ha Hc. apply H; [exact Ha|]. unfold aclient, pclient in *.
    destruct Hc as [X|[X|[X|X]]]; [left; exact X| destruct X as (lo & hi & S1 & S2 & _); right; left; exists lo, hi; split; assumption| right; right; left; exact X| do 5 right; exact X].
  Qed.

  Definition fuzz_one_postA (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
      (st : fsstate FI) (s : PS) (LB : BL) (lo : Z) (canary : word) (m : mem) : PS -> BL -> machine_state -> Prop :=
    fun s' LB' ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m' st',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 0) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom asegs)
      /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ asan_env asegs m' /\ RFAKE FI st' m'
      /\ pkeep LB (bv_unsigned sp) m m'
      /\ fs_live FI st' = fs_live FI st
      /\ RHEAP_A FI AI s' LB' m'
      /\ (forall b, In b LB -> In b LB') /\ (forall b, In b LB' -> In b LB)
      /\ am_nsec FI AI s' <= am_nsec FI AI s + FZ_NSEC
      /\ PZ m'
      /\ (exists errv', rw_cells asegs m' RERRNOA [C4 errv'])
      /\ shz m' (sh lo) (sh (bv_unsigned sp))
      /\ rw_cells asegs m' got_ssp [C8 (Z_to_bv 64 ssp_guard)] /\ rw_cells asegs m' ssp_guard [C8 canary].

  Definition fuzz_one_stmtA : Prop :=
    forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
           (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : PS) (LB : BL) (st : fsstate FI)
           (D n lo : Z) (errv canary : word) (data : list byte),

      bytes_at asegs m D data -> Z.of_nat (length data) = n -> 0 <= n <= 2^26 ->
      ((n = 0 /\ D = EMPTY_OBJ_A) \/ (exists k, In (k, D, n) LB)) ->
      RHEAP_A FI AI s LB m -> RFAKE FI st m -> fs_call_ok FI st tp 6 -> asan_env asegs m ->
      Z.of_nat (length LB) <= 2 -> lb_bytes FI AI LB <= 2^27 ->
      am_nsec FI AI s + FZ_NSEC <= A0_NSEC_MAX ->
      stk asegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - PARSER_STACK_A ->
      bv_unsigned sp mod 16 = 0 -> bv_unsigned sp + 16 < am_stack_top FI AI ->

      shz m (sh lo) (sh (bv_unsigned sp)) -> shr m (sh lo - sh lo mod 8) (sh (bv_unsigned sp) + 8) ->

      shw m 0x5d5f40 0x10040 -> shw m 0x10000 0x113e0 ->
      rw_cells asegs m RERRNOA [C4 errv] -> mem_inv asegs m -> PZ m ->
      rw_cells asegs m got_ssp [C8 (Z_to_bv 64 ssp_guard)] -> rw_cells asegs m ssp_guard [C8 canary] ->
      tp = Z_to_bv 64 RATPA -> a0 = Z_to_bv 64 D -> a1 = Z_to_bv 64 n -> s0 = Z_to_bv 64 n ->
      ra = Z_to_bv 64 0x86410 ->
      frm0 fc ->
      AJ FI AI J (fuzz_one_postA ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st s LB lo canary m)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 fuzz_entryA) fc None m (seg_rom asegs))
        s LB.
End FZ.

Section IFACE.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Variable PZ : mem -> Prop.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Local Notation K := (am_K FI AI).

  Definition CJ1 (mm : mem) : Prop :=
    rw_cells asegs mm 0x5e5f50 [C1 (Z_to_bv 8 1)] /\ rw_cells asegs mm 0x5e5f60 [CB 16 (repeat (Z_to_bv 8 0) 16)].

  Definition TRFRAME (mm : mem) (pad : list byte) (sc PL A L : Z) : Prop :=
    rw_cells asegs mm (usp0 + -208)
      [CB 8 pad; C8 (Z_to_bv 64 0); C8 (Z_to_bv 64 RSVA); C8 (Z_to_bv 64 sc); C8 (Z_to_bv 64 PL); C8 (Z_to_bv 64 (A + 6 + L)); C8 (Z_to_bv 64 L);
       C8 (Z_to_bv 64 A); C8 (Z_to_bv 64 (A + 2)); C8 (Z_to_bv 64 0x861e8)].

  Definition rat_parserA (ap : at_parser (ptr:=unit)) (so : ASt) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (mm : mem)
           (A cap L sc AL OW : Z) (DATA junk mpad pad : list byte) (errv : word) (LB : list (AllocIF.block K))
           (s : aps FI AI) (st : fsstate FI) (kb : K),
      ms = MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2
                   (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 AL) a0 a1 a2 a3 a4 a5 a6 a7
                   (Z_to_bv 64 OW) (Z_to_bv 64 (A + 2)) (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 (ap_calls ap)) (Z_to_bv 64 0) (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
              F (Z_to_bv 64 0x863fc) fc None mm (seg_rom asegs)
      /\ frm0 fc /\ so = stdout_init /\ g = gh FI AI s

      /\ ap_content ap = map bv_unsigned DATA /\ ap_config_len ap = L /\ ap_count ap = (sc <? 0)
      /\ 1 <= ap_calls ap <= 4
      /\ 6 + L <= Z.of_nat (length DATA) <= cap /\ cap <= MAX_INPUT_A /\ 0 <= L < 32768 /\ -128 <= sc < 128
      /\ (0x609000 <= A /\ A + cap + 16 <= alloc_ceiling /\ A mod 16 = 0 /\ win_ok A (cap + 16))
      /\ match ap_owned ap with
         | None => ap_payload_len ap = 0 /\ AL = EMPTY_OBJ_A /\ OW = 0 /\ LB = [(kb, A, cap)]
         | Some _ => exists kp : K, 0 < ap_payload_len ap /\ OW = AL /\ LB = [(kp, AL, ap_payload_len ap); (kb, A, cap)]
                     /\ rw_cells asegs mm AL [CB (Z.to_nat (ap_payload_len ap)) (skipn (Z.to_nat (6 + L)) DATA)]
                     /\ rw_cells asegs mm (sh AL) (shadow_cells (block_shadow (ap_payload_len ap)))
         end

      /\ RHEAP_A FI AI s LB mm /\ RFAKE FI st mm /\ fs_live FI st = []
      /\ am_nsec FI AI s + ap_calls ap * FZ_NSEC <= A0_NSEC_MAX
      /\ rw_cells asegs mm A [CB (length DATA) DATA; CB (Z.to_nat (cap - Z.of_nat (length DATA))) junk]
      /\ rw_cells asegs mm (sh A) (shadow_cells (block_shadow cap))
      /\ TRFRAME mm pad sc (ap_payload_len ap) A L /\ MFRAME sp0 argv mm mpad S7 S6 S5 S4
      /\ stk asegs mm (usp0 - 8388608) (usp0 + -208)
      /\ BASE_A2 PZ sp0 argv envp uid hw rnd TID stdout_init mm
      /\ rw_cells asegs mm RERRNOA [C4 errv]
      /\ CJ1 mm.
End IFACE.
