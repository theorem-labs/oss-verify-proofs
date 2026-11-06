(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation Strings.String.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Agree MonadX Ceiling.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import RunWord.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.ZAW Require Import Segs Shadow Contracts Globals IcptA0 AllocA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Lib Require Import InitStack EntrySecret.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Spec Require Import Prelim STree Monad Stdio Driver Prog.
From OSSVerify.pupnp.FuzzHttp.images Require Import Asan.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.ASN Require Import AsanAcct.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.Top Require Import AllocIF.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7 Require Import RealizeS SeamA0 A0Prog AssembleA0.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import ShadowKit GlobalsShadow Stdio_base Printf_lib F_printf_iface Stdio_iface F_printf_diag Exit RDriverA_kit RDriverA_ctx RDriverA_main RDriverA_exit RF_mainA_A.
From OSSVerify.Proofs.pupnp.FuzzHttp.lib.A0.T7A0 Require Import F_syscalls RDriverA_lib RDriverA_iface RF_mainA_B1 RF_mainA_B2 RF_mainA_B3 RF_mainA_B4 RF_mainA_C RF_mainA_T RF_mainA_post.
Import ListNotations.
Import ITree.Exc.
Open Scope Z_scope.
Open Scope mspec_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Ltac rpc := apply ret_pc_even; [lia| reflexivity].

Record dlayA {K : Type} := mkDL {
  d_A : Z;
  d_cap : Z;
  d_L : Z;
  d_sc : Z;
  d_AL : Z;
  d_OW : Z;
  d_DATA : list byte;
  d_junk : list byte;
  d_mpad : list byte;
  d_pad : list byte;
  d_kb : K;
  d_kp : K
}.
Arguments dlayA K : clear implicits.

Definition drv_status {K} (d : dlayA K) (fl : bool) : Z := if d_sc d <? 0 then 0 else if fl then 78 else 0.

Section SEAMS.
  Context {HC : HasCeiling} {HG : HasGuard}.
  Variable FI : fs_if.
  Variable AI : am_if FI.
  Hypothesis AMS : forall lo hi, a0_static lo hi -> am_static FI AI lo hi.
  Variable PZ : mem -> Prop.
  Hypothesis PZ_agree : forall (P : Z -> Prop) m m', gagree_on P m m' -> (forall a, pz_band a -> P a) -> PZ m -> PZ m'.
  Variables (sp0 : word) (argv envp : list (list byte)) (uid hw : word) (rnd : EntryDraw) (TID : Z) (S4 S5 S6 S7 S8 S9 S10 S11 : word).
  Hypothesis VSP : valid_sp sp0.
  Hypothesis CEIL : alloc_ceiling = LO sp0.
  Hypothesis ESF : entry_stack_fits sp0 argv envp.
  Hypothesis HT : 0 < TID < 2^31.
  Hypothesis EMIT : emit_printf_stmt aget_so aset_so.
  Local Notation K := (am_K FI AI).
  Local Notation BL := (list (AllocIF.block K)).
  Notation usp0 := (bv_unsigned sp0).
  Notation gpv := (Z_to_bv 64 0x10800).
  Notation tpv := (Z_to_bv 64 RATPA).
  Notation BASEs so mm := (BASE_A PZ sp0 argv envp uid hw rnd TID so mm).
  Notation BASE2s so mm := (BASE_A2 PZ sp0 argv envp uid hw rnd TID so mm).

  Notation TST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -208)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 x22 (Z_to_bv 64 (-2)) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).
  Notation GST pc x1 t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 t3 t4 t5 t6 F fc mm :=
    (MS (mkR x1 (Z_to_bv 64 (usp0 + -128)) gpv tpv t0 t1 t2 x8 x9 x10 x11 x12 x13 x14 x15 x16 x17 x18 x19 x20 x21 (Z_to_bv 64 RSVA) (Z_to_bv 64 0) S8 S9 S10 S11 t3 t4 t5 t6)
        F (Z_to_bv 64 pc) fc None mm (seg_rom asegs)).

  Definition DLAY_ok (ap : at_parser (ptr:=unit)) (d : dlayA K) : Prop :=
    ap_content ap = map bv_unsigned (d_DATA d) /\ ap_config_len ap = d_L d /\ ap_count ap = (d_sc d <? 0)
    /\ 1 <= ap_calls ap <= 4
    /\ 6 + d_L d <= Z.of_nat (length (d_DATA d)) <= d_cap d /\ d_cap d <= 67108864 /\ 0 <= d_L d < 32768 /\ -128 <= d_sc d < 128
    /\ (0x609000 <= d_A d /\ d_A d + d_cap d + 16 <= alloc_ceiling /\ d_A d mod 16 = 0 /\ win_ok (d_A d) (d_cap d + 16))
    /\ match ap_owned ap with
       | None => ap_payload_len ap = 0 /\ d_AL d = EMPTY_OBJ_A /\ d_OW d = 0
       | Some _ => 0 < ap_payload_len ap /\ d_OW d = d_AL d /\ (0x609000 <= d_AL d /\ d_AL d + ap_payload_len ap + 16 <= alloc_ceiling /\ d_AL d mod 16 = 0 /\ win_ok (d_AL d) (ap_payload_len ap + 16))
                   /\ d_kp d <> d_kb d
       end.

  Definition DBLOCKS (own : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (LB : BL) : Prop :=
    In (d_kb d, d_A d, d_cap d) LB
    /\ (own = true -> match ap_owned ap with Some _ => In (d_kp d, d_AL d, ap_payload_len ap) LB | None => True end).

  Definition DBYTES (own : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (m : mem) : Prop :=
    rw_cells asegs m (d_A d) [CB (length (d_DATA d)) (d_DATA d); CB (Z.to_nat (d_cap d - Z.of_nat (length (d_DATA d)))) (d_junk d)]
    /\ (own = true -> match ap_owned ap with
                      | Some _ => rw_cells asegs m (d_AL d) [CB (Z.to_nat (ap_payload_len ap)) (skipn (Z.to_nat (6 + d_L d)) (d_DATA d))]
                      | None => True end).

  Definition EXCB (cb : bool) (mm : mem) : Prop :=
    if cb then (exists m0 : mem, EXITC2 TID m0 /\ gagree_on exitc_addr m0 mm) /\ rw_cells asegs mm 0x5e5f54 [C1 (Z_to_bv 8 1)]
    else EXITC2 TID mm.

  Definition BASE_cb (cb : bool) (so : stdout_st) (mm : mem) : Prop :=
    stk asegs mm (LO sp0) (usp0 + -128) /\ mem_inv asegs mm /\ EXCB cb mm /\ MAINC0 mm /\ IMGK sp0 argv envp uid hw rnd mm
    /\ stderr_wfile0 mm /\ stdout_file mm so /\ stk asegs mm RSVA (RSVA + 65536) /\ stdin_file mm
    /\ SHZ sp0 argv envp uid hw rnd mm /\ asan_env asegs mm /\ globals_shadow mm /\ PZ mm /\ wr_at asegs mm 0xb0290 1.

  Definition DMEM (cb : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (m : mem) : Prop :=
    TRFRAME sp0 m (d_pad d) (d_sc d) (ap_payload_len ap) (d_A d) (d_L d)
    /\ MFRAME sp0 argv m (d_mpad d) S7 S6 S5 S4
    /\ BASE_cb cb so m /\ CJ1 m.

  Definition DST (cb own : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (s : aps FI AI) (st : fsstate FI) (LB : BL) (m : mem) : Prop :=
    DLAY_ok ap d /\ DMEM cb ap d so m /\ DBYTES own ap d m /\ DBLOCKS own ap d LB
    /\ RHEAP_A FI AI s LB m /\ RFAKE FI st m
    /\ (exists errv : word, rw_cells asegs m RERRNOA [C4 errv])
    /\ stk asegs m (usp0 - 8388608) (usp0 + -208).

  Definition DBUD (k : Z) (s : aps FI AI) (st : fsstate FI) (LB : BL) : Prop :=
    Z.of_nat (length LB) <= 2 /\ lb_bytes FI AI LB <= 2^27 /\ fs_live FI st = [] /\ am_nsec FI AI s + k * FZ_NSEC <= A0_NSEC_MAX.

  Definition rat_headA (k : Z) (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST 0x863fc x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 1 <= k <= ap_calls ap /\ DST false true ap d so s st LB m /\ DBUD k s st LB.

  Definition rat_callA (k : Z) (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST fuzz_entryA (Z_to_bv 64 0x86410) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 (d_AL d)) (Z_to_bv 64 (ap_payload_len ap)) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 1 <= k <= ap_calls ap /\ DST true true ap d so s st LB m /\ DBUD k s st LB.

  Definition rat_retA (k rc : Z) (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST 0x86410 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 rc) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ DST true true ap d so s st LB m /\ DBUD (k - 1) s st LB.

  Definition rat_emitA (k rc : Z) (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST 0x864cc (Z_to_bv 64 0x86420) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 rc) (Z_to_bv 64 rc) a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) (Z_to_bv 64 rc) (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ DST false true ap d so s st LB m /\ DBUD (k - 1) s st LB.

  Definition rat_emit_retA (k rc : Z) (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST 0x86420 x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) (Z_to_bv 64 rc) (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 k) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 1 <= k <= ap_calls ap /\ 0 <= rc < 2^31 /\ DST false true ap d so s st LB m /\ DBUD (k - 1) s st LB.

  Definition rat_free_ownedA (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST A0_free (Z_to_bv 64 0x8643c) t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               (Z_to_bv 64 (d_OW d)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ DST false true ap d so s st LB m.

  Definition rat_owned_retA (fl : bool) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x19 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = TST 0x8643c x1 t0 t1 t2 (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_AL d))
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_OW d)) x19 (Z_to_bv 64 0x5e5f50) (Z_to_bv 64 0) (Z_to_bv 64 (Z.b2z fl)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ DST false false ap d so s st LB m.

  Definition rat_free_bufA (sts : Z) (ap : at_parser (ptr:=unit)) (d : dlayA K) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = GST A0_free (Z_to_bv 64 0x86270) t0 t1 t2 (Z_to_bv 64 sts) (Z_to_bv 64 (d_A d))
               (Z_to_bv 64 (d_A d)) a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 (d_L d)) (Z_to_bv 64 (d_A d + 6 + d_L d)) (Z_to_bv 64 (ap_payload_len ap)) (Z_to_bv 64 (d_sc d)) t3 t4 t5 t6 F fc m
      /\ frm0 fc /\ g = gh FI AI s /\ 0 <= sts < 256
      /\ DLAY_ok ap d /\ MFRAME sp0 argv m (d_mpad d) S7 S6 S5 S4 /\ BASE2s so m /\ CJ1 m
      /\ DBYTES false ap d m /\ DBLOCKS false ap d LB /\ RHEAP_A FI AI s LB m /\ RFAKE FI st m
      /\ (exists errv : word, rw_cells asegs m RERRNOA [C4 errv])
      /\ stk asegs m (usp0 - 8388608) (usp0 + -128).

  Definition rat_main_retA (sts : Z) (so : stdout_st) (ms : machine_state) (g : gst) : Prop :=
    exists (x1 t0 t1 t2 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) (mpad : list byte)
           (s : aps FI AI) (st : fsstate FI) (LB : BL),
      ms = GST 0x86270 x1 t0 t1 t2 (Z_to_bv 64 sts) x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 t3 t4 t5 t6 F fc m
      /\ g = gh FI AI s /\ 0 <= sts < 256
      /\ MFRAME sp0 argv m mpad S7 S6 S5 S4 /\ BASE2s so m /\ RHEAP_A FI AI s LB m /\ RFAKE FI st m
      /\ stk asegs m (usp0 - 8388608) (usp0 + -128).

  #[using="VSP"] Lemma valid_sp_facts : 0x7fff80000000 <= usp0 <= 0x800000000000 /\ usp0 mod 16 = 0.
  Proof. destruct VSP as (A & B & C). unfold sp_window_lo, sp_window_hi in *. lia. Qed.

  #[using="Type"] Lemma DBYTES_drop : forall ap d m, DBYTES true ap d m -> DBYTES false ap d m.
  Proof. intros ap d m [B1 _]. split; [exact B1| intros X; discriminate X]. Qed.
  #[using="Type"] Lemma DBLOCKS_drop : forall ap d LB, DBLOCKS true ap d LB -> DBLOCKS false ap d LB.
  Proof. intros ap d LB [B1 _]. split; [exact B1| intros X; discriminate X]. Qed.
  #[using="Type"] Lemma DBLOCKS_mono : forall own ap d LB LB', DBLOCKS own ap d LB -> (forall b, In b LB -> In b LB') -> DBLOCKS own ap d LB'.
  Proof.
    intros own ap d LB LB' [B1 B2] HI. split; [apply HI; exact B1|]. intros Ho. specialize (B2 Ho).
    destruct (ap_owned ap); [apply HI; exact B2| exact I].
  Qed.

  #[using="Type"] Lemma DBYTES_agree : forall (P : Z -> Prop) own ap d m m',
    gagree_on P m m' -> DLAY_ok ap d ->
    (forall a, d_A d <= a < d_A d + d_cap d -> P a) ->
    (own = true -> forall a, d_AL d <= a < d_AL d + ap_payload_len ap -> P a) ->
    DBYTES own ap d m -> DBYTES own ap d m'.
  Proof.
    intros P own ap d m m' AG OK HP HP2 [B1 B2]. pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN). split.
    - eapply rw_cells_gagree; [exact AG| exact B1|]. intros a Ha. apply HP. cbn [cells_size csize Nat.add] in Ha. lia.
    - intros Ho. specialize (B2 Ho). specialize (HP2 Ho). destruct (ap_owned ap) as [p|]; [| exact I].
      destruct OWN as (PL & _ & BR2).
      eapply rw_cells_gagree; [exact AG| exact B2|]. intros a Ha. apply HP2. cbn [cells_size csize Nat.add] in Ha. lia.
  Qed.

  #[using="AMS VSP CEIL ESF"] Lemma base_addr_pclient : forall LB q a, q <= usp0 + -128 -> base_addr sp0 argv envp uid hw rnd a -> pclient FI AI LB q a.
  Proof.
    pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. pose proof alloc_ceiling_bounds as CB'.
    intros LB q a HQ Ha. unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band in Ha. unfold LO in *.
    Ltac bandp AMS l h := right; left; exists l, h; split; [apply AMS; unfold a0_static; split; [lia|]; lia | split; [lia | unfold A0_ERRNO; lia]].
    repeat match type of Ha with _ \/ _ => destruct Ha as [Ha|Ha] end.
    all: try (left; lia).
    all: try (bandp AMS 0x10000 0xabde8). all: try (bandp AMS 0xae6c0 0xaedc0). all: try (bandp AMS 0x5e5f80 0x5e5fa0). all: try (bandp AMS 0x5e5fc0 0x5e6060).
    all: try (bandp AMS 0x5e68c8 0x5e68d0). all: try (bandp AMS 0x6069b0 0x6069b8). all: try (bandp AMS 0x6069c0 0x606be0). all: try (bandp AMS 0x1457a0 0x1457a1). all: try (bandp AMS 0x606be0 0x606be4).
    all: try (bandp AMS 0x606c00 0x606c08). all: try (bandp AMS 0x606fc0 0x607480). all: try (bandp AMS 0x7fffa000 0x800b9200).
    right; left. exists (sh alloc_ceiling - sh alloc_ceiling mod 8), 0x10007fff8000. unfold SH_HI in Ha. split; [| split; [lia| unfold A0_ERRNO, sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia]].
    apply AMS. exact a0_static_s6.
  Qed.

  #[using="Type"] Lemma pkeep_rw_cells : forall LB q m m' A cs,
    pkeep FI AI LB q m m' -> rw_cells asegs m A cs -> (forall a, A <= a < A + Z.of_nat (cells_size cs) -> pclient FI AI LB q a) -> rw_cells asegs m' A cs.
  Proof. intros LB q m m' A cs HP HCs HR. eapply rw_cells_gagree; [exact (pkeep_agree FI AI _ _ _ _ HP)| exact HCs| exact HR]. Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_A_pkeep : forall so q LB m m', LO sp0 <= q <= usp0 + -128 ->
    BASEs so m -> pkeep FI AI LB q m m' -> mem_inv asegs m' -> stk asegs m' (LO sp0) q -> asan_env asegs m' -> BASEs so m'.
  Proof.
    intros so q LB m m' HQ BA HP MI' ST' ENV'. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    pose proof (pkeep_agree FI AI _ _ _ _ HP) as AG.
    eapply (BASE_A_agree0 PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT so); [exact BA| exact AG| intros a Ha; apply base_addr_pclient; [lia| exact Ha]| exact MI'| | | exact ENV'].
    - destruct BA as (ST & _). assert (HQ' : usp0 - 8388608 <= q <= usp0 + -128) by lia. unfold LO in ST. destruct (stk_split asegs m _ q _ ST HQ') as [_ STq].
      eapply stk_merge; [exact ST'| | unfold LO; lia]. eapply stk_gagree; [exact AG| exact STq| intros a Ha; left; lia].
    - destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
      eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA, A0_ERRNO in *; lia].
  Qed.

  #[using="Type"] Lemma EXITC2_incb : forall m m', EXITC2 TID m -> gagree_on exitc_addr m m' ->
    rw_cells asegs m' 0x5e5f54 [C1 (Z_to_bv 8 0)] -> EXITC2 TID m'.
  Proof.
    intros m m' (A1 & A2 & (p3 & p4 & A3) & A3b & A3c & (cdt & thr & sec & tm1 & A4) & A5 & A6 & A8 & (dso & A9) & A10 & A11 & A12 & A13 & _) AG CB.
    Ltac trx AG A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; unfold exitc_addr; cbn in Ha; lia].
    unfold EXITC2.
    split; [trx AG A1|]. split; [trx AG A2|]. split; [exists p3, p4; trx AG A3|]. split; [trx AG A3b|]. split; [trx AG A3c|].
    split; [exists cdt, thr, sec, tm1; trx AG A4|].
    split; [trx AG A5|]. split; [trx AG A6|]. split; [trx AG A8|].
    split; [exists dso; trx AG A9|]. split; [trx AG A10|]. split; [trx AG A11|]. split; [trx AG A12|]. split; [trx AG A13| exact CB].
  Qed.

  #[using="Type"] Lemma EXCB_exitc : forall cb m, EXCB cb m -> exists m0, EXITC2 TID m0 /\ gagree_on exitc_addr m0 m.
  Proof.
    intros [] m H; cbv beta iota delta [EXCB] in H; [exact (proj1 H)|].
    exists m. split; [exact H| apply gagree_on_refl].
  Qed.

  #[using="Type"] Lemma BASE_cb_A2 : forall so m, BASE_cb false so m <-> BASE2s so m.
  Proof. intros so m. split; intros H; exact H. Qed.

  #[using="Type"] Lemma BASE_cb_cell : forall cb so m, BASE_cb cb so m -> rw_cells asegs m 0x5e5f54 [C1 (Z_to_bv 8 (Z.b2z cb))].
  Proof.
    intros [] so m (_ & _ & EX & _); cbv beta iota delta [EXCB] in EX.
    - exact (proj2 EX).
    - destruct EX as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & CB). exact CB.
  Qed.

  #[using="PZ_agree VSP CEIL ESF HT"] Lemma BASE_cb_agree0 : forall cb cb' (P : Z -> Prop) so m m',
    BASE_cb cb so m -> gagree_on P m m' -> (forall a, base_addr sp0 argv envp uid hw rnd a -> P a) ->
    mem_inv asegs m' -> stk asegs m' (LO sp0) (usp0 + -128) -> stk asegs m' RSVA (RSVA + 65536) -> asan_env asegs m' ->
    rw_cells asegs m' 0x5e5f54 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> BASE_cb cb' so m'.
  Proof.
    intros cb cb' P so m m' (ST & MI & EX & MC & IMG & SE & SOF0 & RSS & SI & SZ & ENV & GSH & HPZ & CRT) AG HP MI' ST' RSS' ENV' CB'.
    pose proof (sp_facts sp0 VSP CEIL) as SF. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL. pose proof alloc_ceiling_bounds as CB0. unfold LO in *.
    destruct (EXCB_exitc cb m EX) as (m0 & EX0 & AG0).
    assert (AGX : gagree_on exitc_addr m0 m').
    { eapply gagree_on_trans; [exact AG0|]. eapply gagree_on_mono; [exact AG|]. intros a Ha. apply HP. left. exact Ha. }
    split; [exact ST'|]. split; [exact MI'|].
    split. { destruct cb'; cbv beta iota delta [EXCB].
             - split; [exists m0; split; [exact EX0| exact AGX]| exact CB'].
             - eapply EXITC2_incb; [exact EX0| exact AGX| exact CB']. }
    split. { destruct MC as (A1 & A2 & [G1 G2]). unfold MAINC0, ssp_cells, got_ssp, ssp_guard in *.
             Ltac trcb AG HP A := eapply rw_cells_gagree; [exact AG| exact A| intros a Ha; apply HP; unfold base_addr; cbn in Ha; lia].
             split; [trcb AG HP A1|]. split; [trcb AG HP A2|]. split; [trcb AG HP G1| trcb AG HP G2]. }
    split; [eapply IMGK_agree; [exact AG| exact IMG| intros a Ha; apply HP; unfold base_addr; lia]|].
    split; [eapply stderr_wfile0_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SE]|].
    split; [eapply stdout_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SOF0]|].
    split; [exact RSS'|].
    split; [eapply stdin_file_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact SI]|].
    split.
    { destruct SZ as ([Z1 R1] & [Z2 R2] & [Z3 R3] & [Z4 R4]).
      repeat split; (first [ eapply shz_agree; [exact AG| | | | eassumption] | eapply shr_agree; [exact AG| | | | eassumption] ]);
        unfold sh, SHADOW_OFF, SH_HI;
        first [ intros a Ha; apply HP; unfold base_addr, pz_band, sh, SHADOW_OFF, SH_HI; Z.div_mod_to_equations; lia
              | Z.div_mod_to_equations; lia ]. }
    split; [exact ENV'|].
    split; [eapply globals_shadow_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; lia| exact GSH]|].
    split; [eapply PZ_agree; [exact AG| intros a Ha; apply HP; unfold base_addr; tauto| exact HPZ]|].
    apply wr_at_crt.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma BASE_cb_pkeep : forall cb so q LB m m', LO sp0 <= q <= usp0 + -128 ->
    BASE_cb cb so m -> pkeep FI AI LB q m m' -> mem_inv asegs m' -> stk asegs m' (LO sp0) q -> asan_env asegs m' -> BASE_cb cb so m'.
  Proof.
    intros cb so q LB m m' HQ BA HP MI' ST' ENV'. pose proof (sp_facts sp0 VSP CEIL) as SF. unfold LO in *.
    pose proof (pkeep_agree FI AI _ _ _ _ HP) as AG.
    eapply (BASE_cb_agree0 cb cb); [exact BA| exact AG| intros a Ha; apply base_addr_pclient; [lia| exact Ha]| exact MI'| | | exact ENV'| ].
    - destruct BA as (ST & _). assert (HQ' : usp0 - 8388608 <= q <= usp0 + -128) by lia. unfold LO in ST. destruct (stk_split asegs m _ q _ ST HQ') as [_ STq].
      eapply stk_merge; [exact ST'| | unfold LO; lia]. eapply stk_gagree; [exact AG| exact STq| intros a Ha; left; lia].
    - destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _).
      eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| unfold RSVA, A0_ERRNO in *; lia].
    - eapply pkeep_rw_cells; [exact HP| exact (BASE_cb_cell cb so m BA)|].
      intros a Ha. right; left. exists 0x5d5f40, 0x5e5f80. split; [apply AMS; unfold a0_static; lia| cbn in Ha; unfold A0_ERRNO; lia].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma DMEM_pkeep : forall cb ap d so LB m m',
    DMEM cb ap d so m -> pkeep FI AI LB (usp0 + -208) m m' -> mem_inv asegs m' -> stk asegs m' (LO sp0) (usp0 + -208) -> asan_env asegs m' ->
    DMEM cb ap d so m'.
  Proof.
    intros cb ap d so LB m m' (TF & FR & BA & CJ) HP MI' ST' ENV'. pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'.
    split. { unfold TRFRAME in *. eapply pkeep_rw_cells; [exact HP| exact TF| intros a Ha; left; cbn in Ha; lia]. }
    split. { unfold MFRAME in *. eapply pkeep_rw_cells; [exact HP| exact FR| intros a Ha; left; cbn in Ha; lia]. }
    split. { eapply (BASE_cb_pkeep cb so (usp0 + -208)); [unfold LO; lia| exact BA| exact HP| exact MI'| exact ST'| exact ENV']. }
    destruct CJ as [X1 X2]. split; (eapply pkeep_rw_cells; [exact HP| eassumption| intros a Ha; right; left; exists 0x5d5f40, 0x5e5f80; split; [apply AMS; unfold a0_static; lia| cbn in Ha; unfold A0_ERRNO; lia]]).
  Qed.

  #[using="Type"] Lemma DBYTES_pkeep : forall own ap d LB m m',
    DLAY_ok ap d -> DBLOCKS own ap d LB -> DBYTES own ap d m -> pkeep FI AI LB (usp0 + -208) m m' -> DBYTES own ap d m'.
  Proof.
    intros own ap d LB m m' OK [BL1 BL2] [B1 B2] HP.
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN). split.
    - eapply pkeep_rw_cells; [exact HP| exact B1|]. intros a Ha. right; right; left. exists (d_kb d, d_A d, d_cap d). split; [exact BL1|]. cbn -[Z.of_nat Z.add] in Ha |- *. simpl_sizes. cbn. lia.
    - intros Ho. specialize (B2 Ho). specialize (BL2 Ho). destruct (ap_owned ap) as [p|]; [| exact I]. destruct OWN as (PL & _ & BR2 & _).
      eapply pkeep_rw_cells; [exact HP| exact B2|]. intros a Ha. right; right; left. exists (d_kp d, d_AL d, ap_payload_len ap). split; [exact BL2|]. cbn -[Z.of_nat Z.add] in Ha |- *. simpl_sizes. cbn. lia.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma DMEM_alloc : forall ap d so LB st m m',
    DMEM false ap d so m -> alloc_frame_A FI AI (usp0 + -208) (LO sp0) st m m' LB -> DMEM false ap d so m'.
  Proof.
    intros ap d so LB st m m' (TF & FR & BA & CJ) AFR. pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'.
    pose proof AFR as (MI' & ST' & ENV' & RF' & AP).
    split. { unfold TRFRAME in *. eapply (apres_rw_cells FI AI); [exact AP| exact TF| apply aclient_range_above; lia]. }
    split. { unfold MFRAME in *. eapply (apres_rw_cells FI AI); [exact AP| exact FR| apply aclient_range_above; lia]. }
    split. { apply BASE_cb_A2. eapply (BASE_A2_alloc_q FI AI AMS PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF HT so (usp0 + -208)); [unfold LO; lia| apply BASE_cb_A2; exact BA| exact AFR]. }
    destruct CJ as [X1 X2]. split; (eapply (apres_rw_cells FI AI); [exact AP| eassumption| eapply (aclient_range_static FI AI _ _ _ _ 0x5d5f40 0x5e5f80); [apply AMS; unfold a0_static; lia| cbn; lia| cbn; lia]]).
  Qed.

  #[using="Type"] Lemma DBYTES_alloc : forall own ap d LB st m m',
    DLAY_ok ap d -> DBLOCKS own ap d LB -> DBYTES own ap d m -> alloc_frame_A FI AI (usp0 + -208) (LO sp0) st m m' LB -> DBYTES own ap d m'.
  Proof.
    intros own ap d LB st m m' OK [BL1 BL2] [B1 B2] (MI' & ST' & ENV' & RF' & AP).
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN). split.
    - eapply (apres_rw_cells FI AI); [exact AP| exact B1|]. eapply aclient_range_block; [exact BL1| cbn; lia| cbn -[Z.of_nat Z.add]; simpl_sizes; lia].
    - intros Ho. specialize (B2 Ho). specialize (BL2 Ho). destruct (ap_owned ap) as [p|]; [| exact I]. destruct OWN as (PL & _ & BR2).
      eapply (apres_rw_cells FI AI); [exact AP| exact B2|]. eapply aclient_range_block; [exact BL2| cbn; lia| cbn -[Z.of_nat Z.add]; simpl_sizes; lia].
  Qed.

  #[using="PZ_agree VSP CEIL ESF"] Lemma DMEM_emit : forall ap d so so' m m',
    DMEM false ap d so m -> munch [(usp0 - 8388608, usp0 + -208); (0xaebb8, 0xaebb8 + 232); (0x607080, 0x607080 + 1024)] m m' -> wmono asegs m m' ->
    mem_inv asegs m' -> stk asegs m' (usp0 - 8388608) (usp0 + -208) -> asan_env asegs m' -> stdout_file m' so' ->
    DMEM false ap d so' m'.
  Proof.
    intros ap d so so' m m' (TF & FR & BA & CJ) MU WM MI' ST' ENV' SOF'. pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'.
    pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, ((a < usp0 - 8388608 \/ usp0 - 208 <= a) /\ ~ (0xaebb8 <= a < 0xaebb8 + 232) /\ ~ (0x607080 <= a < 0x607080 + 1024)) ->
                            (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -208); (0xaebb8, 0xaebb8 + 232); (0x607080, 0x607080 + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    split. { unfold TRFRAME in *. eapply rw_cells_gagree; [exact AG| exact TF|]. intros a Ha. apply OUT. cbn in Ha. lia. }
    split. { unfold MFRAME in *. eapply rw_cells_gagree; [exact AG| exact FR|]. intros a Ha. apply OUT. cbn in Ha. lia. }
    split.
    { apply BASE_cb_A2. apply BASE_cb_A2 in BA.
      eapply (BASE_A2_agree_so PZ PZ_agree sp0 argv envp uid hw rnd TID VSP CEIL ESF); [exact BA| exact AG| | exact WM| exact MI'| | | exact ENV'| exact SOF'].
      - intros a Ha Hs. apply OUT. unfold base_addr2, base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band, sh, SHADOW_OFF, SH_HI in *.
        clear -Ha Hs SF IL47 CB'. Z.div_mod_to_equations. lia.
      - destruct BA as (ST & _). unfold LO in ST. destruct (stk_split asegs m _ (usp0 + -208) _ ST ltac:(lia)) as [_ SThi].
        eapply stk_merge; [exact ST'| | unfold LO; lia]. eapply stk_gagree; [exact AG| exact SThi| intros a Ha; apply OUT; lia].
      - destruct BA as (_ & _ & _ & _ & _ & _ & _ & RSS & _). eapply stk_gagree; [exact AG| exact RSS| intros a Ha; apply OUT; unfold RSVA in Ha; lia]. }
    destruct CJ as [X1 X2]. split; (eapply rw_cells_gagree; [exact AG| eassumption| intros a Ha; apply OUT; cbn in Ha; lia]).
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma DMEM_cb : forall cb cb' ap d so m m',
    munch [(0x5e5f54, 0x5e5f55)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' 0x5e5f54 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> DMEM cb ap d so m -> DMEM cb' ap d so m'.
  Proof.
    intros cb cb' ap d so m m' MU WM MI' CB (TF & FR & BA & CJ). pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'.
    pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < 0x5e5f54 \/ 0x5e5f55 <= a) -> (fun a0 : Z => outside [(0x5e5f54, 0x5e5f55)] a0) a).
    { intros a Ha. cbn. lia. }
    split. { unfold TRFRAME in *. eapply rw_cells_gagree; [exact AG| exact TF|]. intros a Ha. apply OUT. cbn in Ha. lia. }
    split. { unfold MFRAME in *. eapply rw_cells_gagree; [exact AG| exact FR|]. intros a Ha. apply OUT. cbn in Ha. lia. }
    split.
    { pose proof BA as (ST & _ & _ & _ & _ & _ & _ & RSS & _ & _ & ENV & _).
      eapply (BASE_cb_agree0 cb cb'); [exact BA| exact AG| | exact MI'| | | | exact CB].
      - intros a Ha. apply OUT. unfold base_addr, exitc_addr, stdout_addr, stderr_addr, stdin_addr, pz_band, sh, SHADOW_OFF, SH_HI in *.
        clear -Ha SF IL47 CB'. Z.div_mod_to_equations. lia.
      - eapply stk_gagree; [exact AG| exact ST|]. intros a Ha. apply OUT. unfold LO in Ha. lia.
      - eapply stk_gagree; [exact AG| exact RSS|]. intros a Ha. apply OUT. unfold RSVA in Ha. lia.
      - eapply asan_env_frame; [exact ENV| exact MU| exact WM| env_safe_tac]. }
    destruct CJ as [X1 X2]. split; (eapply rw_cells_gagree; [exact AG| eassumption| intros a Ha; apply OUT; cbn in Ha; lia]).
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma DST_cb : forall cb cb' own ap d so s st LB m m',
    munch [(0x5e5f54, 0x5e5f55)] m m' -> wmono asegs m m' -> mem_inv asegs m' ->
    rw_cells asegs m' 0x5e5f54 [C1 (Z_to_bv 8 (Z.b2z cb'))] -> DST cb own ap d so s st LB m -> DST cb' own ap d so s st LB m'.
  Proof.
    intros cb cb' own ap d so s st LB m m' MU WM MI' CB (OK & DM & DB & DBL & HP & RF & [errv ERR] & ST).
    pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof alloc_ceiling_bounds as CB'.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
    assert (OUT : forall a, (a < 0x5e5f54 \/ 0x5e5f55 <= a) -> (fun a0 : Z => outside [(0x5e5f54, 0x5e5f55)] a0) a).
    { intros a Ha. cbn. lia. }
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN).
    split; [exact OK|].
    split; [eapply DMEM_cb; [exact MU| exact WM| exact MI'| exact CB| exact DM]|].
    split. { eapply (DBYTES_agree _ own ap d m m' AG OK); [| | exact DB].
             - intros a Ha. apply OUT. lia.
             - intros _ a Ha. apply OUT. destruct (ap_owned ap) as [p|]; [| destruct OWN as (PL0 & _); lia]. destruct OWN as (_ & _ & Q). lia. }
    split; [exact DBL|].
    split. { eapply (am_heap_frame FI AI); [exact HP| exact MU| exact WM|].
             repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd].
             right; left; exists 0x5d5f40, 0x5e5f80; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia]. }
    split. { pose proof (fsb_ok FI) as FB. unfold app_mem in FB. eapply (rfake_frame FI); [exact RF| exact MU| exact WM|].
             repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    split. { exists errv. eapply rw_cells_gagree; [exact AG| exact ERR|]. intros a Ha. apply OUT. cbn in Ha. unfold RERRNOA in Ha. lia. }
    eapply stk_gagree; [exact AG| exact ST|]. intros a Ha. apply OUT. lia.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma head_to_callA : forall k fl ap d so ms g, rat_headA k fl ap d so ms g ->
    evt asegs (fun ms' => rat_callA k fl ap d so ms' g) ms.
  Proof.
    intros k fl ap d so ms g (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & HK & SM & DBU).
    pose proof SM as (_ & (_ & _ & BA & _) & _).
    pose proof (BASE_cb_cell false so m BA) as CB. change (Z_to_bv 8 (Z.b2z false)) with (Z_to_bv 8 0) in CB.
    pose proof BA as (_ & MI & _).
    pose proof (munch_refl [(0x5e5f54, 0x5e5f55)] m) as MU. pose proof (wmono_refl asegs m) as WM.
    zstep. zst. zstep. zstep. zstep.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) =>
      apply evt_done; unfold rat_callA; do 16 eexists; exists mx, s, st, LB end.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact Eg|]. split; [exact HK|]. split; [| exact DBU].
    eapply DST_cb; [exact MU| exact WM| exact MI| exact CB| exact SM].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma rat_parser_callA : forall ap so ms g, rat_parserA FI AI PZ sp0 argv envp uid hw rnd TID S4 S5 S6 S7 S8 S9 S10 S11 ap so ms g ->
    exists d, evt asegs (fun ms' => rat_callA (ap_calls ap) false ap d so ms' g) ms /\ so = stdout_init.
  Proof.
    intros ap so ms g (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & mm & A & cap & L & sc & AL & OW & DATA & junk & mpad & pad & errv & LB & s & st & kb
                       & -> & FRM & -> & Eg & HC0 & HL & HCNT & HK & LEN & CAPM & LR & SCR & BR & OWN & HP & RF & FSL & NSR & BLK & BSH & TFR & FR & ST & BA & ERR & CJ).
    assert (KP : exists kp : K, match ap_owned ap with
                                | None => ap_payload_len ap = 0 /\ AL = EMPTY_OBJ_A /\ OW = 0 /\ LB = [(kb, A, cap)]
                                | Some _ => 0 < ap_payload_len ap /\ OW = AL /\ LB = [(kp, AL, ap_payload_len ap); (kb, A, cap)]
                                            /\ rw_cells asegs mm AL [CB (Z.to_nat (ap_payload_len ap)) (skipn (Z.to_nat (6 + L)) DATA)]
                                            /\ rw_cells asegs mm (sh AL) (shadow_cells (block_shadow (ap_payload_len ap))) end).
    { destruct (ap_owned ap); [destruct OWN as [kp OWN']; exists kp; exact OWN'| exists kb; exact OWN]. }
    clear OWN. destruct KP as [kp OWN].
    exists (mkDL K A cap L sc AL OW DATA junk mpad pad kb kp). split; [| reflexivity].
    apply head_to_callA.
    exists x1, t0, t1, t2, a0, a1, a2, a3, a4, a5, a6, a7, (Z_to_bv 64 (A + 2)), t3, t4, t5, t6, F, fc, mm, s, st, LB.
    split; [reflexivity|]. split; [exact FRM|]. split; [exact Eg|]. split; [lia|].
    split; [|
      unfold DBUD; split; [| split; [| split; [exact FSL| exact NSR]]];
      (destruct (ap_owned ap); [destruct OWN as (Q1 & Q2 & -> & _)| destruct OWN as (Q1 & Q2 & Q3 & ->)]);
      unfold lb_bytes, ap_payload_len, HDR_MIN, zlength in *; rewrite ?HC0, ?length_map in *; cbn; lia ].
    split. { unfold DLAY_ok. cbn. repeat (split; [first [assumption| lia]|]).
             destruct (ap_owned ap); [destruct OWN as (Q1 & Q2 & Q3 & Q4 & Q5)| destruct OWN as (Q1 & Q2 & Q3 & Q4); repeat split; assumption].
             pose proof (am_block_range FI AI _ _ _ (kp, AL, ap_payload_len ap) HP ltac:(rewrite Q3; left; reflexivity)) as R; cbn in R.
             split; [exact Q1|]. split; [exact Q2|]. split.
             { split; [lia|]. split; [lia|]. split; [lia|]. apply win_ok_of_range; lia. }
             intros E. pose proof (am_blocks_nodup FI AI _ _ _ HP) as ND. rewrite Q3, E in ND. cbn in ND. inversion ND as [|x l NI ND']; subst. apply NI. constructor. }
    split. { unfold DMEM. cbn [d_A d_cap d_L d_sc d_AL d_OW d_DATA d_junk d_mpad d_pad d_kb d_kp].
             split; [exact TFR|]. split; [exact FR|]. split; [apply BASE_cb_A2; exact BA| exact CJ]. }
    split. { unfold DBYTES. cbn. split; [exact BLK|]. intros _. destruct (ap_owned ap); [destruct OWN as (Q1 & Q2 & Q3 & Q4 & Q5); exact Q4| exact I]. }
    split. { unfold DBLOCKS. cbn. destruct (ap_owned ap).
             - destruct OWN as (Q1 & Q2 & -> & Q4 & Q5). split; [right; left; reflexivity| intros _; left; reflexivity].
             - destruct OWN as (Q1 & Q2 & Q3 & ->). split; [left; reflexivity| intros _; exact I]. }
    split; [exact HP|]. split; [exact RF|]. split; [exists errv; exact ERR| exact ST].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma ret_to_emitA : forall k rc fl ap d so ms g, rat_retA k rc fl ap d so ms g -> evt asegs (fun ms' => rat_emitA k rc fl ap d so ms' g) ms.
  Proof.
    intros k rc fl ap d so ms g (x1 & t0 & t1 & t2 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & HK & HRC & SM).
    destruct SM as [SM DBU]. pose proof SM as (_ & (_ & _ & BA & _) & _). pose proof BA as (_ & MI & _).
    eapply (post_to_emit sp0); [exact (BASE_cb_cell true so m BA)| exact MI|].
    intros m' MU WM MI' CB. apply evt_done. unfold rat_emitA. do 15 eexists. exists m', s, st, LB. split; [reflexivity|].
    split; [exact FRM|]. split; [exact Eg|]. split; [exact HK|]. split; [exact HRC|]. split; [| exact DBU].
    eapply DST_cb; [exact MU| exact WM| exact MI'| exact CB| exact SM].
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF EMIT"] Lemma emit_stepA : forall k fl ap d so ms g, rat_emitA k 0 fl ap d so ms g ->
    implM asegs (stdout_vprintf aget_so aset_so pieces_emit) so (fun _ so' ms' => rat_emit_retA k 0 fl ap d so' ms' g) ms.
  Proof.
    intros k fl ap d so ms g (t0 & t1 & t2 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & HK & HRC & SM).
    pose proof valid_sp_facts as SF. pose proof (sp_facts sp0 VSP CEIL) as SF'. pose proof (IMGB_len47 sp0 argv envp uid hw rnd ESF) as IL47. pose proof alloc_ceiling_bounds as CB'.
    destruct SM as ((OK & DM & DB & DBL & HP & RF & [errv ERR] & ST) & DBU).
    pose proof DM as (TF & FR & BA & CJ).
    pose proof BA as (STm & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). destruct MC as (G28 & GSE & SSP).
    eapply implM_mono.
    { eapply EMIT with (lo := usp0 - 8388608) (canary := guard_word); rewrite ?unsigned_lit by lia;
        first [ exact SOF | reflexivity | exact ST | unfold EMIT_DEPTH; lia | unfold GLOBALS_TOP; lia | lia | exact SSP | exact MI | exact FRM | exact ENV
              | clear -SF; Z.div_mod_to_equations; lia
              | unfold RO_LO, RO_SZ; apply (SHZ_ro sp0 argv envp uid hw rnd); exact SZ
              | apply (SHZ_stdout_buf sp0 argv envp uid hw rnd); exact SZ
              | apply (SHZ_stack sp0 argv envp uid hw rnd); [exact SZ | lia | lia | lia | lia] ]. }
    cbv beta. intros [] so' ms' PO.
    destruct PO as (u0 & u1 & u2 & b0 & b1 & b2 & b3 & b4 & b5 & b6 & b7 & u3 & u4 & u5 & u6 & Ft & fc' & m' & -> & MU & WM & MI' & FRM' & FEQ & ST' & SOF' & SSP' & ENV').
    rewrite !unsigned_lit in MU by lia. rewrite !unsigned_lit in ST' by lia.
    pose proof (gagree_on_of_munch _ _ _ MU WM) as AG.
    pose proof OK as (_ & _ & _ & _ & LEN & _ & _ & _ & BR & OWN).
    assert (OUT : forall a, ((a < usp0 - 8388608 \/ usp0 - 208 <= a) /\ ~ (0xaebb8 <= a < 0xaebb8 + 232) /\ ~ (0x607080 <= a < 0x607080 + 1024)) ->
                            (fun a0 : Z => outside [(usp0 - 8388608, usp0 + -208); (0xaebb8, 0xaebb8 + 232); (0x607080, 0x607080 + 1024)] a0) a).
    { intros a Ha. cbn. lia. }
    unfold rat_emit_retA. do 18 eexists. exists m', s, st, LB.
    split; [replace (ret_pc (Z_to_bv 64 0x86420)) with (Z_to_bv 64 0x86420) by (symmetry; rpc); reflexivity|].
    split; [exact FRM'|]. split; [exact Eg|]. split; [exact HK|]. split; [exact HRC|].
    split; [| exact DBU].
    split; [exact OK|].
    split; [eapply DMEM_emit; [exact DM| exact MU| exact WM| exact MI'| exact ST'| exact ENV'| exact SOF']|].
    split. { eapply (DBYTES_agree _ true ap d m m' AG OK); [| | exact DB].
             - intros a Ha. apply OUT. lia.
             - intros _ a Ha. apply OUT. destruct (ap_owned ap) as [p|]; [| destruct OWN as (PL0 & _); lia]. destruct OWN as (_ & _ & Q). lia. }
    split; [exact DBL|].
    split. { eapply (am_heap_frame FI AI); [exact HP| exact MU| exact WM|].
             repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd];
               first [ left; lia
                     | right; left; exists 0xae6c0, 0xaedc0; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia]
                     | right; left; exists 0x606fc0, 0x607480; split; [apply AMS; unfold a0_static; lia| unfold a0_wsafe; lia] ]. }
    split. { pose proof (fsb_ok FI) as FB. unfold app_mem in FB. eapply (rfake_frame FI); [exact RF| exact MU| exact WM|].
             repeat apply Forall_cons; try apply Forall_nil; cbn [fst snd]; left; unfold sh, SHADOW_OFF in *; Z.div_mod_to_equations; lia. }
    split. { exists errv. eapply rw_cells_gagree; [exact AG| exact ERR|]. intros a Ha. apply OUT. cbn in Ha. unfold RERRNOA in Ha. lia. }
    exact ST'.
  Qed.

  #[using="AMS PZ_agree VSP CEIL ESF HT"] Lemma emit_ret_callA : forall k rc fl ap d so ms g, rat_emit_retA k rc fl ap d so ms g -> 1 < k ->
    evt asegs (fun ms' => rat_callA (k - 1) (fl || (0 <? rc)) ap d so ms' g) ms.
  Proof.
    intros k rc fl ap d so ms g (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & HK & HRC & SM) H1.
    pose proof SM as (((_ & _ & _ & HC4 & _) & _) & _).
    eapply (emit_ret_next sp0 S8 S9 S10 S11 _ k rc fl); [lia| exact HRC| | intros X; exfalso; lia].
    intros _. apply (head_to_callA (k - 1) (fl || (0 <? rc)) ap d so _ g).
    unfold rat_headA. do 19 eexists. exists m, s, st, LB. split; [reflexivity|]. split; [exact FRM|]. split; [exact Eg|]. split; [lia| exact SM].
  Qed.

  #[using="Type"] Lemma emit_ret_freeA : forall k rc fl ap d so ms g, rat_emit_retA k rc fl ap d so ms g -> k = 1 ->
    evt asegs (fun ms' => rat_free_ownedA (fl || (0 <? rc)) ap d so ms' g) ms.
  Proof.
    intros k rc fl ap d so ms g (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & HK & HRC & SM) H1.
    eapply (emit_ret_next sp0 S8 S9 S10 S11 _ k rc fl); [lia| exact HRC| intros X; exfalso; lia|].
    intros _. apply evt_done. unfold rat_free_ownedA, A0_free. do 17 eexists. exists m, s, st, LB. split; [reflexivity|]. split; [exact FRM|]. split; [exact Eg| exact (proj1 SM)].
  Qed.

  #[using="VSP"] Lemma owned_ret_to_free_bufA : forall fl ap d so ms g, rat_owned_retA fl ap d so ms g ->
    evt asegs (fun ms' => rat_free_bufA (drv_status d fl) ap d so ms' g) ms.
  Proof.
    intros fl ap d so ms g (x1 & t0 & t1 & t2 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x19 & t3 & t4 & t5 & t6 & F & fc & m & s & st & LB & -> & FRM & Eg & SM).
    pose proof valid_sp_facts as SF.
    destruct SM as (OK & DM & DB & DBL & HP & RF & ERR & ST). pose proof OK as (_ & _ & _ & _ & _ & _ & _ & SCR & _).
    destruct DM as (TF & FR & BA & CJ). apply BASE_cb_A2 in BA.
    eapply (free_ret_to_main sp0 S8 S9 S10 S11 VSP _ fl (d_sc d) (ap_payload_len ap) (d_A d) (d_L d) (d_pad d));
      [exact TF| exact ST| lia| exact SCR|].
    intros a1' ST'. apply evt_done. unfold rat_free_bufA, A0_free. do 16 eexists. exists m, s, st, LB. split; [reflexivity|]. split; [exact FRM|]. split; [exact Eg|].
    split; [unfold drv_status; destruct (d_sc d <? 0); [cbn; lia| destruct fl; cbn; lia]|].
    repeat (split; [assumption|]). exact ST'.
  Qed.

  #[using="VSP CEIL"] Lemma main_ret_exitA : forall sts so ms g, rat_main_retA sts so ms g ->
    evt asegs (rat_exitA TID sts so) ms.
  Proof.
    intros sts so ms g (x1 & t0 & t1 & t2 & x9 & a0 & a1 & a2 & a3 & a4 & a5 & a6 & a7 & x18 & x19 & x20 & x21 & t3 & t4 & t5 & t6 & F & fc & m & mpad & s & st & LB
                        & -> & Eg & HST & FR & BA & HP & RF & ST).
    pose proof BA as (STm & MI & EX & MC & IMG & SE & SOF & RSS & SI & SZ & ENV & GSH & HPZ & CRT). destruct MC as (G28 & GSE & [GG GU]). unfold got_ssp, ssp_guard in GG, GU.
    eapply (main_return2 sp0 argv TID VSP CEIL sts so);
      [exact FR| exact STm| exact EX| exact CRT| exact ENV| exact GSH| exact GG| exact GU| exact SOF| apply stderr_wfile0_file; exact SE| exact SI| exact MI].
  Qed.
End SEAMS.
