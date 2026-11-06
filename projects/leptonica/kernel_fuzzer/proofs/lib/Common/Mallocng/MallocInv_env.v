(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout Fs State Monad Specs Run.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common Require Import
  PropExec CatExec Hoare StoreOk MmapSim AllocSim ShapeAlg ShapeNodes VmLedger.
From OSSVerify.Proofs.leptonica.kernel_fuzzer.lib.Common.Mallocng Require Import
  MallocLayout MallocTree MallocOps MallocInv_defs MallocInv_heap MallocInv_word MallocInv_w32
  MallocInv_sep MallocInv_tables MallocInv_steps MallocInv_repw.
Import ListNotations.
Local Open Scope Z_scope.
Local Open Scope malloc_scope.

Section WithLayout.
Context {ML : MallocLayout} {MLok : MallocLayoutOk ML} {HT : HeapTop}.

(* [comment removed for export] *)
Definition GOTA : Z := bv_unsigned A_GOT_SSP.
Definition SSPA : Z := bv_unsigned A_SSP.
Definition NLA : Z := bv_unsigned A_NEED_LOCKS.
Definition PGA : Z := bv_unsigned A_PAGE_SIZE.

(* [comment removed for export] *)
Lemma layout_statics :
  GOTA = bv_unsigned A_GOT_SSP /\ SSPA = bv_unsigned A_SSP /\ NLA = bv_unsigned A_NEED_LOCKS /\ PGA = bv_unsigned A_PAGE_SIZE /\
  RW_LO <= GOTA /\ GOTA + 8 <= ERRNO /\ ERRNO + 4 <= SSPA /\ SSPA + 11 <= NLA /\ NLA + 45 = PGA /\ PGA + 8 <= LOCKA /\
  LOCKA + 940 <= IMG_HI /\ IMG_HI <= 2^32 /\ 4096 <= IMG_LO /\ IMG_LO <= RW_LO /\
  0x7fff7f800000 <= alloc_ceiling.
Proof.
  pose proof layout_nums. unfold GOTA, SSPA, NLA, PGA. unfold LOCKA, ERRNO in *.
  pose proof (mlo_order_got (ML:=ML)). pose proof (mlo_order_errno (ML:=ML)). pose proof (mlo_order_tp (ML:=ML)).
  pose proof (mlo_order_ssp (ML:=ML)). pose proof (mlo_order_libc (ML:=ML)).
  pose proof (mlo_need_locks (ML:=ML)). pose proof (mlo_page_size (ML:=ML)).
  repeat split; lia.
Qed.

(* [comment removed for export] *)
Definition static_addr (x : Z) : Prop :=
  (GOTA <= x < GOTA + 8) \/ x = NLA \/ (PGA <= x < PGA + 8) \/ (SSPA <= x < SSPA + 8) \/ (LOCKA <= x < LOCKA + 8).

Record statics_ok (m : word -> option byte) : Prop := {
  so_got  : forall a, GOTA <= a < GOTA + 8 -> m (Z_to_bv 64 a) = None;
  so_nl   : rdn ml_segs m A_NEED_LOCKS 1 = Some [Z_to_bv 8 0];
  so_lock : forall j, 0 <= j < 8 -> m (Z_to_bv 64 (LOCKA + j)) = None
}.

Lemma static_not_wzone : forall w x, wzone w -> f_a w <= x < f_a w + f_n w -> ~ static_addr x.
Proof. intros w x Hz Hx Hs. pose proof layout_statics. unfold wzone, static_addr, CTX, CTX_END in *. lia. Qed.

Lemma statics_frame : forall m m',
  statics_ok m -> (forall a : word, static_addr (bv_unsigned a) -> m' a = m a) -> statics_ok m'.
Proof.
  intros m m' [G N L] Hf. pose proof layout_statics. constructor.
  - intros a Ha. rewrite Hf; [apply G; exact Ha|]. unfold static_addr. rewrite uZ by lia. lia.
  - rewrite <- N. rewrite <- (Z_to_bv_bv_unsigned 64 A_NEED_LOCKS). rewrite !rdn1_eq. rewrite Hf; [reflexivity|].
    unfold static_addr, NLA in *. rewrite uZ by (pose proof (u64_range A_NEED_LOCKS); lia). lia.
  - intros j Hj. rewrite Hf; [apply L; exact Hj|]. unfold static_addr. rewrite uZ by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma repw_statics : forall A m0 ws m, RepW A m0 ws m -> statics_ok m0 -> statics_ok m.
Proof.
  intros A m0 ws m HR HS. apply (statics_frame m0 m HS). intros a Ha.
  apply (rw_frame A m0 ws m HR). unfold wfree. rewrite Forall_forall. intros w Hw.
  pose proof (rw_zone A m0 ws m HR w Hw) as Hz. pose proof layout_statics. unfold wzone, static_addr, CTX, CTX_END in *. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Definition GOT_BYTES : list byte := Z_to_le_bytes 8 SSPA.

Lemma got_image : rdn ml_segs (fun _ => None) (Z_to_bv 64 GOTA) 8 = Some GOT_BYTES.
Proof.
  pose proof layout_statics as L. pose proof (u64_range A_SSP) as RS.
  destruct (rdn_rom_bytes _ _ GOTA 8 (mlo_got_ssp (ML:=ML))) as (bs & Hbs & Hlen & Hnth);
    [unfold GOTA; apply u64_range | lia | cbn [length map Z.of_nat]; unfold GOTA; lia | cbn [length map]; unfold GOTA; lia |].
  unfold GOTA in Hbs |- *. rewrite Hbs. f_equal.
  apply (nth_ext _ _ (Z_to_bv 8 0) (Z_to_bv 8 0)); [unfold GOT_BYTES; rewrite length_Z_to_le_bytes; exact Hlen|].
  intros k Hk. rewrite Hlen in Hk. rewrite Hnth by exact Hk. unfold GOT_BYTES.
  apply bv_eq. rewrite nth_Z_to_le_bytes by (unfold SSPA; lia). unfold byte_of.
  rewrite Z.sub_diag. cbn [Z.to_nat Nat.add]. unfold SSPA.
  rewrite Z_to_bv_unsigned.
  assert (E : forall i : nat, (i < 8)%nat -> nth i (map (fun i0 : Z => (bv_unsigned A_SSP / 2 ^ (8 * i0)) mod 256) [0; 1; 2; 3; 4; 5; 6; 7]) 0
                                        = (bv_unsigned A_SSP / 2 ^ (8 * Z.of_nat i)) mod 256).
  { intros i Hi. do 8 (destruct i as [|i]; [reflexivity|]). lia. }
  rewrite E by lia. replace (Z.to_nat 0 + k)%nat with k by lia.
  apply bv_wrap_small. change (bv_modulus 8) with 256. apply Z.mod_pos_bound. lia.
Qed.

Lemma got_read : forall m, statics_ok m -> rdn ml_segs m (Z_to_bv 64 GOTA) 8 = Some GOT_BYTES.
Proof.
  intros m HS. pose proof layout_statics. rewrite <- got_image. apply rdn_ext; [rewrite uZ by lia; cbn; lia|].
  intros x Hx. rewrite uZ in Hx by lia. rewrite <- (Z_to_bv_bv_unsigned 64 x). apply (so_got m HS). cbn in Hx. lia.
Qed.

Lemma got_val : le_val GOT_BYTES = A_SSP.
Proof.
  unfold le_val, GOT_BYTES, SSPA. pose proof (u64_range A_SSP) as R.
  rewrite bytes_le_to_Z_of_le_bytes by lia. change (2 ^ (8 * Z.of_nat 8)) with (2^64).
  rewrite Z.mod_small by lia. apply Z_to_bv_bv_unsigned.
Qed.

Lemma guard_read : forall m, exists cb, rdn ml_segs m A_SSP 8 = Some cb /\ length cb = 8%nat.
Proof.
  intros m. pose proof layout_statics as L. rewrite <- (Z_to_bv_bv_unsigned 64 A_SSP). fold SSPA.
  assert (G : forall n a, SSPA <= a -> a + Z.of_nat n <= SSPA + 8 ->
             exists cb, rdn ml_segs m (Z_to_bv 64 a) n = Some cb /\ length cb = n).
  { induction n as [|n IH]; intros a Ha Hn.
    - exists []. split; reflexivity.
    - rewrite Nat2Z.inj_succ in Hn. rewrite rdn_S_split, rdn1_eq.
      destruct (IH (a + 1) ltac:(lia) ltac:(lia)) as (bs & Hbs & Hl).
      assert (R : exists b, match m (Z_to_bv 64 a) with Some b => Some b | None => seg_rom ml_segs (Z_to_bv 64 a) end = Some b).
      { destruct (m (Z_to_bv 64 a)) as [b|]; [exists b; reflexivity|].
        destruct (seg_rom ml_segs (Z_to_bv 64 a)) as [b|] eqn:E; [exists b; reflexivity|].
        exfalso. apply (mlo_rom_in (Z_to_bv 64 a)); [rewrite uZ by lia; lia | exact E]. }
      destruct R as [b Hb]. rewrite Hb. rewrite u_add1_lit, Hbs. exists (b :: bs). split; [reflexivity | cbn; lia]. }
  apply G; [lia | cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Section EnvSteps.
  Context {R : Type}.
  Implicit Types (s : mstate) (P : R -> mstate -> Prop).

  Lemma ts_canary_load : forall s (k : word * word -> M R) P,
    statics_ok (ms_mem s) -> WIN s ->
    (forall cb, rdn ml_segs (ms_mem s) A_SSP 8 = Some cb ->
       tsafe (k (A_SSP, le_val cb) s) P) ->
    tsafe ((cc <- m_canary_load ;; k cc) s) P.
  Proof.
    intros s k P HS HW Hk. pose proof layout_statics. unfold m_canary_load. reassoc.
    rewrite <- (Z_to_bv_bv_unsigned 64 A_GOT_SSP). fold GOTA.
    eapply ts_ld; [apply acc_ok_heap; [exact HW | lia | lia | lia] | apply got_read; exact HS |].
    rewrite got_val. reassoc.
    destruct (guard_read (ms_mem s)) as (cb & Hcb & Hl).
    pose proof Hcb as Hcb'. rewrite <- (Z_to_bv_bv_unsigned 64 A_SSP) in Hcb'. fold SSPA in Hcb'.
    rewrite <- (Z_to_bv_bv_unsigned 64 A_SSP) at 1. fold SSPA.
    eapply ts_ld; [apply acc_ok_heap; [exact HW | lia | lia | lia] | exact Hcb' |].
    apply ts_bind_ret. apply Hk. exact Hcb.
  Qed.

  Lemma ts_canary_check : forall s cb (k : unit -> M R) P,
    WIN s -> rdn ml_segs (ms_mem s) A_SSP 8 = Some cb ->
    tsafe (k tt s) P ->
    tsafe ((x <- m_canary_check A_SSP (le_val cb) ;; k x) s) P.
  Proof.
    intros s cb k P HW Hcb Hk. pose proof layout_statics. unfold m_canary_check. reassoc.
    rewrite <- (Z_to_bv_bv_unsigned 64 A_SSP) in Hcb |- *. fold SSPA in Hcb. fold SSPA.
    eapply ts_ld; [apply acc_ok_heap; [exact HW | lia | lia | lia] | exact Hcb |].
    apply ts_assert; [apply c_eq_refl | exact Hk].
  Qed.

  Lemma ts_needlocks : forall s (k : word -> M R) P,
    statics_ok (ms_mem s) -> WIN s -> tsafe (k (Z_to_bv 64 0) s) P ->
    tsafe ((x <- m_lbu A_NEED_LOCKS ;; k x) s) P.
  Proof.
    intros s k P HS HW Hk. pose proof layout_statics. pose proof (so_nl _ HS) as N.
    rewrite <- (Z_to_bv_bv_unsigned 64 A_NEED_LOCKS) in N |- *. fold NLA in N |- *.
    eapply ts_lbu; [apply acc_ok_heap; [exact HW | lia | lia | lia] | exact N |].
    exact Hk.
  Qed.

  (* [comment removed for export] *)
  Lemma lock_read : forall m, statics_ok m -> rdn ml_segs m A_LOCK 4 = Some (Z_to_le_bytes 4 0).
  Proof.
    intros m HS. pose proof layout_statics. rewrite A_LOCK_eq.
    assert (G : forall n a, LOCKA <= a -> a + Z.of_nat n <= LOCKA + 8 ->
               rdn ml_segs m (Z_to_bv 64 a) n = Some (repeat (Z_to_bv 8 0) n)).
    { induction n as [|n IH]; intros a Ha Hn; [reflexivity|].
      rewrite Nat2Z.inj_succ in Hn. rewrite rdn_S_split, rdn1_eq.
      assert (Hj : 0 <= a - LOCKA < 8) by lia.
      pose proof (so_lock m HS (a - LOCKA) Hj) as HL. replace (LOCKA + (a - LOCKA)) with a in HL by lia. rewrite HL.
      rewrite (mlo_ctx_zero (Z_to_bv 64 a)).
      2: { rewrite uZ by lia. pose proof layout_nums. unfold LOCKA in *. pose proof (mlo_order_ctx (ML:=ML)). pose proof (mlo_ctx (ML:=ML)). unfold CTX_SIZE in *. lia. }
      rewrite u_add1_lit, (IH (a + 1)) by lia. reflexivity. }
    rewrite (G 4%nat LOCKA) by (cbn; lia). reflexivity.
  Qed.

  Lemma ts_unlock : forall s (k : unit -> M R) P,
    statics_ok (ms_mem s) -> WIN s -> tsafe (k tt s) P ->
    tsafe ((x <- m_unlock ;; k x) s) P.
  Proof.
    intros s k P HS HW Hk. pose proof layout_statics. unfold m_unlock. reassoc.
    pose proof (lock_read _ HS) as LR. rewrite A_LOCK_eq in LR |- *.
    eapply ts_lw; [apply acc_ok_heap; [exact HW | lia | lia | lia] | exact LR |].
    apply ts_assert; [| exact Hk].
    rewrite (le_val_Z _ 0) by reflexivity. reflexivity.
  Qed.
End EnvSteps.

End WithLayout.
