From Stdlib Require Import ZArith List Lia.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Lib Require Import PropExec MState Mem Exec Frame.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.B Require Import Img0 AsanRT.
From OSSVerify.Proofs.libreac.fuzz_ctrl.lib.Prog Require Import RcAsan RcAsanLib.
Import ListNotations.
Open Scope Z_scope.

Lemma rt_app_shadow : forall a, app_mem a -> in_shadow (shadow_addr a).
Proof.
  unfold app_mem, in_shadow, shadow_addr, ASAN_K, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG,
    APPMEM_END.
  intros a [H|H]; [left|right]; Z.div_mod_to_equations; lia.
Qed.

Lemma rt_shadow_bound : forall a, in_shadow a -> 0 <= a < 2^47.
Proof.
  unfold in_shadow, LOWMEM_END, LOWSHADOW_END, HIGHSHADOW_BEG, HIGHMEM_BEG. intros a [H|H]; lia.
Qed.

Lemma rt_asan_rt : forall m W, asan_cells m ->
  (forall x, GOT_CELL_K <= x < GOT_CELL_K + 8 \/ CELL_K <= x < CELL_K + 8 \/ in_shadow x -> outside W x) ->
  asan_rt rsegs m GOT_CELL_K CELL_K ASAN_K W.
Proof.
  intros m W HC HW. destruct HC as (Hk & Hg & _).
  split; [exact Hg|]. split; [exact Hk|].
  split; intros x Hx; apply HW; [left | right; left]; exact Hx.
Qed.

Lemma rt_addr_byte : forall m a, addr_byte m a ->
  exists k : byte, bytes_at rsegs m (asan_shadow ASAN_K a) [k] /\ shadow_ok a (bv_signed k).
Proof.
  intros m a (Ha & b & Hb & Hok). exists b. split; [|exact Hok].
  pose proof (rt_shadow_bound _ (rt_app_shadow a Ha)) as R. unfold shadow_addr in R.
  unfold asan_shadow. split; [lia|]. split; [cbn; lia|].
  intros i Hi. cbn in Hi. destruct i as [|i]; [|lia]. cbn [Z.of_nat nth_error]. rewrite Z.add_0_r. exact Hb.
Qed.

Lemma rt_shadow_rd : forall m p n W, addressable m p n -> (forall x, in_shadow x -> outside W x) ->
  asan_shadow_rd rsegs m ASAN_K p n W.
Proof.
  intros m p n W (H0 & Hn & Hend & HA) HW i Hi.
  pose proof (HA i Hi) as HB. destruct HB as (Ha & _). split.
  - apply HW. exact (rt_app_shadow (p + i) Ha).
  - destruct (rt_addr_byte m (p + i) (HA i Hi)) as (k & Hk & _). exists k. exact Hk.
Qed.

Lemma rt_addressable : forall m p n, addressable m p n -> asan_addressable rsegs m ASAN_K p n.
Proof.
  intros m p n (_ & _ & _ & HA) i k Hi Hk.
  destruct (rt_addr_byte m (p + i) (HA i Hi)) as (k0 & Hk0 & Hok).
  rewrite (rc_byte1_eq rsegs m _ k k0 Hk Hk0). unfold asan_ok. unfold shadow_ok in Hok. lia.
Qed.

Lemma rt_rt3 : forall m p n, addressable m p n -> asan_rt3 rsegs m ASAN_K p n.
Proof.
  intros m p n (_ & _ & _ & HA) i k Hi Hk.
  destruct (rt_addr_byte m (p + i) (HA i Hi)) as (k0 & Hk0 & Hok).
  rewrite (rc_byte1_eq rsegs m _ k k0 Hk Hk0). unfold shadow_ok in Hok. lia.
Qed.

Lemma rt_addressable_bound : forall m p n, addressable m p n -> 0 <= p /\ 0 <= n /\ p + n <= 2^47.
Proof. intros m p n (H0 & Hn & Hend & _). unfold APPMEM_END in Hend. lia. Qed.
