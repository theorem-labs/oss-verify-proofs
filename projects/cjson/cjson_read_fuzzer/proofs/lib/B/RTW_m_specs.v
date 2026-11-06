(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib Require Import ShapeAlg.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Tac Bytes PropExec MState Mem Cells Step Frame Exec SCPS.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import Spin SRealizes LBase.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require LSCPS.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT.LSCPS.LStep.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.LRT Require Import LSCPS LSCPS2.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import BImg RT_defs RT_data.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.RT_geom.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_wf RT_rep CJ_iface RT_art RT_fp.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_fp.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_fp.RT_artB.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_cost.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_cost.RT_artG.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_artF.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_kit.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_kit.RT_shlem.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_common_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_primary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_sec.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_sec.RTW_secondary_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RTW_primary_iface.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RTW_primary_iface.RTW_depot_iface.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RTW_m_tpz.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require RT_wf.
Import OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B.RT_wf.ABand.
From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.B Require Import RT_bandtac4.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.

Import ListNotations.
Open Scope Z_scope.

From OSSVerify.Proofs.cjson.cjson_read_fuzzer.lib.Lib Require Import Ceil.
(* [comment removed for export] *)
Section CeilWrap.
Context {ACEIL : Ceil}.


(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma errno_notin_primary_fp : forall st c a, RTWF st -> 0 <= c < KNUMCLASSES -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (primary_fp st c) a.
Proof.
  intros st c a WF Hc Ha (lo & hi & Hin & Hr). pose proof (t_range st WF) as TR. destruct (region_range st WF c Hc) as (R1 & R2 & _).
  pose proof (P_range st WF) as (P1 & _). pose proof (ris_range st WF) as (I1 & _). pose proof (rt_SH_mono KHIGHMEM_BEG (rbeg st c) ltac:(lia)) as SB. change (SH KHIGHMEM_BEG) with 0x2008fff7000 in SB.
  unfold primary_fp, fp_class, fp_tpage, rinfo, AERRNO, ATP, KHIGHMEM_BEG in *. cbn in Hin.
  destruct Hin as [E|[E|[E|[E|[]]]]]; injection E as E1 E2; subst lo hi; blia.
Qed.
Lemma errno_notin_secondary_fp : forall st mb n a, RTWF st -> ablk mb (mb + smapsize n) -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (secondary_fp st mb n) a.
Proof.
  intros st mb n a WF Hmb Ha (lo & hi & Hin & Hr). pose proof (t_range st WF) as TR. pose proof (pa_range st WF) as (P1 & _).
  pose proof (ablk_img _ _ Hmb) as Hmi. unfold AIMG_HI in Hmi.
  pose proof (rt_SH_mono 0 mb ltac:(lia)) as SB. change (SH 0) with 0x7fff8000 in SB.
  unfold secondary_fp, fp_tpage, A_SECONDARY, A_GSTATS, A_ALLOC, AERRNO, ATP, KHIGHMEM_BEG in *.
  apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
  - cbn in Hin. destruct Hin as [E|[E|[E|[E|[E|[]]]]]]; injection E as E1 E2; subst lo hi; blia.
  - cbn in Hin. destruct Hin as [E|[]]. injection E as E1 E2; subst lo hi; blia.
  - apply in_map_iff in Hin as ([b k] & E & Hb). injection E as E1 E2; subst lo hi. cbn [fst] in Hr.
    pose proof (wb_ranges st (wf_base_ok st WF) (b, b + smapsize k)) as R.
    specialize (R ltac:(rewrite rt_ranges_tail; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b, k); auto)).
    cbn [fst snd] in R. lia.
Qed.
Lemma errno_notin_secondary_fp0 : forall st a, RTWF st -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (secondary_fp st 0 0) a.
Proof.
  intros st a WF Ha (lo & hi & Hin & Hr). pose proof (t_range st WF) as TR. pose proof (pa_range st WF) as (P1 & _).
  assert (E : smapsize 0 = 8192) by (vm_compute; reflexivity).
  unfold secondary_fp, fp_tpage in Hin. rewrite E in Hin. change (SH 0) with 0x7fff8000 in Hin. change (SH (0 + 8192)) with 0x7fff8400 in Hin.
  unfold A_SECONDARY, A_GSTATS, A_ALLOC, AERRNO, ATP, KHIGHMEM_BEG in *.
  apply in_app_iff in Hin as [Hin|Hin]; [| apply in_app_iff in Hin as [Hin|Hin]].
  - cbn in Hin. destruct Hin as [E'|[E'|[E'|[E'|[E'|[]]]]]]; injection E' as E1 E2; subst lo hi; blia.
  - cbn in Hin. destruct Hin as [E'|[]]. injection E' as E1 E2; subst lo hi; blia.
  - apply in_map_iff in Hin as ([b k] & E' & Hb). injection E' as E1 E2; subst lo hi. cbn [fst] in Hr.
    pose proof (wb_ranges st (wf_base_ok st WF) (b, b + smapsize k)) as R.
    specialize (R ltac:(rewrite rt_ranges_tail; apply in_or_app; right; apply in_or_app; right; apply in_or_app; left; apply in_map_iff; exists (b, k); auto)).
    cbn [fst snd] in R. lia.
Qed.
Lemma errno_notin_depot_fp : forall st a, RTWF st -> AERRNO <= a < AERRNO + 4 -> ~ in_ivs (depot_fp st) a.
Proof.
  intros st a WF Ha (lo & hi & Hin & Hr). unfold depot_fp, fp_depot_blocks, A_STACKSTORE, A_DEPOT_MAP1, AERRNO, ATP in *.
  destruct Hin as [E|Hin]; [injection E as E1 E2; subst lo hi; lia|].
  pose proof (wb_ranges st (wf_base_ok st WF) (lo, hi)) as R.
  specialize (R ltac:(rewrite rt_ranges_tail; apply in_or_app; right; apply in_or_app; right; apply in_or_app; right; exact Hin)).
  cbn [fst snd] in R. unfold KHIGHMEM_BEG in R. blia.
Qed.

(* [comment removed for export] *)
Definition depot_put_specS : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (P : Z) (tr : list Z) (lo : Z),
  RTS st m mo g ->
  a0 = wz P -> a1 = wz (zlen tr) -> 1 <= zlen tr <= TRACE_MAX_LEN -> Forall (fun pc => 0 <= pc < 2^64) tr ->
  cells_at bsegs m P (trace_cells tr) -> (P + 8 * zlen tr <= lo \/ bv_unsigned sp <= P) -> alloc_ceiling <= P -> P + 8 * zlen tr < 2^64 ->
  tp = wz ATP ->
  trs_room tr (st_trs st) ->
  rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ADEPOT_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (depot_put_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st tr lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ADEPOT_PUT) fc None m (seg_rom bsegs)) mo g.
Lemma depot_put_specS_hub : depot_put_spec -> depot_put_specS.
Proof. intros H. unfold depot_put_specS. intros. eapply H; eauto. Qed.

Definition ACALLOC : Z := 0x365c0.            (* [comment removed for export] *)
Definition ACALLOC_STACK : Z := AREFILL_STACK + 48.

(* [comment removed for export] *)
Definition calloc_deposit (n : Z) : Z := if bprim n then 2 * csize (pclass n) else SEC_ALLOC_COST n + SEC_SLOT_TAX.

(* [comment removed for export] *)
Definition calloc_rel (st st' : rtstate) (n r : Z) : Prop :=
  same_client st st' /\ st_qpend st' = st_qpend st /\ st_qtmp st' = st_qtmp st /\ st_qcur st' = st_qcur st
  /\ st_qthread st' = st_qthread st /\ st_qglobal st' = st_qglobal st /\ st_depot st' = st_depot st
  /\ st_fs st' = st_fs st /\ st_t st' = st_t st /\ st_spacebeg st' = st_spacebeg st /\ st_pbase st' = st_pbase st /\ st_pa st' = st_pa st
  /\ ( (r = 0 /\ st_apend st' = st_apend st /\ st_spend st' = st_spend st /\ st_sec st' = st_sec st)
     \/ (bprim n = true /\ exists k, r = cptr_addr st (pclass n) k
            /\ st_apend st' = (pclass n, k) :: st_apend st /\ st_spend st' = st_spend st /\ st_sec st' = st_sec st)
     \/ (bprim n = false /\ exists mb, r = sec_alloc_beg mb /\ ablk mb (mb + smapsize n) /\ mb mod 4096 = 0 /\ mb + smapsize n <= alloc_ceiling
            /\ st_apend st' = st_apend st /\ st_spend st' = (mb, n) :: st_spend st /\ st_sec st' = st_sec st ++ [(mb, n)]
            /\ st_regions st' = st_regions st /\ st_cache st' = st_cache st) ).

(* [comment removed for export] *)

(* [comment removed for export] *)
Definition sec_alloc_postW (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ sec_alloc_rel st st' n r
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ (r = 0 -> rt_frame (secondary_fp st 0 0) lo (bv_unsigned sp) m m' /\ budget_ok st g st' g' 0)
        /\ (forall mb, r = sec_alloc_beg mb -> ablk mb (mb + smapsize n) ->
              rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
              /\ budget_ok st g st' g' (SEC_ALLOC_COST n + SEC_SLOT_TAX)
              /\ rw_cells bsegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
              /\ rw_cells bsegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096)) (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
              /\ sec_win g' mb n)
        /\ gmono g g').

Definition large_alloc_specW : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv bsegs m ->
  LSCPS bsegs (sec_alloc_postW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
Definition sec_alloc2_post_blkW (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists mb,
        a0' = wz (sec_alloc_beg mb) /\ sec_alloc_rel st st' n (sec_alloc_beg mb) /\ ablk mb (mb + smapsize n)
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m'
        /\ rt_frame (secondary_fp st mb n) lo (bv_unsigned sp) m m'
        /\ budget_ok st g st' g' (SEC_ALLOC_COST n + SEC_SLOT_TAX)
        /\ rw_cells bsegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
        /\ rw_cells bsegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096)) (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
        /\ sec_win g' mb n
        /\ gmono g g').
Definition large_alloc_spec2W : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g ->
  0 <= n -> bprim n = false -> needed n <= 2^40 ->
  a0 = wz A_SECONDARY -> a1 = wz A_GSTATS -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  SEC_ALLOC_COST n + SEC_SLOT_TAX + rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ALARGE_ALLOC_STACK ->
  mem_inv bsegs m ->
  LSCPS2 bsegs (sec_alloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
               (sec_alloc2_post_blkW ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ALARGE_ALLOC) fc None m (seg_rom bsegs)) mo g.

Definition calloc_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ 0 <= r < 2^64 /\ calloc_rel st st' n r
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' (if r =? 0 then 0 else calloc_deposit n)
        (* [comment removed for export] *)
        /\ (bprim n = false -> forall mb, r = sec_alloc_beg mb -> ablk mb (mb + smapsize n) ->
              rw_cells bsegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
              /\ rw_cells bsegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096))
                   (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
              /\ sec_win g' mb n)).

Definition combined_alloc_spec : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  calloc_deposit n + rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK -> bv_unsigned sp <= st_sp0 st ->
  mem_inv bsegs m ->
  LSCPS bsegs (calloc_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition calloc2_post_null (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 0 /\ st' = st
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).
Definition calloc2_post_sec (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists mb,
        a0' = wz (sec_alloc_beg mb) /\ ablk mb (mb + smapsize n) /\ mb mod 4096 = 0 /\ mb + smapsize n <= alloc_ceiling
        /\ same_but_secondary st st' /\ st_qcur st' = st_qcur st
        /\ st_spend st' = (mb, n) :: st_spend st /\ st_sec st' = st_sec st ++ [(mb, n)]
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' (calloc_deposit n)
        /\ rw_cells bsegs m' (SH mb) (zcells (zrep SV_HEAP_LEFT_RZ 512))
        /\ rw_cells bsegs m' (SH (sec_alloc_beg mb + rounded8 n + 4096))
             (zcells (zrep SV_HEAP_LEFT_RZ ((mb + smapsize n - (sec_alloc_beg mb + rounded8 n + 4096)) / 8)))
        /\ sec_win g' mb n).

Definition calloc2_sec_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 -> bprim n = false ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  calloc_deposit n + rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK -> bv_unsigned sp <= st_sp0 st ->
  mem_inv bsegs m ->
  LSCPS2 bsegs (calloc2_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
               (calloc2_post_sec ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACALLOC) fc None m (seg_rom bsegs)) mo g.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition calloc2f_post_null (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' =>
        a0' = wz 0 /\ calloc_rel st st' n 0
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' 0).
Definition calloc2f_post_blk (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : rtstate) (n lo : Z) (m : word -> option byte) (g : lghost) : machine_state -> Model -> lghost -> Prop :=
  rt_post_std ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
    (fun a0' m' st' mo' g' => exists r,
        a0' = wz r /\ 0 < r < 2^64 /\ calloc_rel st st' n r
        /\ RTS st' m' mo' g' /\ stk bsegs m' lo (bv_unsigned sp)
        /\ cli_pres st (bv_unsigned sp) m m' /\ errno_same m m'
        /\ gmono g g' /\ budget_ok st g st' g' (calloc_deposit n)).

Definition calloc2_fresh_stmt : Prop :=
  forall (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : word -> option byte) (mo : Model) (g : lghost)
         (st : rtstate) (n lo : Z),
  RTS st m mo g -> (forall st0, RTWF st0 -> tpx_ok st0) -> st_apend st = [] ->
  0 <= n < 2^32 -> bprim n = true -> fresh_cls st (pclass n) ->
  a0 = wz A_ALLOC -> a1 = wz (acache st) -> a2 = wz (needed n) -> a3 = wz 8 ->
  tp = wz ATP ->
  calloc_deposit n + rt_prov st <= g_res g ->
  stk bsegs m lo (bv_unsigned sp) -> alloc_ceiling <= lo -> lo <= bv_unsigned sp - ACALLOC_STACK -> bv_unsigned sp <= st_sp0 st ->
  mem_inv bsegs m ->
  LSCPS2 bsegs (calloc2f_post_null ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
               (calloc2f_post_blk ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st n lo m g)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (wz ACALLOC) fc None m (seg_rom bsegs)) mo g.


End CeilWrap.
