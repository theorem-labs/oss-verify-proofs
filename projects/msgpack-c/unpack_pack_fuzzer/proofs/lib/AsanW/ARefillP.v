(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType State Specs Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib Require PropExec MState Mem Cells Exec Step Frame Arr Tac ITree Nodes Decode SysStep.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require MM_syscalls WStr.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA Require SysStepF.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec Require STree AsanCtrl AsanEmbed.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AImg AProto ABase AKit AKit2 ABytes AModelFacts ARep ARepKit ARepFrame ALayout AHeapP ARefill_iface RT_stubs.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_apoison.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acache.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aalloc3.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_ammap.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_aensure F_apopulate.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_agetfrom.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arefill.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AC6U AExh.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common Require RunDraw.
Module ARefillP.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition newslots (nd : Z) (n : nat) : list Z := rev (map (fun j => nd + Z.of_nat j) (seq 0 n)).

Lemma newslots_length : forall nd n, length (newslots nd n) = n.
Proof. intros. unfold newslots. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma newslots_In : forall nd n k, In k (newslots nd n) <-> nd <= k < nd + Z.of_nat n.
Proof.
  intros nd n k. unfold newslots. rewrite <- in_rev, in_map_iff. split.
  - intros (j & <- & Hj). apply in_seq in Hj. lia.
  - intros Hk. exists (Z.to_nat (k - nd)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma newslots_NoDup : forall nd n, List.NoDup (newslots nd n).
Proof.
  intros nd n. unfold newslots. apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros a b _ _ E. lia.
Qed.

Lemma map_cw_newslots : forall c nd n, 1 <= c < K_NUM_CLASSES ->
  map (fun k => Z_to_bv 64 (acompact c k)) (newslots nd n) = fvals (nd * size_of_class c) (size_of_class c) n.
Proof.
  intros c nd n Hc. pose proof (size_of_class_facts c Hc) as [S1 S3].
  unfold newslots, fvals. rewrite map_rev, map_map. f_equal. apply map_ext. intros j.
  f_equal. unfold acompact. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
  generalize S1 S3; clear; intros. Z.div_mod_to_equations. nia.
Qed.

Lemma NoDup_bound_length : forall (l : list Z) n, List.NoDup l -> (forall k, In k l -> 0 <= k < n) -> 0 <= n -> Z.of_nat (length l) <= n.
Proof.
  intros l n ND B N.
  assert (INCL : incl (map Z.to_nat l) (seq 0 (Z.to_nat n))).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq. specialize (B k Hk). lia. }
  apply NoDup_incl_length in INCL.
  - rewrite length_map, length_seq in INCL. lia.
  - apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros a b Ha Hb E. pose proof (B a Ha). pose proof (B b Hb). lia.
Qed.

Lemma nodup_app : forall {A} (a b : list A), List.NoDup a -> List.NoDup b -> (forall x, In x a -> ~ In x b) -> List.NoDup (a ++ b).
Proof.
  intros A a b NA NB D. induction a as [|x a IH]; cbn; [exact NB|].
  inversion NA; subst. constructor.
  - rewrite in_app_iff. intros [Hx|Hx]; [exact (H1 Hx)|]. exact (D x (or_introl eq_refl) Hx).
  - apply IH; [exact H2|]. intros y Hy. apply D. right; exact Hy.
Qed.

Lemma junk_sub : forall m A n A' n', junk_at m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> junk_at m A' n'.
Proof.
  intros m A n A' n' J H1 H2 H3.
  destruct (junk_split m A (A' - A) (n - (A' - A)) ltac:(replace (A' - A + (n - (A' - A))) with n by lia; exact J) ltac:(lia) ltac:(lia)) as [_ J2].
  replace (A + (A' - A)) with A' in J2 by lia.
  destruct (junk_split m A' n' (n - (A' - A) - n') ltac:(replace (n' + (n - (A' - A) - n')) with (n - (A' - A)) by lia; exact J2) ltac:(lia) ltac:(lia)) as [J3 _].
  exact J3.
Qed.

Lemma fill_sub : forall m A n A' n' v, fill_at m A n v -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> fill_at m A' n' v.
Proof.
  intros m A n A' n' v F H1 H2 H3. unfold fill_at in *.
  pose proof (rw_cells_split_CB asegs m A [] (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) [] [Z.to_nat (A' - A); Z.to_nat n'; Z.to_nat (n - (A' - A) - n')] F ltac:(cbn; lia)) as SP.
  cbn [app mk_CB_cells] in SP.
  rewrite !skipn_repeat' in SP. rewrite (firstn_repeat' _ (Z.to_nat n')) in SP by lia.
  apply (proj1 (rw_cells_app asegs m A [_] [_; _])) in SP. destruct SP as [_ SP].
  apply (proj1 (rw_cells_app asegs m _ [_] [_])) in SP. destruct SP as [SP _].
  cbn [cells_size csize Nat.add] in SP. rewrite Nat.add_0_r, Z2Nat.id in SP by lia.
  replace (A + (A' - A)) with A' in SP by lia. exact SP.
Qed.

Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v F1 F2 Ha Hb. unfold fill_at in *.
  pose proof (cb_app m A _ _ _ _ F1 ltac:(rewrite Z2Nat.id by lia; exact F2)) as CA.
  rewrite <- repeat_app in CA. replace (Z.to_nat a + Z.to_nat b)%nat with (Z.to_nat (a + b)) in CA by lia. exact CA.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr asegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws AR. exists (u32s ws). apply rw_cells_of_u8arr' || idtac.
  pose proof (rw_cells_of_u8arr asegs m A (u32s ws) (u8arr_of_u32arr asegs m A ws AR)) as R.
  rewrite u32s_length in R. replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia. exact R.
Qed.

Lemma junk_of_fill : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v F. eexists. exact F. Qed.

Lemma u32arr_firstn : forall m A ws k, u32arr asegs m A ws -> (k <= length ws)%nat -> u32arr asegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1. split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    rewrite <- (firstn_skipn k ws) in B. specialize (B i ltac:(rewrite u32s_length, length_app, length_firstn, length_skipn; lia)).
    rewrite u32s_app, nth_error_app1 in B by (rewrite u32s_length, length_firstn; lia). exact B.
  - split; [lia|]. split; [rewrite length_firstn; lia|]. intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

Definition xr (X : aconc) (c : Z) (fr ca : list Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass fr ca else x_cls X c') (x_busy X).

Lemma busy_of_In_slots : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b Hb. destruct (busy_of_Some_facts X c k b Hb) as (HIn & HC & HK).
  unfold busy_slots. apply in_map_iff. exists b. split; [exact HK|]. apply filter_In. split; [exact HIn|]. apply Z.eqb_eq. exact HC.
Qed.

Lemma xr_busy_of : forall X c fr ca c' k, busy_of (xr X c fr ca) c' k = busy_of X c' k.
Proof. intros. reflexivity. Qed.
Lemma xr_busy_slots : forall X c fr ca c', busy_slots (xr X c fr ca) c' = busy_slots X c'.
Proof. intros. reflexivity. Qed.
Lemma xr_cls_eq : forall X c fr ca, x_cls (xr X c fr ca) c = mkXClass fr ca.
Proof. intros. unfold xr. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma xr_cls_ne : forall X c fr ca c', c' <> c -> x_cls (xr X c fr ca) c' = x_cls X c'.
Proof. intros X c fr ca c' NE. unfold xr. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.

Lemma alayout_res_disj : forall L, alayout_ok L ->
     (al_ctx L + 65536 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L)
  /\ (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L).
Proof.
  intros L H. pose proof (ad_ctx_res L H) as D1. pose proof (ad_t_res L H) as D2. pose proof (ao_space L H) as SB.
  pose proof (ao_ctx L H) as C. pose proof (ao_t L H) as T.
  unfold adisj, aobj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472. lia.
Qed.

Lemma region_other_geo : forall L c c', alayout_ok L -> 1 <= c < 32 -> 1 <= c' < 32 -> c' <> c ->
  al_space_beg L <= aregion L c' /\ (aregion L c' + 4294967296 <= aregion L c \/ aregion L c + 4294967296 <= aregion L c') /\ aregion L c' + 4294967296 <= al_space_beg L + 137438953472
  /\ afreearr L c' = aregion L c' + 3758096384 /\ aregion_info L c' = al_space_beg L + 137438953472 + c' * 128 /\ acache_addr L c' = al_t L + 208 + c' * 80
  /\ aregion L c' mod 8 = 0 /\ (shad (aregion L c') + shlen 4294967296 <= shad (aregion L c) \/ shad (aregion L c + 4294967296) <= shad (aregion L c'))
  /\ 2201439137792 <= shad (aregion L c') /\ shad (aregion L c') + shlen 4294967296 <= 17594333495296
  /\ shad (afreearr L c') = shad (aregion L c') + shlen 3758096384.
Proof.
  intros L c c' ALO HC Hc' NE.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  unfold afreearr, aregion_info, acache_addr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE.
  change (2^32) with 4294967296. change (2^37) with 137438953472.
  assert (Q : exists q, al_space_beg L = 65536 * q) by (exists (al_space_beg L / 65536); Z.div_mod_to_equations; lia).
  destruct Q as [q Hq]. rewrite Hq in *.
  rewrite !shad_div, !shlen_div. unfold ASHOFF.
  replace ((65536 * q + c' * 4294967296) / 8) with (8192 * q + c' * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296) / 8) with (8192 * q + c * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296 + 4294967296) / 8) with (8192 * q + c * 536870912 + 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c' * 4294967296 + 3758096384) / 8) with (8192 * q + c' * 536870912 + 469762048) by (Z.div_mod_to_equations; lia).
  change (4294967296 / 8) with 536870912. change (3758096384 / 8) with 469762048.
  assert (CC : c' + 1 <= c \/ c + 1 <= c') by lia.
  repeat split; lia.
Qed.

Section RefillP.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Definition store_refill_stmt_ns : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr asegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X' WH, AREPns H L st_r X' m' /\ munch WH m m' /\ sec_untouched L WH /\ (c = K_BATCH_CLASS -> c6_untouched L WH) /\ sec_same st st_r
    /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m'.

Definition store_refill_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c = K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr asegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono asegs m m'.

Notation Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n :=
  ([(sp - 672, sp); (RB + mu, RB + mu'); (SHU0, SHU1); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1);
    (t + 2792, t + 2800); (t + 2800, t + 3168); (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
    (CA, CA + 4); (CA + 16, CA + 16 + 4 * n)]%Z) (only parsing).

Lemma outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. intros l1 l2 x. induction l1 as [|[lo hi] l1 IH]; cbn; tauto. Qed.

Lemma dj_app : forall l1 l2 A k, disjoint_from l1 A k -> disjoint_from l2 A k -> disjoint_from (l1 ++ l2) A k.
Proof. intros l1 l2 A k D1 D2. induction l1 as [|[lo hi] l1 IH]; cbn in *; [exact D2|]. destruct D1 as [D1 D1']. split; [exact D1| apply IH; exact D1']. Qed.

Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1 : Z).
Definition rkfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 672 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6483968 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80 /\ 1 <= n <= 8)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= mu' /\ mu' <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : rkfacts.

Ltac kind := pose proof KF as KF'; unfold rkfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_obj : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2792 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 16 + 4 * n <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_slots : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_gap : forall A k, RB + mu' <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 56 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= RI + 72 \/ RI + 80 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_shlow : forall A k, 2201439137792 <= A -> A + k <= SHU0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shmid : forall A k, SHU1 <= A -> A + k <= SHF0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shhigh : forall A k, SHF1 <= A -> A + k <= 17594333495296 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
End Kinds.

Definition rrec (mu' au2 nfr mfa' n : Z) : aclass := mkAClass mu' au2 nfr mfa' n.

Lemma init_cache_fields : forall st,
  a_live (init_cache st) = a_live st /\ a_next (init_cache st) = a_next st /\ a_qloc (init_cache st) = a_qloc st
  /\ a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob (init_cache st) = a_qglob st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_nsec (init_cache st) = a_nsec st /\ a_nres (init_cache st) = a_nres st /\ a_ptr_array (init_cache st) = a_ptr_array st
  /\ a_space_beg (init_cache st) = a_space_beg st /\ a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; cbn; repeat split; try reflexivity. exact E. Qed.

Lemma put_cls_fields : forall c r st,
  a_live (put_cls c r st) = a_live st /\ a_next (put_cls c r st) = a_next st /\ a_qloc (put_cls c r st) = a_qloc st
  /\ a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob (put_cls c r st) = a_qglob st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_nsec (put_cls c r st) = a_nsec st /\ a_nres (put_cls c r st) = a_nres st /\ a_ptr_array (put_cls c r st) = a_ptr_array st
  /\ a_space_beg (put_cls c r st) = a_space_beg st /\ a_cinit (put_cls c r st) = a_cinit st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma awf_refill : forall L st X c mu' ncnt mfa' n,
  let r := get_cls st c in let S := size_of_class c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  let nd := ndist st c in let nf2 := nf + ncnt in let au2 := au + ncnt * S in
  let FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt) in
  let st_r := put_cls c (rrec mu' au2 (nf2 - n) mfa' n) (init_cache st) in
  let X' := xr X c (firstn (Z.to_nat (nf2 - n)) FL2) (skipn (Z.to_nat (nf2 - n)) FL2) in
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count r = 0 ->
  mu <= mu' <= K_FREEARR_OFF -> mu' mod K_USER_MAP = 0 -> 0 <= ncnt -> au2 <= mu' ->
  4 * nf2 <= mfa' <= K_FREEARR_MAX -> mfa <= mfa' -> mfa' mod K_FREEARR_MAP = 0 ->
  1 <= n <= nf2 -> 2 * n = max_cached c ->
  awf L st_r X'.
Proof.
  intros L st X c mu' ncnt mfa' n. cbv zeta.
  intros WF HC CNT0 MUB MUM NC0 NCS NEWB NEWM NEWMOD N N2.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  set (st1 := init_cache st) in *.
  set (S := size_of_class c) in *. set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)) in *.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  assert (NDE : nd * S <= c_allocated_user (get_cls st c) < nd * S + S /\ 0 <= nd).
  { subst nd S. unfold ndist. generalize A1 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as [NDE ND0].
  assert (AUE : c_allocated_user (get_cls st c) = nd * S) by (subst nd S; unfold ndist; generalize A3 A1 SZ16 NDE; clear; intros; Z.div_mod_to_equations; nia).
  assert (ND2 : ndist (put_cls c (rrec mu' (c_allocated_user (get_cls st c) + ncnt * S) (c_num_freed (get_cls st c) + ncnt - n) mfa' n) st1) c = nd + ncnt).
  { unfold ndist. rewrite get_cls_put_cls_eq. cbn [c_allocated_user rrec]. fold S. rewrite AUE.
    generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  assert (LFL2 : Z.of_nat (length FL2) = c_num_freed (get_cls st c) + ncnt) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0; lia).
  unfold awf.
  cbn [a_space_beg a_ptr_array a_live a_next put_cls set_cls].
  rewrite E10, E9.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  {
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_put_cls_eq, xr_cls_eq. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count rrec xc_free xc_cache]. fold S.
      rewrite ND2. unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      rewrite xr_busy_slots.
      split; [clear -A1 NC0 NCS SZ16; nia|]. split; [exact (proj2 MUB)|]. split.
      { rewrite AUE. rewrite <- Z.mul_add_distr_r. apply Z_mod_mult. }
      split; [exact MUM|]. split; [clear -N NC0 A5; lia|]. split; [clear -NEWB N; lia|]. split; [exact NEWMOD|].
      split; [rewrite length_firstn; clear -LFL2 N NC0 A5; lia|].
      split; [rewrite length_skipn; clear -LFL2 N NC0 A5; lia|].
      split; [clear -N N2; lia|].
      rewrite app_assoc, firstn_skipn.
      split.
      +
        subst FL2. rewrite XC0 in ND. cbn [app] in ND. rewrite <- app_assoc.
        eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_app_swap_app|].
        apply nodup_app; [apply newslots_NoDup | exact ND |].
        intros x Hx Hx'. apply newslots_In in Hx. rewrite Z2Nat.id in Hx by exact NC0.
        specialize (RANGE x ltac:(rewrite XC0; cbn [app]; exact Hx')). unfold ndist in RANGE. fold S nd in RANGE. clear -Hx RANGE. lia.
      + intros k0 Hk. subst FL2. rewrite <- app_assoc, in_app_iff, in_app_iff in Hk.
        destruct Hk as [Hk|[Hk|Hk]].
        * specialize (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
        * apply newslots_In in Hk. rewrite Z2Nat.id in Hk by exact NC0. clear -Hk ND0; lia.
        * specialize (RANGE k0 ltac:(rewrite XC0; cbn [app]; apply in_app_iff; right; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
    - rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite (xr_cls_ne X c _ _ c' NE), xr_busy_slots.
      subst st1. rewrite init_cache_cls. unfold ndist. rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite init_cache_cls.
      unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      pose proof (max_cached_range c' ltac:(unfold K_NUM_CLASSES in Hc'; clear -Hc'; lia)) as [MCR' _].
      unfold max_count in BCNTB. unfold ndist in BRANGE.
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -B1 B6 BCNTB MCR'; lia).
      destruct (a_cinit st); clear -BCNTB MCR'; lia. }
  split.
  { intros c' Hc'. rewrite (get_cls_put_cls_ne c c') by (intros ->; exact (Hc' HC)). subst st1. rewrite init_cache_cls. apply OUTC. exact Hc'. }
  cbn [x_busy xr]. rewrite E1, E2.
  split; [exact BUSY|]. split; [exact LIVE|]. split; [exact FRESH|]. exact UNIQ.
Qed.

Lemma refill_store_ns : store_refill_stmt_ns.
Proof.
  unfold store_refill_stmt_ns.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [MCR MCE].
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }

  destruct RR as (m1 & MU1 & WM1 & TR & RECS').
  unfold refill_tail_ret in TR. rewrite !init_cache_cls in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & (bfl & EXH' & EXH0) & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (n := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)).
  set (fr := firstn (Z.to_nat (nf + ncnt - n)) FL2). set (ca := skipn (Z.to_nat (nf + ncnt - n)) FL2).
  set (X' := xr X c fr ca).
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (NDE : nd * S <= au < nd * S + S /\ 0 <= nd /\ au = nd * S).
  { subst nd S au. unfold ndist. generalize A1 A3 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as (NDE & ND0 & AUE).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).

  assert (STR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)).
  { rewrite GC2. cbn [c_num_freed cls_set_num_freed cls_set_count c_mapped_user c_allocated_user c_mapped_free_array c_count]. unfold rrec.
    destruct ST2E as [E|E]; rewrite E at 1; [reflexivity| apply put_cls_put_cls]. }
  set (st_r := put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) in *. rewrite STR.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (ND2 : ndist st_r c = nd + ncnt).
  { unfold ndist. rewrite GR. cbn [c_allocated_user rrec]. fold S. rewrite AUE. generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }

  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  set (SHU0 := shad (RB + mu)) in *. set (SHU1 := SHU0 + shlen (mu' - mu)) in *.
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHU1 = shad (RB + mu') /\ SHF1 = shad (FA + mfa') /\ shad RB + shlen mu = SHU0 /\ shad FA + shlen mfa = SHF0
                /\ 2201439137792 <= shad RB /\ shad RB <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 + shlen (3758096384 - mu') = shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ SHU1 <= shad FA /\ SHF1 <= shad (RB + 4294967296)
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296).
  { subst SHU1 SHU0 SHF1 SHF0. rewrite RBE, FAE. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 SP3 HC MUB A1 A2 A4 MUM' A5 A6 A7 NEWB NEWM NEWMOD. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE2 & SHE3 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH12 & SH13 & SH9 & SH10 & SH11).
  assert (KF : rkfacts (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1).
  { unfold rkfacts. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL2 TL4 CL1 CL2 CL3 CL5 HC CAE N SP1 SP2 RBE FAE RIE TSP SCX A1 MUB A5 A6 NEWB NEWM SH1 SH2 SH3 SH5 SH6 SH8 SH12 SH13.
    unfold AIMG_HI in CL3. unfold iclr, AIMG_LO, AIMG_HI in TL4 |- *. repeat split; first [assumption | lia]. }
  assert (MUALL : munch (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUT]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW]. cbn [outside] in H13 |- *. split; [exact (proj1 H13) | exact HW].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst CA. exact H13. }
  pose proof (wmono_trans _ _ _ _ WM1 WMT) as WMALL.

  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  assert (FLE : map (fun k => Z_to_bv 64 (acompact c k)) FL2 = map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)) ++ fvals au S (Z.to_nat ncnt)).
  { subst FL2. rewrite map_app. f_equal. rewrite AUE. apply map_cw_newslots. unfold K_NUM_CLASSES; exact HC. }
  rewrite <- FLE in AR2, CH'.
  assert (LFL2 : length FL2 = Z.to_nat (nf + ncnt)) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0 A5; lia).
  assert (MOD8 : mu mod 8 = 0 /\ mu' mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\ au mod 8 = 0 /\ S mod 8 = 0 /\ RB mod 8 = 0 /\ FA mod 8 = 0).
  { rewrite RBE, FAE, AUE. clear -A4 MUM' A7 NEWMOD SZM SP3 ND0. Z.div_mod_to_equations. nia. }
  destruct MOD8 as (M8a & M8b & M8c & M8d & M8e & M8f & M8g & M8h).

  assert (BIGJ : junk_at m' (RB + au) (mu' - au)).
  { assert (J1 : junk_at m' (RB + au) (mu - au)).
    { eapply junk_frame; [exact UND | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -A1; lia | apply ICW_far; clear -A1 A2 TSP RBE HC; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & ZN & _)].
    - rewrite Emu. exact J1.
    - replace (mu' - au) with ((mu - au) + (mu' - mu)) by (clear; lia). apply junk_merge; [exact J1 | | clear -A1; lia | clear -MUB; lia].
      replace (RB + au + (mu - au)) with (RB + mu) by (clear; lia). eexists. exact ZN. }
  assert (BIGF : fill_at m' (shad (RB + au)) (shlen (mu' - au)) 0xfa).
  { assert (F1 : fill_at m' (shad (RB + au)) (shlen (mu - au)) 0xfa).
    { eapply fill_frame; [exact SUND | exact MUALL | exact WMALL |]. intros _.
      assert (B : shad (RB + au) + shlen (mu - au) <= SHU0 /\ 2201439137792 <= shad (RB + au) /\ 0 <= shlen (mu - au)).
      { subst SHU0. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -A1 SH1 M8g M8e M8a. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B; lia | apply ICW_far; clear -B TL1u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & _ & FI & _)].
    - rewrite Emu. exact F1.
    - replace (shlen (mu' - au)) with (shlen (mu - au) + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b M8e A1 MUB; Z.div_mod_to_equations; lia).
      apply fill_merge; [exact F1 | | rewrite shlen_div; clear -A1 M8a M8e; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia].
      replace (shad (RB + au) + shlen (mu - au)) with (shad (RB + mu)) by (rewrite !shad_div, shlen_div; clear -A1 M8a M8e M8g; Z.div_mod_to_equations; lia).
      exact FI. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user rrec]. fold S.
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [unfold aflag_cell; destruct (c =? K_BATCH_CLASS) eqn:QB; [apply Z.eqb_eq in QB; rewrite (EXH0 QB) in EXH'; exact EXH'| exact (junk_of_cells m' _ _ EXH')]|].
    destruct (junk_split m (RI + 72) 8 48 RJ56 ltac:(clear; lia) ltac:(clear; lia)) as [_ J48].
    replace 56 with (8 + 48) by reflexivity. apply junk_merge; [| | clear; lia | clear; lia].
    - pose proof (junk_of_cells m' _ _ STN') as J8. cbn in J8. exact J8.
    - eapply junk_frame; [exact J48 | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_free].
    split; [| split].
    - subst fr. rewrite <- firstn_map. apply u32arr_firstn; [exact AR2 | rewrite length_map, LFL2; clear -N NLE NC0 A5; lia].
    - replace (mfa' - 4 * (nf + ncnt - n)) with (4 * Z.of_nat (length (skipn (Z.to_nat (nf + ncnt - n)) FL2)) + (mfa' - 4 * (nf + ncnt)))
        by (rewrite length_skipn, LFL2; clear -N NLE NC0 A5; lia).
      apply junk_merge; [| | clear; lia | clear -NEWB; lia].
      + pose proof (u32arr_skipn m' FA _ (Z.to_nat (nf + ncnt - n)) AR2 ltac:(rewrite length_map, LFL2; clear -N NLE NC0 A5; lia)) as SK.
        replace (FA + 4 * Z.of_nat (Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt - n)) in SK by (clear -N NLE NC0 A5; lia).
        rewrite skipn_map in SK. apply junk_of_u32arr in SK. rewrite length_map in SK. exact SK.
      + rewrite length_skipn, LFL2. replace (FA + 4 * (nf + ncnt - n) + 4 * Z.of_nat (Z.to_nat (nf + ncnt) - Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt)) by (clear -N NLE NC0 A5; lia).
        exact JR.
    -
      assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_shmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite <- ?SHE4; clear -SH12 SHE4 A5 A6 M8c; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia
                      | apply ICW_far; clear -SHE4 SH5 SH6 SH13 SH8 SH1 SH2 SH3 SH12 TL1u; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia]. }
      destruct FD as [Emfa|(_ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply junk_of_fill; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (SLOTK : forall k, 0 <= k -> aslot_addr L c k = RB + k * S /\ (k < nd -> k * S + S <= au) /\ (nd <= k < nd + ncnt -> au <= k * S /\ k * S + S <= au + ncnt * S)
                            /\ shad (aslot_addr L c k) = shad RB + shlen (k * S) /\ shad (aslot_addr L c k) + shlen S = shad RB + shlen (k * S + S)).
  { intros k Hk. assert (E : aslot_addr L c k = RB + k * S) by reflexivity. rewrite E.
    assert (KS8 : (k * S) mod 8 = 0) by (clear -M8f Hk; Z.div_mod_to_equations; nia).
    split; [reflexivity|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|].
    rewrite !shad_div, !shlen_div. clear -KS8 M8g M8f Hk SZ16. Z.div_mod_to_equations. nia. }
  assert (NEWFREE : forall k, nd <= k -> busy_of X c k = None).
  { intros k Hk. destruct (busy_of X c k) as [b|] eqn:Bk; [exfalso| reflexivity].
    apply busy_of_In_slots in Bk. specialize (RANGE k ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Bk)).
    unfold ndist in RANGE. fold S au nd in RANGE. clear -RANGE Hk. lia. }
  assert (SLc : aslots L st_r X' m' c).
  { unfold aslots. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & _ & _).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        destruct (busy_of X c k) as [b|] eqn:Bk.
        * destruct (busy_of_Some_facts X c k b Bk) as (BIn & BC & BK).
          eapply (aslot_busy_frame L _ m m' MUALL WMALL); [exact SL | exact (awf_fits L st X b WF BIn) |].
          unfold xb_alloc. rewrite BC, BK, AE. fold S.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
        * eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros _. rewrite AE.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). rewrite AE.
        eapply junk_sub; [exact BIGJ | clear -KHI | clear -KHI NCS | clear -SZ16]; lia.
    - eapply junk_sub; [exact BIGJ | clear -NC0 SZ16; nia | clear; lia | clear -NCS; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { unfold aslot_shadow. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & SHA & SHB).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SSL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia).
        assert (B : shad RB + shlen (k * S + S) <= SHU0 /\ 2201439137792 <= shad RB + shlen (k * S)).
        { rewrite <- SHE3. rewrite !shlen_div. clear -KLO A1 SH1 Hk SZ16. Z.div_mod_to_equations. nia. }
        rewrite SHA.
        apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); [clear -B; lia | rewrite <- SHA, SHB; clear -B; lia | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia]
                      | apply ICW_far; rewrite <- SHA, SHB; clear -B SHA SHB TL1u TL4u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). cbn [slot_shadow_bytes]. rewrite SHA.
        eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia].
        * rewrite shad_div, (shad_div RB), shlen_div. clear -KHI M8g M8e A1. Z.div_mod_to_equations. nia.
        * rewrite (shad_div (RB + au)), (shad_div RB), !shlen_div. clear -KHI NCS M8g M8e M8f A1 SZ16 Hk. Z.div_mod_to_equations. nia.
    - eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -NCS; Z.div_mod_to_equations; lia].
      + rewrite !shad_div. clear -NC0 SZ16 M8g M8e; Z.div_mod_to_equations; nia.
      + rewrite !shad_div, !shlen_div. clear -NC0 NCS SZ16 M8g M8e M8f A1; Z.div_mod_to_equations; nia. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec]. fold RB FA. split; [exact AZU' | exact AZF']. }
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_cache].
    unfold max_count. rewrite CIR. exists (skipn (Z.to_nat n) chunks0).
    split; [exact REC'|]. split.
    - subst ca. rewrite <- skipn_map. exact CH'.
    - subst ca. rewrite !length_skipn, LFL2, LCH. clear -N NLE NC0 A5; lia. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. change (aregion L c) with RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).

    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                        | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 SH2; lia.
      - eapply (RK_shhigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD10 SH13; lia. }
    assert (DJI : disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xr_cls_ne X c _ _ c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|].
        destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xr_cls_ne X c _ _ c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC N; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *.
      change (aregion L c) with RB in P5, P4. change (c_allocated_user (get_cls st c)) with au in P4, Q1. change (c_mapped_user (get_cls st c)) with mu in Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). change (aregion L c) with RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2 A1; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2792) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|H3]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    pose proof CL1 as CL1'; unfold sclr, KLS in CL1'.
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1' CL2 CL5 SCX; lia. }

  assert (WF' : awf L st_r X').
  { subst st_r X' fr ca FL2. apply awf_refill; first [exact WF | exact HC | exact CNT0 | exact MUB | exact MUM' | exact NC0 | exact NCS | exact NEWB | exact NEWM | exact NEWMOD | exact N2 | clear -N NLE; lia]. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  assert (EFemb : a_emb st_r = a_emb st) by (subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity).
  assert (EFexh : a_exh st_r = a_exh st) by (subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity).
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 24 8); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J24 _].
        eapply junk_frame; [exact J24 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + replace (al_t L + 2768 + 24) with (al_t L + 2792) by (clear; lia). pose proof (junk_of_cells m' _ _ STM') as J. cbn in J. exact J.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  assert (SHX : shlen 4294967296 = 536870912 /\ shad (RB + 4294967296) = shad RB + 536870912 /\ SHF1 <= shad RB + 536870912).
  { split; [rewrite shlen_div; reflexivity|]. clear -SH9 SH10 SH13. split; lia. }
  destruct SHX as (SX1 & SX2 & SX3).
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 672, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (RB + mu, RB + 4294967296); (SHU0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SX3 SH2 SH3 SH12 SH5 SH6 MUB NEWB A5 A1 CAE RBE FAE HC N.
      repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (QU : quar_untouched L X WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]). subst X'. unfold xr. cbn [x_busy].
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : ah_quar H L st_r X' m').
  { eapply (hq_frame _ HL L st st_r X X' m m'); [exact HQ | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC MUB A1; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [exact EFemb| exact EFexh]. }
  assert (HD' : ah_depot H L m').
  { eapply (hd_frame _ HL L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREPns H L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GPA & GSC & GPSH).
    unfold arng. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
    split; [| split; [rewrite EF8; exact GPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact GSC| exact GPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec].
      destruct (GC c HC) as (R1 & R2 & R3 & R4).
      change (aregion L c) with RB in R1, R2 |- *. change (afreearr L c) with FA in R3, R4 |- *.
      change (c_mapped_user (get_cls st c)) with mu in R1, R2. change (c_mapped_free_array (get_cls st c)) with mfa in R3, R4.
      split; [| split; [| split]].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R1|].
        replace mu' with (mu + (mu' - mu)) by (clear; lia). apply rng_merge; [exact BW | clear -A1; lia | clear -MUB; lia | exact R1 | exact RU].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R2|].
        replace (shlen mu') with (shlen mu + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A1; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia | exact R2 |].
        rewrite SHE3. exact RSU.
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact R3 | exact RF].
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R4|].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact R4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (GC c' Hc'). }

  exists X', WH.
  split; [exact AR'|]. split; [exact MUH|]. split; [exact SU|].
  split. {
    intros C24. unfold c6_untouched. subst WH.
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_ri L c _ _ ALO HC); [clear -RIE; lia| clear -RIE; lia| right; right; exact C24] |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.RIP; clear -RSP RBE HC MUB A1; unfold K_NUM_CLASSES in HC; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  split; [exact SSM|].
  split; [exact ARNG'|]. split; [exact CIR|].
  split; [rewrite GR; unfold max_count; rewrite CIR; cbn [c_count rrec]; subst n; reflexivity|].
  split; [unfold max_count; rewrite CIR; subst n; clear -N; lia|].
  split; [subst X'; reflexivity|].
  split; [intros c' NE; subst X'; apply xr_cls_ne; exact NE|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|]. split; [exact EF7|]. split; [exact EF8|].
  split; [exact GO|].
  split; [| exact WMALL].
  eapply munch_weaken; [| exact MUH]. unfold sub_fp. intros x Hx. subst WH. unfold K_REGION in Hx. change (2^32) with 4294967296 in Hx.
  rewrite SX1 in Hx. cbn [outside] in Hx |- *. clear -Hx. lia.
Qed.

Lemma refill_store : store_refill_stmt.
Proof.
  unfold store_refill_stmt.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC C24 CNT0 CEIL LO CH LCH RR.
  pose proof (refill_store_ns L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR) as S0. cbv zeta in S0 |- *.
  destruct S0 as (X' & WH & ARNS & MUH & SU & C6U & SSX & REST).
  exists X'. split; [| exact REST].
  apply AREP_split. split; [exact ARNS|].
  destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
  destruct REST as (_ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GO & _ & WM).
  eapply (hs_frame _ HL L st _ X X' m m' WH); [exact HS| exact MUH| exact WM| exact SU| exact (C6U C24)| exact SSX].
Qed.

Section WithStore.
Hypothesis STORE : store_refill_stmt.

Theorem arefill_from_store : refill_stmt H.
Proof.
  unfold refill_stmt.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC24 CNT0 RSTK KONT.
  assert (HC : 1 <= c < K_NUM_CLASSES) by (rewrite HC24; unfold K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  unfold aflag_cell in EXH. replace (c =? K_BATCH_CLASS) with true in EXH by (symmetry; apply Z.eqb_eq; exact HC24).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.

  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (STORE L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC HC24 CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  eapply KONT. unfold ARefill_iface.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End WithStore.

Theorem arefillP : refill_stmt H.
Proof. exact (arefill_from_store refill_store). Qed.
End RefillP.
End CANSEC1.
End ARefillP.

From Stdlib Require Import Sorting.Permutation.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AKitQ AKitR AQConst ARepQ ARepQP ARepQR AFreeRep AFreeGeo.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AFreeRead.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require ARecRep ARepQD.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_amaybe.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_acdrain.
From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require F_arecyc1.
Module ARecyc1P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARecRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQD. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_acdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecyc1.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (SHUB, SHUB + gr); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' AB S rz gr SHLO SHUB SHHI SHF0 SHF1 : Z).
Let HB := AB + rz - 16.
Definition reckf : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6483968 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (RB <= AB /\ AB + S <= RB + au /\ 16 <= rz /\ rz <= S)
  /\ (2201439137792 <= SHLO /\ SHLO <= SHUB /\ 0 <= gr /\ SHUB + gr <= SHHI /\ SHHI <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf.

Ltac kind := pose proof KF as KF'; unfold reckf, AIMG_HI in *; subst HB;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_ab & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_obj : forall A k, ((6483968 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.

Lemma RK_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  (A + k <= AB \/ AB + 8 <= A) -> (A + k <= HB \/ HB + 4 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHUB \/ SHUB + gr <= A) -> (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
End Kinds.

Lemma upd_app_right : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
Lemma upd_app_left : forall {X} (l1 l2 : list X) i x, (i < length l1)%nat -> upd (l1 ++ l2) i x = upd l1 i x ++ l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. rewrite IH by lia. reflexivity.
Qed.

Lemma AQdr_drop_prim : forall R L st X m c k n b1 ctx l1 l2 drained pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_drop R pend') 0 0 L st (xrec st X c k l1 l2 drained) m.
Proof.
  intros R L st X m c k n b1 ctx l1 l2 drained pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP XB WF.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_drop_prim L st st X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF eq_refl eq_refl).
Qed.

Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Definition AHr (R : qrconc) (cs : list achunk) : aholes := mkAHoles (AQdr R 0 0) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

Definition rec_W (L : alayout) (sp : Z) (c k n nf mfa mfa' : Z) : list (Z * Z) :=
  let AB := aslot_addr L c k in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z)
  ++ cd_W L sp c nf mfa mfa'.

Definition arecyc1_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk) (c k n lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_rec1_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (pend' : list (achunk * Z)) (cs : list achunk) (c k n b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, k) :: pend' -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  recyc1_ret L RNG sp st c k n b1 ctx lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Lemma read_qchunk : forall L st X m c k n b1 ctx l1 l2,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  aslots L st X m c -> aslot_shadow L st X m c ->
  let S := size_of_class c in let AB := aslot_addr L c k in let rz := rz_size n in let UB := AB + rz in
     rw_cells asegs m (UB - 16) [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ junk_at m UB (S - rz)
  /\ (16 < rz -> rw_cells asegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz - 32))
  /\ rw_cells asegs m (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)))]
  /\ rw_cells asegs m (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)))]
  /\ rw_cells asegs m (shad UB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n)))].
Proof.
  intros L st X m c k n b1 ctx l1 l2 ALO WF XB [SL _] [SH _]. cbv zeta.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  destruct SL as (LH & [stb [E HDR]] & UJ). injection E as <-.
  replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exact UJ|]. split; [exact LH|].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & _).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) ltac:(apply repeat_length) ltac:(apply repeat_length) SH) as (SHA & SHU & SHR).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.

Lemma pend_head_busy : forall L st X R m c n k pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  exists b1 ctx l1 l2, x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Proof.
  intros L st X R m c n k pend' (_ & _ & _ & _ & _ & _ & CP & _) EP.
  destruct CP as (_ & _ & OK & _). unfold qr_entries in OK. rewrite EP in OK.
  assert (HOK : qentry_ok X (CPrim c n, k)).
  { eapply (proj1 (Forall_forall _ _) OK). rewrite !in_app_iff. right. right. right. left. reflexivity. }
  unfold qentry_ok in HOK. cbn [fst snd] in HOK. destruct HOK as (b1 & ctx & Hin).
  destruct (in_split _ _ Hin) as (l1 & l2 & E). exists b1, ctx, l1, l2. exact E.
Qed.

Lemma nf_bound : forall L st X c, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c
  /\ 4 * (c_num_freed (get_cls st c) + max_cached c / 2) <= K_FREEARR_MAX.
Proof.
  intros L st X c WF HC. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  split; [exact NFA|].
  pose proof (size_of_class_pos c HC) as [SZ _]. pose proof (ARecRep.max_cached_range c) as (_ & MC & _).
  unfold K_FREEARR_MAX, K_FREEARR_OFF in *. generalize NFA A1 A2 SZ MC. clear. intros. Z.div_mod_to_equations. nia.
Qed.

Lemma cache_vals_lt : forall L st X c tail, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  Forall (fun w : word => bv_unsigned w < 2^31)
         (firstn (Z.to_nat (c_count (get_cls st c))) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail)).
Proof.
  intros L st X c tail WF HC LEN. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  rewrite firstn_app, length_map. replace (Z.to_nat (c_count (get_cls st c)) - length (xc_cache (x_cls X c)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply Forall_forall. intros w Hw.
  assert (Hw' : In w (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)))).
  { rewrite <- (firstn_skipn (Z.to_nat (c_count (get_cls st c))) (map _ _)). apply in_app_iff. left. exact Hw. }
  apply in_map_iff in Hw'. destruct Hw' as (k0 & <- & Hk).
  pose proof (RANGE k0 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
  assert (B : 0 <= acompact c k0 < 2^28).
  { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
  rewrite unsigned_lit; lia.
Qed.

Lemma rec1_store : store_rec1_stmt.
Proof.
  unfold store_rec1_stmt.
  intros L RNG RNG' sp m m' st stX X R pend' cs c k n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.max_cached_range c) as (MCR & MCH & MCE).

  destruct RR as (m1 & MU1 & WM1 & CDR & MAG' & HDR' & SHU'). cbv zeta in MU1.
  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *. set (rz := rz_size n) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.

  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).

  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).

  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2]. fold rz in RZ1, RZ2.
  pose proof (rounded_size_facts n (proj1 N0)) as (RS1 & RS2 & RS3 & RS4 & RS5).
  assert (FITr : rz + n <= S /\ rz <= S) by (subst S rz; clear -FIT0 RS1 RZ1 N0; lia). destruct FITr as [FITr RZS].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & SG2 & GE & SG0 & SGF & SHLO1 & SHHI1 & SHR1 & SHR2).
  fold S AB rz RB mu in SE, SG2, GE, SG0, SGF, SHLO1, SHHI1, SHR1, SHR2.

  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHUB := shad (AB + rz)) in *. set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA /\ SHUB = shad AB + shlen rz).
  { subst SHUB SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB rz half cnt nf' cnt'.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 SE RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16 & SHE0).
  assert (KF : reckf (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' AB S rz (granules n) (shad AB) SHUB (shad AB + shlen S) SHF0 SHF1).
  { unfold reckf. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL1u TL4u TL2 TL4 CL1 CL1u CL2 CL3 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 RZ1 RZS SHLO1 SE SG2 SG0 GE SGF SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). unfold granules in *.
    unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].     }
  assert (MUALL : munch (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst AB rz SHUB. cbn [outside] in H13 |- *.
      pose proof (bv_unsigned_in_range 64 sp). clear -H13 H. lia.
    - unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
      apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
      subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  destruct (read_qchunk L st X m c k n b1 ctx l1 l2 ALO WF XB SLOTS0 SSH0) as (_ & UJ & LH & SHA & _ & SHR).
  fold S AB rz in UJ, LH, SHA, SHR. rewrite <- ?SHE0 in SHR.
  assert (HBE : AB + rz + -16 = AB + rz - 16) by (clear; lia).

  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  rewrite CPT in CH'.

  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }

  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply (aflag_cell_frame L _ _ _ MUALL WMALL); [exact EXH|]. fold RI.
    apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ SHUB + granules n <= shad FA /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SGF SHE0 SG0 GE. lia. }
  destruct FAB as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6 & FB7).
  assert (SHB : shad RB <= SHUB /\ SHF1 <= shad (RB + 4294967296) /\ 0 <= granules n) by (clear -SH13 SHE0 SG2 SH5 FB2 GE SG0 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  destruct SHB as (SB1 & SB2 & SB3).

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB3 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB2 SHE4 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (HBK : 16 < rz -> 32 <= rz) by (intros H16; clear -RZ2 H16; Z.div_mod_to_equations; lia).
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16 DJ RZ1 RZS; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16 RZ1 RZS; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). fold S AB.

      assert (UJ' : junk_at m' (AB + rz) (S - rz)).
      { eapply junk_frame; [exact UJ | exact MUALL | exact WMALL |]. intros POS.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
      pose proof (junk_of_cells m' _ _ HDR') as JH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JH. fold AB rz in JH. rewrite ?HBE in JH.
      change (Z.of_nat 16) with 16 in JH.
      destruct (Z.lt_ge_cases 16 rz) as [RZG|RZE].
      + specialize (HBK RZG). destruct (LH RZG) as [_ LJ]. pose proof (junk_of_cells m' _ _ (MAG' RZG)) as JM. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JM. change (Z.of_nat 16) with 16 in JM.
        assert (LJ' : junk_at m' (AB + 16) (rz - 32)).
        { eapply junk_frame; [exact LJ | exact MUALL | exact WMALL |]. intros POS.
          apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
        replace S with (16 + ((rz - 32) + (16 + (S - rz)))) by (clear; lia).
        apply junk_merge; [exact JM | | clear; lia | clear -HBK RZS; lia].
        apply junk_merge; [exact LJ' | | clear -HBK; lia | clear -RZS; lia].
        replace (AB + 16 + (rz - 32)) with (AB + rz - 16) by (clear; lia).
        apply junk_merge; [exact JH | | clear; lia | clear -RZS; lia].
        replace (AB + rz - 16 + 16) with (AB + rz) by (clear; lia). exact UJ'.
      + assert (RZ16 : rz = 16) by (clear -RZE RZ1; lia). rewrite RZ16 in JH, UJ'.
        replace (AB + 16 - 16) with AB in JH by (clear; lia).
        replace S with (16 + (S - 16)) by (clear; lia). apply junk_merge; [exact JH | exact UJ' | clear; lia | clear -RZS RZ16; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)
                  /\ (shad (aslot_addr L c k') + shlen S <= shad AB \/ shad AB + shlen S <= shad (aslot_addr L c k'))).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 DJ AL' AL16 SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4 SGF SHE0 SG2; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB1 FB2 FB3 FB4 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH10 SH11 SH12 SH13 SH14 SH15 SGF SHE0 SG2 SG0 GE; lia
                                | apply ICW_far; clear -POS FB2 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      assert (SHA' : rw_cells asegs m' (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen rz)))]).
      { eapply cells_frame; [exact SHA | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SG2; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 FB5 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 GE SG0; lia]. }
      assert (SHR' : rw_cells asegs m' (SHUB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { eapply cells_frame; [exact SHR | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SGF GE SG0; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF GE SG0 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 SH12 SH13; lia]. }
      assert (C2pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz))) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (granules n)))]).
      { rewrite Z2Nat.id by (clear -SG2; lia). rewrite <- SHE0. exact SHU'. }
      pose proof (cb_app m' _ _ _ _ _ SHA' C2pre) as C2.
      assert (C3pre : rw_cells asegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { replace (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) with (SHUB + granules n) by (rewrite SHE0; clear -SG2 GE SG0; lia). exact SHR'. }
      pose proof (cb_app m' _ _ _ _ _ C2 C3pre) as C3.
      rewrite <- !repeat_app in C3.
      replace (Z.to_nat (shlen rz) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen rz - granules n))%nat with (Z.to_nat (shlen S)) in C3 by (clear -SG2 GE SG0 SGF; lia).
      exact C3. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 SGF SHE0 SG2; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2; lia.
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2 SGF FB3; lia. }
    assert (DJI : disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ ((xb_alloc L b + size_of_class (xb_class b) <= RB + mu /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ AB + S <= xb_alloc L b))
          \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - assert (NK : xb_slot b <> k) by (intros EK; exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb EC EK)).
      pose proof (slots_disjoint L c (xb_slot b) k (proj1 KB) (proj1 KR) NK ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. split; [clear -P4 A1; lia| exact DJ].
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL2 CL3 CL5 SCX; unfold AIMG_HI in *; lia. }

  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BQuar c k n b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (AB, AB + S);
              (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_drop R pend') 0 0 L st X' m) by (subst X'; eapply AQdr_drop_prim; [exact HQ | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_drop R pend') 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity| subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity]. }
  assert (HS' : ASECc cs L st_r X' m').
  {
    set (WS3 := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 68); (RI + 69, RI + 128); (AB, AB + S);
                (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
    assert (MUS3 : munch WS3 m m').
    { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WS3. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3a & O3b & O4 & O5 & O6 & O7 & _).
      apply outside_app. split.
      - cbn [outside]. clear -O1 O2 O3a O3b O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
        pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
      - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
    eapply (hs_frame _ (HL (qr_drop R pend') cs) L st st_r X X' m m' WS3); [exact HS | exact MUS3 | exact WMALL | | | exact SSM].
    - unfold sec_untouched, aknown. subst WS3. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
      apply Forall_nil.
    - unfold c6_untouched. subst WS3. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      assert (HCk : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -HC; lia).
      assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
      { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
        clear -RSP ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_ri L c _ _ ALO HCk); [clear -RIE; subst RI; lia| clear -RIE; subst RI; lia| left; subst RI; clear; lia] |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_ri L c _ _ ALO HCk); [clear -RIE; subst RI; lia| clear -RIE; subst RI; lia| right; left; subst RI; clear; lia] |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.RIP; clear -RSP RBE HC G5 G6; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.RIP; clear -RSP RBE FAE HC A5; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5 SHBx; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5 SHBx; lia |].
      apply Forall_nil. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_drop R pend') cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }

  exists X', mfa'.
  split. { unfold rec_W. cbv zeta. fold AB rz. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H5 _]. cbn [outside] in H5 |- *. subst SHUB. clear -H5. lia.
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [_ HW]. exact HW. }
  split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BQuar c k n b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

Theorem arecyc1 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells asegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom asegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R pend' cs
         c kk n CBA lo cbs ALO ARNG AR EP MI ST CEIL LO TP Ha0 Ha1 CBC CB0 CB1 RSTK RCB KONT.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct (pend_head_busy L st X R m c n kk pend' HQ EP) as (b1 & ctx & l1 & l2 & XB).
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  destruct (read_qchunk L st X m c kk n b1 ctx l1 l2 ALO WF XB SLOTS SSH) as (HDR & UJ & MAG & SHA & SHU & SHR).
  destruct (slot_rng L st X c kk ALO WF HC KR RNG ARNG) as [RAB RSAB].
  pose proof (slot_geo L st X c kk ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).

  eapply (recyc1_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c kk n b1 ctx CBA lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta cbs (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))));
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ CBA _ => exact CBC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- rw_cells _ _ (aslot_addr _ _ _ + rz_size _ - 16) _ => exact HDR
       | |- 16 < _ -> _ => intros H16; exact (proj1 (MAG H16))
       | |- rw_cells _ _ (shad _) _ => exact SHU
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ CBA _ => exact RCB
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (aslot_addr _ _ _) _ => exact RAB
       | |- rng _ (shad (aslot_addr _ _ _)) _ => exact RSAB
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | rewrite Ha1; unfold qhdr; reflexivity]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- (_ + 1) * _ <= _ =>
           unfold ndist in KR; transitivity (c_allocated_user (get_cls st c) / size_of_class c * size_of_class c);
           [apply Z.mul_le_mono_nonneg_r; [clear -S1; lia| clear -KR; lia]
           | rewrite Z.mul_comm; pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (size_of_class c) ltac:(clear -S1; lia)); clear -A1 H; lia]
       | |- 1 <= _ => first [assumption | idtac]; destruct (BUSY (bany BQuar c kk n b1 ctx) ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]; cbn in M; clear -M; lia
       | |- rz_size _ + _ <= _ => pose proof (rounded_size_ge n); clear -FIT0 H; lia
       | |- 0 <= _ < _ => first [assumption | clear -CTX0; lia]
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- 0 <= _ => first [assumption | exact (proj1 KR)]
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.

  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (rec1_store L RNG RNG' sp m m' st stX X R pend' cs c kk n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & MU1 & AU1 & XS & XL).
  destruct RR as (m1 & _ & _ & CDR & _). destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold arecyc1_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|]. split; [exact MU1|]. split; [exact AU1|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
End ARecyc1P.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW Require AEmbFrame.
Module ARefillP_e.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSECE. Context {rc : runConstT} {ov : annOV}.
Section RefillPE.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Definition refill_ret_e (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  ARefill_iface.refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms'
  /\ a_emb st_r = a_emb st /\ a_exh st_r = a_exh st.

Definition refill_stmt_e : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  c = K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_r X' RNG' ms', refill_ret_e L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x41b70) fc None m (seg_rom asegs)).

Theorem arefillP_e : refill_stmt_e.
Proof.
  unfold refill_stmt_e.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC24 CNT0 RSTK KONT.
  assert (HC : 1 <= c < K_NUM_CLASSES) by (rewrite HC24; unfold K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  unfold aflag_cell in EXH. replace (c =? K_BATCH_CLASS) with true in EXH by (symmetry; apply Z.eqb_eq; exact HC24).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.

  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (refill_store H HL L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC HC24 CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST2E & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  assert (EMB2 : a_emb st2 = a_emb st) by (destruct ST2E as [E|E]; rewrite E; exact (init_cache_emb st)).
  assert (EXH2 : a_exh st2 = a_exh st) by (destruct ST2E as [E|E]; rewrite E; unfold init_cache; destruct (a_cinit st); reflexivity).
  eapply KONT. unfold refill_ret_e. split; [| split; [exact EMB2| exact EXH2]].
  unfold ARefill_iface.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End RefillPE.
End CANSECE.
End ARefillP_e.

Module ACdeallocP.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQR. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARecRep. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQD. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.F_acdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecyc1. Import ARecyc1P.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6483968 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6483968 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6483968 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_obj : forall A k, ((6483968 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.

Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.

Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m' /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr asegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono asegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Lemma cd24_store : store_cd24_stmt.
Proof.
  unfold store_cd24_stmt.
  intros L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  set (c := K_BATCH_CLASS) in *. set (k := kb) in *.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.max_cached_range c) as (MCR & MCH & MCE).

  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.

  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).

  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).

  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.

  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].     }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.

  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }

  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply (aflag_cell_frame L _ _ _ MUALL WMALL); [exact EXH|]. fold RI.
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  destruct FAB as (FB1 & FB2 & FB4 & FB5 & FB6 & FB7).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr asegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.

      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6483968 ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }

  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity| subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity]. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | | exact SSM].

    unfold c6_untouched. subst WH. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    assert (HCk : 1 <= c < K_NUM_CLASSES) by (unfold c, K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
    assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
    { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
      clear -RSP ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_ri L c _ _ ALO HCk); [subst RI; clear; lia| subst RI; clear; lia| right; right; reflexivity] |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.RIP; clear -RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5 SHBx; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }

  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  destruct (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) as (b & Hb & Sb & Cb & Kb).
  destruct (in_split _ _ Hb) as (l1 & l2 & E). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv asegs m ->
  stk asegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS asegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS asegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom asegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs
         kb lo ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  set (c := K_BATCH_CLASS) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr ARecyc1P.AHr] in HQ, HS, HD.
  destruct (pendb_busy L st X R m kb HQ EB) as (nb & b1 & ctx & l1 & l2 & XB). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  pose proof (slot_geo L st X c kb ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).

  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.

  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  destruct (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
End ACdeallocP.

From OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW Require BImg.
Module TwinB.
Import stdpp.gmap.

Module ARefillP.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AExh.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Definition newslots (nd : Z) (n : nat) : list Z := rev (map (fun j => nd + Z.of_nat j) (seq 0 n)).

Lemma newslots_length : forall nd n, length (newslots nd n) = n.
Proof. intros. unfold newslots. rewrite length_rev, length_map, length_seq. reflexivity. Qed.

Lemma newslots_In : forall nd n k, In k (newslots nd n) <-> nd <= k < nd + Z.of_nat n.
Proof.
  intros nd n k. unfold newslots. rewrite <- in_rev, in_map_iff. split.
  - intros (j & <- & Hj). apply in_seq in Hj. lia.
  - intros Hk. exists (Z.to_nat (k - nd)). split; [lia|]. apply in_seq. lia.
Qed.

Lemma newslots_NoDup : forall nd n, List.NoDup (newslots nd n).
Proof.
  intros nd n. unfold newslots. apply NoDup_rev. apply NoDup_map_NoDup_ForallPairs; [| apply seq_NoDup].
  intros a b _ _ E. lia.
Qed.

Lemma map_cw_newslots : forall c nd n, 1 <= c < K_NUM_CLASSES ->
  map (fun k => Z_to_bv 64 (acompact c k)) (newslots nd n) = fvals (nd * size_of_class c) (size_of_class c) n.
Proof.
  intros c nd n Hc. pose proof (size_of_class_facts c Hc) as [S1 S3].
  unfold newslots, fvals. rewrite map_rev, map_map. f_equal. apply map_ext. intros j.
  f_equal. unfold acompact. rewrite Z.shiftr_div_pow2 by lia. change (2^4) with 16.
  generalize S1 S3; clear; intros. Z.div_mod_to_equations. nia.
Qed.

Lemma NoDup_bound_length : forall (l : list Z) n, List.NoDup l -> (forall k, In k l -> 0 <= k < n) -> 0 <= n -> Z.of_nat (length l) <= n.
Proof.
  intros l n ND B N.
  assert (INCL : incl (map Z.to_nat l) (seq 0 (Z.to_nat n))).
  { intros x Hx. apply in_map_iff in Hx. destruct Hx as (k & <- & Hk). apply in_seq. specialize (B k Hk). lia. }
  apply NoDup_incl_length in INCL.
  - rewrite length_map, length_seq in INCL. lia.
  - apply NoDup_map_NoDup_ForallPairs; [| exact ND]. intros a b Ha Hb E. pose proof (B a Ha). pose proof (B b Hb). lia.
Qed.

Lemma nodup_app : forall {A} (a b : list A), List.NoDup a -> List.NoDup b -> (forall x, In x a -> ~ In x b) -> List.NoDup (a ++ b).
Proof.
  intros A a b NA NB D. induction a as [|x a IH]; cbn; [exact NB|].
  inversion NA; subst. constructor.
  - rewrite in_app_iff. intros [Hx|Hx]; [exact (H1 Hx)|]. exact (D x (or_introl eq_refl) Hx).
  - apply IH; [exact H2|]. intros y Hy. apply D. right; exact Hy.
Qed.

Lemma junk_sub : forall m A n A' n', junk_at m A n -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> junk_at m A' n'.
Proof.
  intros m A n A' n' J H1 H2 H3.
  destruct (junk_split m A (A' - A) (n - (A' - A)) ltac:(replace (A' - A + (n - (A' - A))) with n by lia; exact J) ltac:(lia) ltac:(lia)) as [_ J2].
  replace (A + (A' - A)) with A' in J2 by lia.
  destruct (junk_split m A' n' (n - (A' - A) - n') ltac:(replace (n' + (n - (A' - A) - n')) with (n - (A' - A)) by lia; exact J2) ltac:(lia) ltac:(lia)) as [J3 _].
  exact J3.
Qed.

Lemma fill_sub : forall m A n A' n' v, fill_at m A n v -> A <= A' -> A' + n' <= A + n -> 0 <= n' -> fill_at m A' n' v.
Proof.
  intros m A n A' n' v F H1 H2 H3. unfold fill_at in *.
  pose proof (rw_cells_split_CB bsegs m A [] (Z.to_nat n) (repeat (Z_to_bv 8 v) (Z.to_nat n)) [] [Z.to_nat (A' - A); Z.to_nat n'; Z.to_nat (n - (A' - A) - n')] F ltac:(cbn; lia)) as SP.
  cbn [app mk_CB_cells] in SP.
  rewrite !skipn_repeat' in SP. rewrite (firstn_repeat' _ (Z.to_nat n')) in SP by lia.
  apply (proj1 (rw_cells_app bsegs m A [_] [_; _])) in SP. destruct SP as [_ SP].
  apply (proj1 (rw_cells_app bsegs m _ [_] [_])) in SP. destruct SP as [SP _].
  cbn [cells_size csize Nat.add] in SP. rewrite Nat.add_0_r, Z2Nat.id in SP by lia.
  replace (A + (A' - A)) with A' in SP by lia. exact SP.
Qed.

Lemma fill_merge : forall m A a b v, fill_at m A a v -> fill_at m (A + a) b v -> 0 <= a -> 0 <= b -> fill_at m A (a + b) v.
Proof.
  intros m A a b v F1 F2 Ha Hb. unfold fill_at in *.
  pose proof (cb_app m A _ _ _ _ F1 ltac:(rewrite Z2Nat.id by lia; exact F2)) as CA.
  rewrite <- repeat_app in CA. replace (Z.to_nat a + Z.to_nat b)%nat with (Z.to_nat (a + b)) in CA by lia. exact CA.
Qed.

Lemma junk_of_u32arr : forall m A ws, u32arr bsegs m A ws -> junk_at m A (4 * Z.of_nat (length ws)).
Proof.
  intros m A ws AR. exists (u32s ws). apply rw_cells_of_u8arr' || idtac.
  pose proof (rw_cells_of_u8arr bsegs m A (u32s ws) (u8arr_of_u32arr bsegs m A ws AR)) as R.
  rewrite u32s_length in R. replace (Z.to_nat (4 * Z.of_nat (length ws))) with (4 * length ws)%nat by lia. exact R.
Qed.

Lemma junk_of_fill : forall m A n v, fill_at m A n v -> junk_at m A n.
Proof. intros m A n v F. eexists. exact F. Qed.

Lemma u32arr_firstn : forall m A ws k, u32arr bsegs m A ws -> (k <= length ws)%nat -> u32arr bsegs m A (firstn k ws).
Proof.
  intros m A ws k [[B0 [B1 B]] [W0 [W1 W]]] K. rewrite u32s_length in B1. split.
  - split; [lia|]. split; [rewrite u32s_length, length_firstn; lia|].
    intros i Hi. rewrite u32s_length, length_firstn in Hi.
    rewrite <- (firstn_skipn k ws) in B. specialize (B i ltac:(rewrite u32s_length, length_app, length_firstn, length_skipn; lia)).
    rewrite u32s_app, nth_error_app1 in B by (rewrite u32s_length, length_firstn; lia). exact B.
  - split; [lia|]. split; [rewrite length_firstn; lia|]. intros i Hi. rewrite length_firstn in Hi. apply W. lia.
Qed.

Definition xr (X : aconc) (c : Z) (fr ca : list Z) : aconc :=
  mkAConc (fun c' => if c' =? c then mkXClass fr ca else x_cls X c') (x_busy X).

Lemma busy_of_In_slots : forall X c k b, busy_of X c k = Some b -> In k (busy_slots X c).
Proof.
  intros X c k b Hb. destruct (busy_of_Some_facts X c k b Hb) as (HIn & HC & HK).
  unfold busy_slots. apply in_map_iff. exists b. split; [exact HK|]. apply filter_In. split; [exact HIn|]. apply Z.eqb_eq. exact HC.
Qed.

Lemma xr_busy_of : forall X c fr ca c' k, busy_of (xr X c fr ca) c' k = busy_of X c' k.
Proof. intros. reflexivity. Qed.
Lemma xr_busy_slots : forall X c fr ca c', busy_slots (xr X c fr ca) c' = busy_slots X c'.
Proof. intros. reflexivity. Qed.
Lemma xr_cls_eq : forall X c fr ca, x_cls (xr X c fr ca) c = mkXClass fr ca.
Proof. intros. unfold xr. cbn. rewrite Z.eqb_refl. reflexivity. Qed.
Lemma xr_cls_ne : forall X c fr ca c', c' <> c -> x_cls (xr X c fr ca) c' = x_cls X c'.
Proof. intros X c fr ca c' NE. unfold xr. cbn. replace (c' =? c) with false by (symmetry; apply Z.eqb_neq; exact NE). reflexivity. Qed.

Lemma alayout_res_disj : forall L, alayout_ok L ->
     (al_ctx L + 65536 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_ctx L)
  /\ (al_t L + 4096 <= al_space_beg L \/ al_space_beg L + K_SPACE_SIZE + K_SPACE_EXTRA <= al_t L).
Proof.
  intros L H. pose proof (ad_ctx_res L H) as D1. pose proof (ad_t_res L H) as D2. pose proof (ao_space L H) as SB.
  pose proof (ao_ctx L H) as C. pose proof (ao_t L H) as T.
  unfold adisj, aobj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472. lia.
Qed.

Lemma region_other_geo : forall L c c', alayout_ok L -> 1 <= c < 32 -> 1 <= c' < 32 -> c' <> c ->
  al_space_beg L <= aregion L c' /\ (aregion L c' + 4294967296 <= aregion L c \/ aregion L c + 4294967296 <= aregion L c') /\ aregion L c' + 4294967296 <= al_space_beg L + 137438953472
  /\ afreearr L c' = aregion L c' + 3758096384 /\ aregion_info L c' = al_space_beg L + 137438953472 + c' * 128 /\ acache_addr L c' = al_t L + 208 + c' * 80
  /\ aregion L c' mod 8 = 0 /\ (shad (aregion L c') + shlen 4294967296 <= shad (aregion L c) \/ shad (aregion L c + 4294967296) <= shad (aregion L c'))
  /\ 2201439137792 <= shad (aregion L c') /\ shad (aregion L c') + shlen 4294967296 <= 17594333495296
  /\ shad (afreearr L c') = shad (aregion L c') + shlen 3758096384.
Proof.
  intros L c c' ALO HC Hc' NE.
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  unfold K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *. change (2^37) with 137438953472 in *.
  unfold afreearr, aregion_info, acache_addr, aregion, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE.
  change (2^32) with 4294967296. change (2^37) with 137438953472.
  assert (Q : exists q, al_space_beg L = 65536 * q) by (exists (al_space_beg L / 65536); Z.div_mod_to_equations; lia).
  destruct Q as [q Hq]. rewrite Hq in *.
  rewrite !shad_div, !shlen_div. unfold ASHOFF.
  replace ((65536 * q + c' * 4294967296) / 8) with (8192 * q + c' * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296) / 8) with (8192 * q + c * 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c * 4294967296 + 4294967296) / 8) with (8192 * q + c * 536870912 + 536870912) by (Z.div_mod_to_equations; lia).
  replace ((65536 * q + c' * 4294967296 + 3758096384) / 8) with (8192 * q + c' * 536870912 + 469762048) by (Z.div_mod_to_equations; lia).
  change (4294967296 / 8) with 536870912. change (3758096384 / 8) with 469762048.
  assert (CC : c' + 1 <= c \/ c + 1 <= c') by lia.
  repeat split; lia.
Qed.

Section RefillP.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Definition store_refill_stmt_ns : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X' WH, AREPns H L st_r X' m' /\ munch WH m m' /\ sec_untouched L WH /\ (c = K_BATCH_CLASS -> c6_untouched L WH) /\ sec_same st st_r
    /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m'.

Definition store_refill_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st st2 : astate) (X : aconc) (c lo : Z) (chunks0 : list word),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  1 <= c < K_NUM_CLASSES -> c = K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  u32arr bsegs m (acache_addr L c + 16) chunks0 -> length chunks0 = 16%nat ->
  refill_ret L RNG sp st c lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) chunks0 (fun j => c_count (get_cls st j)) m st2 RNG' m' ->
  let n := max_cached c / 2 in
  let st_r := put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2 in
  exists X', AREP H L st_r X' m' /\ arng L RNG' st_r
    /\ a_cinit st_r = true /\ c_count (get_cls st_r c) = max_count st_r c / 2 /\ 0 < max_count st_r c / 2
    /\ x_busy X' = x_busy X /\ (forall c', c' <> c -> x_cls X' c' = x_cls X c')
    /\ a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
    /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
    /\ (forall c', c' <> c -> get_cls st_r c' = get_cls st c')
    /\ munch (arefill_W L st c (bv_unsigned sp)) m m' /\ wmono bsegs m m'.

Notation Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n :=
  ([(sp - 672, sp); (RB + mu, RB + mu'); (SHU0, SHU1); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1);
    (t + 2792, t + 2800); (t + 2800, t + 3168); (RI, RI + 8); (RI + 16, RI + 56); (RI + 68, RI + 69); (RI + 72, RI + 80);
    (CA, CA + 4); (CA + 16, CA + 16 + 4 * n)]%Z) (only parsing).

Lemma outside_app : forall l1 l2 x, outside (l1 ++ l2) x <-> outside l1 x /\ outside l2 x.
Proof. intros l1 l2 x. induction l1 as [|[lo hi] l1 IH]; cbn; tauto. Qed.

Lemma dj_app : forall l1 l2 A k, disjoint_from l1 A k -> disjoint_from l2 A k -> disjoint_from (l1 ++ l2) A k.
Proof. intros l1 l2 A k D1 D2. induction l1 as [|[lo hi] l1 IH]; cbn in *; [exact D2|]. destruct D1 as [D1 D1']. split; [exact D1| apply IH; exact D1']. Qed.

Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1 : Z).
Definition rkfacts : Prop :=
     (ATOP <= lo /\ lo <= sp - 672 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6492160 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80 /\ 1 <= n <= 8)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= mu' /\ mu' <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : rkfacts.

Ltac kind := pose proof KF as KF'; unfold rkfacts, AIMG_HI in *; unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in KF';
  destruct KF' as (F_lo & F_t & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_obj : forall A k, (A + k <= 2147446784 \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2792 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 16 + 4 * n <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_slots : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_gap : forall A k, RB + mu' <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 56 <= A) -> (A + k <= RI + 68 \/ RI + 69 <= A) -> (A + k <= RI + 72 \/ RI + 80 <= A) ->
  disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_shlow : forall A k, 2201439137792 <= A -> A + k <= SHU0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shmid : forall A k, SHU1 <= A -> A + k <= SHF0 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
Lemma RK_shhigh : forall A k, SHF1 <= A -> A + k <= 17594333495296 -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.

Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wr sp RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 t RI CA n) A k.
Proof. intros. kind. Qed.
End Kinds.

Definition rrec (mu' au2 nfr mfa' n : Z) : aclass := mkAClass mu' au2 nfr mfa' n.

Lemma init_cache_fields : forall st,
  a_live (init_cache st) = a_live st /\ a_next (init_cache st) = a_next st /\ a_qloc (init_cache st) = a_qloc st
  /\ a_qloc_bytes (init_cache st) = a_qloc_bytes st /\ a_qglob (init_cache st) = a_qglob st /\ a_qglob_bytes (init_cache st) = a_qglob_bytes st
  /\ a_nsec (init_cache st) = a_nsec st /\ a_nres (init_cache st) = a_nres st /\ a_ptr_array (init_cache st) = a_ptr_array st
  /\ a_space_beg (init_cache st) = a_space_beg st /\ a_cinit (init_cache st) = true.
Proof. intros st. unfold init_cache. destruct (a_cinit st) eqn:E; cbn; repeat split; try reflexivity. exact E. Qed.

Lemma put_cls_fields : forall c r st,
  a_live (put_cls c r st) = a_live st /\ a_next (put_cls c r st) = a_next st /\ a_qloc (put_cls c r st) = a_qloc st
  /\ a_qloc_bytes (put_cls c r st) = a_qloc_bytes st /\ a_qglob (put_cls c r st) = a_qglob st /\ a_qglob_bytes (put_cls c r st) = a_qglob_bytes st
  /\ a_nsec (put_cls c r st) = a_nsec st /\ a_nres (put_cls c r st) = a_nres st /\ a_ptr_array (put_cls c r st) = a_ptr_array st
  /\ a_space_beg (put_cls c r st) = a_space_beg st /\ a_cinit (put_cls c r st) = a_cinit st.
Proof. intros. repeat split; reflexivity. Qed.

Lemma awf_refill : forall L st X c mu' ncnt mfa' n,
  let r := get_cls st c in let S := size_of_class c in
  let mu := c_mapped_user r in let au := c_allocated_user r in let nf := c_num_freed r in let mfa := c_mapped_free_array r in
  let nd := ndist st c in let nf2 := nf + ncnt in let au2 := au + ncnt * S in
  let FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt) in
  let st_r := put_cls c (rrec mu' au2 (nf2 - n) mfa' n) (init_cache st) in
  let X' := xr X c (firstn (Z.to_nat (nf2 - n)) FL2) (skipn (Z.to_nat (nf2 - n)) FL2) in
  awf L st X -> 1 <= c < K_NUM_CLASSES -> c_count r = 0 ->
  mu <= mu' <= K_FREEARR_OFF -> mu' mod K_USER_MAP = 0 -> 0 <= ncnt -> au2 <= mu' ->
  4 * nf2 <= mfa' <= K_FREEARR_MAX -> mfa <= mfa' -> mfa' mod K_FREEARR_MAP = 0 ->
  1 <= n <= nf2 -> 2 * n = max_cached c ->
  awf L st_r X'.
Proof.
  intros L st X c mu' ncnt mfa' n. cbv zeta.
  intros WF HC CNT0 MUB MUM NC0 NCS NEWB NEWM NEWMOD N N2.
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  set (st1 := init_cache st) in *.
  set (S := size_of_class c) in *. set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)) in *.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  assert (NDE : nd * S <= c_allocated_user (get_cls st c) < nd * S + S /\ 0 <= nd).
  { subst nd S. unfold ndist. generalize A1 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as [NDE ND0].
  assert (AUE : c_allocated_user (get_cls st c) = nd * S) by (subst nd S; unfold ndist; generalize A3 A1 SZ16 NDE; clear; intros; Z.div_mod_to_equations; nia).
  assert (ND2 : ndist (put_cls c (rrec mu' (c_allocated_user (get_cls st c) + ncnt * S) (c_num_freed (get_cls st c) + ncnt - n) mfa' n) st1) c = nd + ncnt).
  { unfold ndist. rewrite get_cls_put_cls_eq. cbn [c_allocated_user rrec]. fold S. rewrite AUE.
    generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }
  assert (LFL2 : Z.of_nat (length FL2) = c_num_freed (get_cls st c) + ncnt) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0; lia).
  unfold awf.
  cbn [a_space_beg a_ptr_array a_live a_next put_cls set_cls].
  rewrite E10, E9.
  split; [exact SBE|]. split; [exact PAE|]. split; [exact SAL|]. split; [exact SLO|]. split; [exact SHI|].
  split.
  {
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite get_cls_put_cls_eq, xr_cls_eq. cbn [c_mapped_user c_allocated_user c_num_freed c_mapped_free_array c_count rrec xc_free xc_cache]. fold S.
      rewrite ND2. unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      rewrite xr_busy_slots.
      split; [clear -A1 NC0 NCS SZ16; nia|]. split; [exact (proj2 MUB)|]. split.
      { rewrite AUE. rewrite <- Z.mul_add_distr_r. apply Z_mod_mult. }
      split; [exact MUM|]. split; [clear -N NC0 A5; lia|]. split; [clear -NEWB N; lia|]. split; [exact NEWMOD|].
      split; [rewrite length_firstn; clear -LFL2 N NC0 A5; lia|].
      split; [rewrite length_skipn; clear -LFL2 N NC0 A5; lia|].
      split; [clear -N N2; lia|].
      rewrite app_assoc, firstn_skipn.
      split.
      +
        subst FL2. rewrite XC0 in ND. cbn [app] in ND. rewrite <- app_assoc.
        eapply Permutation.Permutation_NoDup; [apply Permutation.Permutation_app_swap_app|].
        apply nodup_app; [apply newslots_NoDup | exact ND |].
        intros x Hx Hx'. apply newslots_In in Hx. rewrite Z2Nat.id in Hx by exact NC0.
        specialize (RANGE x ltac:(rewrite XC0; cbn [app]; exact Hx')). unfold ndist in RANGE. fold S nd in RANGE. clear -Hx RANGE. lia.
      + intros k0 Hk. subst FL2. rewrite <- app_assoc, in_app_iff, in_app_iff in Hk.
        destruct Hk as [Hk|[Hk|Hk]].
        * specialize (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
        * apply newslots_In in Hk. rewrite Z2Nat.id in Hk by exact NC0. clear -Hk ND0; lia.
        * specialize (RANGE k0 ltac:(rewrite XC0; cbn [app]; apply in_app_iff; right; exact Hk)). unfold ndist in RANGE. fold S nd in RANGE. clear -RANGE NC0; lia.
    - rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite (xr_cls_ne X c _ _ c' NE), xr_busy_slots.
      subst st1. rewrite init_cache_cls. unfold ndist. rewrite (get_cls_put_cls_ne c c') by exact NE. rewrite init_cache_cls.
      unfold max_count. cbn [a_cinit put_cls set_cls]. rewrite E11.
      destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
      pose proof (max_cached_range c' ltac:(unfold K_NUM_CLASSES in Hc'; clear -Hc'; lia)) as [MCR' _].
      unfold max_count in BCNTB. unfold ndist in BRANGE.
      repeat lazymatch goal with |- _ /\ _ => split end; try assumption; try (clear -B1 B6 BCNTB MCR'; lia).
      destruct (a_cinit st); clear -BCNTB MCR'; lia. }
  split.
  { intros c' Hc'. rewrite (get_cls_put_cls_ne c c') by (intros ->; exact (Hc' HC)). subst st1. rewrite init_cache_cls. apply OUTC. exact Hc'. }
  cbn [x_busy xr]. rewrite E1, E2.
  split; [exact BUSY|]. split; [exact LIVE|]. split; [exact FRESH|]. exact UNIQ.
Qed.

Lemma refill_store_ns : store_refill_stmt_ns.
Proof.
  unfold store_refill_stmt_ns.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (max_cached_range c ltac:(unfold K_NUM_CLASSES in HC; clear -HC; lia)) as [MCR MCE].
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }

  destruct RR as (m1 & MU1 & WM1 & TR & RECS').
  unfold refill_tail_ret in TR. rewrite !init_cache_cls in TR. cbv zeta in TR.
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & UD & MUB & MUM' & NCE & NC0 & NCS & FD & NEWB & NEWM & NEWMOD & NLE & AR2 & JR
                  & GC2 & ST2E & MUT & WMT & MIT & STT & MTX' & REG' & (bfl & EXH' & EXH0) & STN' & STATS' & LSJ' & STM' & REC' & CH' & AZU' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (n := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (FL2 := xc_free (x_cls X c) ++ newslots nd (Z.to_nat ncnt)).
  set (fr := firstn (Z.to_nat (nf + ncnt - n)) FL2). set (ca := skipn (Z.to_nat (nf + ncnt - n)) FL2).
  set (X' := xr X c fr ca).
  assert (N : 1 <= n <= 8 /\ 2 * n = max_cached c) by (subst n; clear -MCR MCE; Z.div_mod_to_equations; lia). destruct N as [N N2].
  assert (NDE : nd * S <= au < nd * S + S /\ 0 <= nd /\ au = nd * S).
  { subst nd S au. unfold ndist. generalize A1 A3 SZ16; clear; intros. Z.div_mod_to_equations. nia. }
  destruct NDE as (NDE & ND0 & AUE).
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).

  assert (STR : put_cls c (cls_set_count n (cls_set_num_freed (c_num_freed (get_cls st2 c) - n) (get_cls st2 c))) st2
                = put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)).
  { rewrite GC2. cbn [c_num_freed cls_set_num_freed cls_set_count c_mapped_user c_allocated_user c_mapped_free_array c_count]. unfold rrec.
    destruct ST2E as [E|E]; rewrite E at 1; [reflexivity| apply put_cls_put_cls]. }
  set (st_r := put_cls c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) in *. rewrite STR.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (ND2 : ndist st_r c = nd + ncnt).
  { unfold ndist. rewrite GR. cbn [c_allocated_user rrec]. fold S. rewrite AUE. generalize SZ16 ND0 NC0; clear; intros. rewrite <- Z.mul_add_distr_r, Z.div_mul by lia. reflexivity. }

  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.
  set (SHU0 := shad (RB + mu)) in *. set (SHU1 := SHU0 + shlen (mu' - mu)) in *.
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHU1 = shad (RB + mu') /\ SHF1 = shad (FA + mfa') /\ shad RB + shlen mu = SHU0 /\ shad FA + shlen mfa = SHF0
                /\ 2201439137792 <= shad RB /\ shad RB <= SHU0 /\ SHU0 <= SHU1 /\ SHU1 + shlen (3758096384 - mu') = shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ SHU1 <= shad FA /\ SHF1 <= shad (RB + 4294967296)
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296).
  { subst SHU1 SHU0 SHF1 SHF0. rewrite RBE, FAE. rewrite !shad_div, !shlen_div. unfold ASHOFF.
    clear -SP1 SP2 SP3 HC MUB A1 A2 A4 MUM' A5 A6 A7 NEWB NEWM NEWMOD. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE2 & SHE3 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH7 & SH8 & SH12 & SH13 & SH9 & SH10 & SH11).
  assert (KF : rkfacts (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu mu' au nf mfa mfa' n SHU0 SHU1 SHF0 SHF1).
  { unfold rkfacts. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL2 TL4 CL1 CL2 CL3 CL5 HC CAE N SP1 SP2 RBE FAE RIE TSP SCX A1 MUB A5 A6 NEWB NEWM SH1 SH2 SH3 SH5 SH6 SH8 SH12 SH13.
    unfold AIMG_HI in CL3. unfold iclr, AIMG_LO, AIMG_HI in TL4 |- *. repeat split; first [assumption | lia]. }
  assert (MUALL : munch (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MUT]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW]. cbn [outside] in H13 |- *. split; [exact (proj1 H13) | exact HW].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst CA. exact H13. }
  pose proof (wmono_trans _ _ _ _ WM1 WMT) as WMALL.

  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  assert (FLE : map (fun k => Z_to_bv 64 (acompact c k)) FL2 = map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)) ++ fvals au S (Z.to_nat ncnt)).
  { subst FL2. rewrite map_app. f_equal. rewrite AUE. apply map_cw_newslots. unfold K_NUM_CLASSES; exact HC. }
  rewrite <- FLE in AR2, CH'.
  assert (LFL2 : length FL2 = Z.to_nat (nf + ncnt)) by (subst FL2; rewrite length_app, newslots_length; clear -LENF NC0 A5; lia).
  assert (MOD8 : mu mod 8 = 0 /\ mu' mod 8 = 0 /\ mfa mod 8 = 0 /\ mfa' mod 8 = 0 /\ au mod 8 = 0 /\ S mod 8 = 0 /\ RB mod 8 = 0 /\ FA mod 8 = 0).
  { rewrite RBE, FAE, AUE. clear -A4 MUM' A7 NEWMOD SZM SP3 ND0. Z.div_mod_to_equations. nia. }
  destruct MOD8 as (M8a & M8b & M8c & M8d & M8e & M8f & M8g & M8h).

  assert (BIGJ : junk_at m' (RB + au) (mu' - au)).
  { assert (J1 : junk_at m' (RB + au) (mu - au)).
    { eapply junk_frame; [exact UND | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -A1; lia | apply ICW_far; clear -A1 A2 TSP RBE HC; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & ZN & _)].
    - rewrite Emu. exact J1.
    - replace (mu' - au) with ((mu - au) + (mu' - mu)) by (clear; lia). apply junk_merge; [exact J1 | | clear -A1; lia | clear -MUB; lia].
      replace (RB + au + (mu - au)) with (RB + mu) by (clear; lia). eexists. exact ZN. }
  assert (BIGF : fill_at m' (shad (RB + au)) (shlen (mu' - au)) 0xfa).
  { assert (F1 : fill_at m' (shad (RB + au)) (shlen (mu - au)) 0xfa).
    { eapply fill_frame; [exact SUND | exact MUALL | exact WMALL |]. intros _.
      assert (B : shad (RB + au) + shlen (mu - au) <= SHU0 /\ 2201439137792 <= shad (RB + au) /\ 0 <= shlen (mu - au)).
      { subst SHU0. rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -A1 SH1 M8g M8e M8a. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B; lia | apply ICW_far; clear -B TL1u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia]. }
    destruct UD as [Emu|(_ & _ & Emu & _ & FI & _)].
    - rewrite Emu. exact F1.
    - replace (shlen (mu' - au)) with (shlen (mu - au) + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b M8e A1 MUB; Z.div_mod_to_equations; lia).
      apply fill_merge; [exact F1 | | rewrite shlen_div; clear -A1 M8a M8e; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia].
      replace (shad (RB + au) + shlen (mu - au)) with (shad (RB + mu)) by (rewrite !shad_div, shlen_div; clear -A1 M8a M8e M8g; Z.div_mod_to_equations; lia).
      exact FI. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user rrec]. fold S.
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [unfold aflag_cell; destruct (c =? K_BATCH_CLASS) eqn:QB; [apply Z.eqb_eq in QB; rewrite (EXH0 QB) in EXH'; exact EXH'| exact (junk_of_cells m' _ _ EXH')]|].
    destruct (junk_split m (RI + 72) 8 48 RJ56 ltac:(clear; lia) ltac:(clear; lia)) as [_ J48].
    replace 56 with (8 + 48) by reflexivity. apply junk_merge; [| | clear; lia | clear; lia].
    - pose proof (junk_of_cells m' _ _ STN') as J8. cbn in J8. exact J8.
    - eapply junk_frame; [exact J48 | exact MUALL | exact WMALL |]. intros _.
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_free].
    split; [| split].
    - subst fr. rewrite <- firstn_map. apply u32arr_firstn; [exact AR2 | rewrite length_map, LFL2; clear -N NLE NC0 A5; lia].
    - replace (mfa' - 4 * (nf + ncnt - n)) with (4 * Z.of_nat (length (skipn (Z.to_nat (nf + ncnt - n)) FL2)) + (mfa' - 4 * (nf + ncnt)))
        by (rewrite length_skipn, LFL2; clear -N NLE NC0 A5; lia).
      apply junk_merge; [| | clear; lia | clear -NEWB; lia].
      + pose proof (u32arr_skipn m' FA _ (Z.to_nat (nf + ncnt - n)) AR2 ltac:(rewrite length_map, LFL2; clear -N NLE NC0 A5; lia)) as SK.
        replace (FA + 4 * Z.of_nat (Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt - n)) in SK by (clear -N NLE NC0 A5; lia).
        rewrite skipn_map in SK. apply junk_of_u32arr in SK. rewrite length_map in SK. exact SK.
      + rewrite length_skipn, LFL2. replace (FA + 4 * (nf + ncnt - n) + 4 * Z.of_nat (Z.to_nat (nf + ncnt) - Z.to_nat (nf + ncnt - n))) with (FA + 4 * (nf + ncnt)) by (clear -N NLE NC0 A5; lia).
        exact JR.
    -
      assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_shmid _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite <- ?SHE4; clear -SH12 SHE4 A5 A6 M8c; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia
                      | apply ICW_far; clear -SHE4 SH5 SH6 SH13 SH8 SH1 SH2 SH3 SH12 TL1u; rewrite ?shlen_div in *; Z.div_mod_to_equations; lia]. }
      destruct FD as [Emfa|(_ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply junk_of_fill; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (SLOTK : forall k, 0 <= k -> aslot_addr L c k = RB + k * S /\ (k < nd -> k * S + S <= au) /\ (nd <= k < nd + ncnt -> au <= k * S /\ k * S + S <= au + ncnt * S)
                            /\ shad (aslot_addr L c k) = shad RB + shlen (k * S) /\ shad (aslot_addr L c k) + shlen S = shad RB + shlen (k * S + S)).
  { intros k Hk. assert (E : aslot_addr L c k = RB + k * S) by reflexivity. rewrite E.
    assert (KS8 : (k * S) mod 8 = 0) by (clear -M8f Hk; Z.div_mod_to_equations; nia).
    split; [reflexivity|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|]. split; [rewrite AUE; clear -Hk SZ16; intros; nia|].
    rewrite !shad_div, !shlen_div. clear -KS8 M8g M8f Hk SZ16. Z.div_mod_to_equations. nia. }
  assert (NEWFREE : forall k, nd <= k -> busy_of X c k = None).
  { intros k Hk. destruct (busy_of X c k) as [b|] eqn:Bk; [exfalso| reflexivity].
    apply busy_of_In_slots in Bk. specialize (RANGE k ltac:(apply in_app_iff; right; apply in_app_iff; right; exact Bk)).
    unfold ndist in RANGE. fold S au nd in RANGE. clear -RANGE Hk. lia. }
  assert (SLc : aslots L st_r X' m' c).
  { unfold aslots. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & _ & _).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        destruct (busy_of X c k) as [b|] eqn:Bk.
        * destruct (busy_of_Some_facts X c k b Bk) as (BIn & BC & BK).
          eapply (aslot_busy_frame L _ m m' MUALL WMALL); [exact SL | exact (awf_fits L st X b WF BIn) |].
          unfold xb_alloc. rewrite BC, BK, AE. fold S.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
        * eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros _. rewrite AE.
          apply dj_app; [eapply (RK_slots _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -KLO Hk A1 SZ16; nia | apply ICW_far; clear -KLO Hk A1 A2 SZ16 TSP RBE HC; nia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). rewrite AE.
        eapply junk_sub; [exact BIGJ | clear -KHI | clear -KHI NCS | clear -SZ16]; lia.
    - eapply junk_sub; [exact BIGJ | clear -NC0 SZ16; nia | clear; lia | clear -NCS; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { unfold aslot_shadow. cbv zeta. rewrite ND2, GR. cbn [c_allocated_user c_mapped_user rrec]. fold S RB. subst X'. split.
    - intros k Hk. rewrite xr_busy_of. destruct (SLOTK k ltac:(clear -Hk; lia)) as (AE & KLO & KHI & SHA & SHB).
      destruct (Z_lt_le_dec k nd) as [KL|KG].
      + specialize (SSL k ltac:(clear -Hk KL; lia)). specialize (KLO KL).
        eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia).
        assert (B : shad RB + shlen (k * S + S) <= SHU0 /\ 2201439137792 <= shad RB + shlen (k * S)).
        { rewrite <- SHE3. rewrite !shlen_div. clear -KLO A1 SH1 Hk SZ16. Z.div_mod_to_equations. nia. }
        rewrite SHA.
        apply dj_app; [eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); [clear -B; lia | rewrite <- SHA, SHB; clear -B; lia | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia]
                      | apply ICW_far; rewrite <- SHA, SHB; clear -B SHA SHB TL1u TL4u SH2 SH3 SH12 SH5 SH6 SH13 SH8; lia].
      + rewrite (NEWFREE k KG). specialize (KHI ltac:(clear -KG Hk; lia)). cbn [slot_shadow_bytes]. rewrite SHA.
        eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -SZ16; Z.div_mod_to_equations; lia].
        * rewrite shad_div, (shad_div RB), shlen_div. clear -KHI M8g M8e A1. Z.div_mod_to_equations. nia.
        * rewrite (shad_div (RB + au)), (shad_div RB), !shlen_div. clear -KHI NCS M8g M8e M8f A1 SZ16 Hk. Z.div_mod_to_equations. nia.
    - eapply fill_sub; [exact BIGF | | | rewrite shlen_div; clear -NCS; Z.div_mod_to_equations; lia].
      + rewrite !shad_div. clear -NC0 SZ16 M8g M8e; Z.div_mod_to_equations; nia.
      + rewrite !shad_div, !shlen_div. clear -NC0 NCS SZ16 M8g M8e M8f A1; Z.div_mod_to_equations; nia. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec]. fold RB FA. split; [exact AZU' | exact AZF']. }
  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count rrec]. subst X'. rewrite xr_cls_eq. cbn [xc_cache].
    unfold max_count. rewrite CIR. exists (skipn (Z.to_nat n) chunks0).
    split; [exact REC'|]. split.
    - subst ca. rewrite <- skipn_map. exact CH'.
    - subst ca. rewrite !length_skipn, LFL2, LCH. clear -N NLE NC0 A5; lia. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. change (aregion L c) with RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).

    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                        | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
    { intros A k HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_shlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 SH2; lia.
      - eapply (RK_shhigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD10 SH13; lia. }
    assert (DJI : disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xr_cls_ne X c _ _ c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k Hk _. subst X'. rewrite xr_busy_of. split; [reflexivity|].
        destruct (slot_in_region L st c' k ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xr_cls_ne X c _ _ c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC N; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X) ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. destruct (BUSY b Hb) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact Hb| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *.
      change (aregion L c) with RB in P5, P4. change (c_allocated_user (get_cls st c)) with au in P4, Q1. change (c_mapped_user (get_cls st c)) with mu in Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). change (aregion L c) with RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2 A1; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2792) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|H3]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wr (bv_unsigned sp) RB mu mu' SHU0 SHU1 FA nf mfa' SHF0 SHF1 (al_t L) RI CA n ++ ic_W L 1 31) A k).
  { intros A k H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    pose proof CL1 as CL1'; unfold sclr, KLS in CL1'.
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1' CL2 CL5 SCX; lia. }

  assert (WF' : awf L st_r X').
  { subst st_r X' fr ca FL2. apply awf_refill; first [exact WF | exact HC | exact CNT0 | exact MUB | exact MUM' | exact NC0 | exact NCS | exact NEWB | exact NEWM | exact NEWMOD | exact N2 | clear -N NLE; lia]. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (rrec mu' (au + ncnt * S) (nf + ncnt - n) mfa' n) (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).
  assert (EFemb : a_emb st_r = a_emb st) by (subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity).
  assert (EFexh : a_exh st_r = a_exh st) by (subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity).
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 24 8); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J24 _].
        eapply junk_frame; [exact J24 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + replace (al_t L + 2768 + 24) with (al_t L + 2792) by (clear; lia). pose proof (junk_of_cells m' _ _ STM') as J. cbn in J. exact J.
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  assert (SHX : shlen 4294967296 = 536870912 /\ shad (RB + 4294967296) = shad RB + 536870912 /\ SHF1 <= shad RB + 536870912).
  { split; [rewrite shlen_div; reflexivity|]. clear -SH9 SH10 SH13. split; lia. }
  destruct SHX as (SX1 & SX2 & SX3).
  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 672, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (RB + mu, RB + 4294967296); (SHU0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SX3 SH2 SH3 SH12 SH5 SH6 MUB NEWB A5 A1 CAE RBE FAE HC N.
      repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (QU : quar_untouched L X WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      split; [clear -CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1u TL4u TL2 TSP SP1 SP2 RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]). subst X'. unfold xr. cbn [x_busy].
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : ah_quar H L st_r X' m').
  { eapply (hq_frame _ HL L st st_r X X' m m'); [exact HQ | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC MUB A1; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [exact EFemb| exact EFexh]. }
  assert (HD' : ah_depot H L m').
  { eapply (hd_frame _ HL L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE HC MUB A1 SH1 SH2 SH9 SH11 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREPns H L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & G9 & GC & GPA & GSC & GPSH).
    unfold arng. split; [exact G1|]. split; [exact G2|]. split; [exact G3|]. split; [exact G4|]. split; [exact G5|].
    split; [exact G6|]. split; [exact G7|]. split; [exact G8|]. split; [exact G9|].
    split; [| split; [rewrite EF8; exact GPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact GSC| exact GPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array rrec].
      destruct (GC c HC) as (R1 & R2 & R3 & R4).
      change (aregion L c) with RB in R1, R2 |- *. change (afreearr L c) with FA in R3, R4 |- *.
      change (c_mapped_user (get_cls st c)) with mu in R1, R2. change (c_mapped_free_array (get_cls st c)) with mfa in R3, R4.
      split; [| split; [| split]].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R1|].
        replace mu' with (mu + (mu' - mu)) by (clear; lia). apply rng_merge; [exact BW | clear -A1; lia | clear -MUB; lia | exact R1 | exact RU].
      + destruct UD as [Emu|(_ & _ & _ & _ & _ & RU & RSU & BW)]; [rewrite Emu; exact R2|].
        replace (shlen mu') with (shlen mu + shlen (mu' - mu)) by (rewrite !shlen_div; clear -M8a M8b; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A1; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -MUB; Z.div_mod_to_equations; lia | exact R2 |].
        rewrite SHE3. exact RSU.
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact R3 | exact RF].
      + destruct FD as [Emfa|(_ & _ & _ & RF & RSF & BW)]; [rewrite Emfa; exact R4|].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact R4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (GC c' Hc'). }

  exists X', WH.
  split; [exact AR'|]. split; [exact MUH|]. split; [exact SU|].
  split. {
    intros C24. unfold c6_untouched. subst WH.
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_ri L c _ _ ALO HC); [clear -RIE; lia| clear -RIE; lia| right; right; exact C24] |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.TwinB.RIP; clear -RSP RBE HC MUB A1; unfold K_NUM_CLASSES in HC; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH1 SH2 SH9 SH10 SH11; lia |].
    apply Forall_nil. }
  split; [exact SSM|].
  split; [exact ARNG'|]. split; [exact CIR|].
  split; [rewrite GR; unfold max_count; rewrite CIR; cbn [c_count rrec]; subst n; reflexivity|].
  split; [unfold max_count; rewrite CIR; subst n; clear -N; lia|].
  split; [subst X'; reflexivity|].
  split; [intros c' NE; subst X'; apply xr_cls_ne; exact NE|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|]. split; [exact EF7|]. split; [exact EF8|].
  split; [exact GO|].
  split; [| exact WMALL].
  eapply munch_weaken; [| exact MUH]. unfold sub_fp. intros x Hx. subst WH. unfold K_REGION in Hx. change (2^32) with 4294967296 in Hx.
  rewrite SX1 in Hx. cbn [outside] in Hx |- *. clear -Hx. lia.
Qed.

Lemma refill_store : store_refill_stmt.
Proof.
  unfold store_refill_stmt.
  intros L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC C24 CNT0 CEIL LO CH LCH RR.
  pose proof (refill_store_ns L RNG RNG' sp m m' st st2 X c lo chunks0 ALO ARNG AR HC CNT0 CEIL LO CH LCH RR) as S0. cbv zeta in S0 |- *.
  destruct S0 as (X' & WH & ARNS & MUH & SU & C6U & SSX & REST).
  exists X'. split; [| exact REST].
  apply AREP_split. split; [exact ARNS|].
  destruct AR as (_ & _ & _ & _ & _ & _ & HS & _).
  destruct REST as (_ & _ & _ & _ & _ & _ & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GO & _ & WM).
  eapply (hs_frame _ HL L st _ X X' m m' WH); [exact HS| exact MUH| exact WM| exact SU| exact (C6U C24)| exact SSX].
Qed.

Section WithStore.
Hypothesis STORE : store_refill_stmt.

Theorem arefill_from_store : refill_stmt H.
Proof.
  unfold refill_stmt.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC24 CNT0 RSTK KONT.
  assert (HC : 1 <= c < K_NUM_CLASSES) by (rewrite HC24; unfold K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  unfold aflag_cell in EXH. replace (c =? K_BATCH_CLASS) with true in EXH by (symmetry; apply Z.eqb_eq; exact HC24).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.

  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (STORE L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC HC24 CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  eapply KONT. unfold ARefill_iface.TwinB.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End WithStore.

Theorem arefillP : refill_stmt H.
Proof. exact (arefill_from_store refill_store). Qed.
End RefillP.
End CANSEC1.
End ARefillP.

Module ARecyc1P.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARecRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQD.TwinB. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_acdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecyc1.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Notation Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (SHUB, SHUB + gr); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Kinds.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' AB S rz gr SHLO SHUB SHHI SHF0 SHF1 : Z).
Let HB := AB + rz - 16.
Definition reckf : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6492160 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (RB <= AB /\ AB + S <= RB + au /\ 16 <= rz /\ rz <= S)
  /\ (2201439137792 <= SHLO /\ SHLO <= SHUB /\ 0 <= gr /\ SHUB + gr <= SHHI /\ SHHI <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf.

Ltac kind := pose proof KF as KF'; unfold reckf, AIMG_HI in *; subst HB;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_ab & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_obj : forall A k, ((6492160 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.

Lemma RK_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  (A + k <= AB \/ AB + 8 <= A) -> (A + k <= HB \/ HB + 4 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHUB \/ SHUB + gr <= A) -> (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
Lemma RK_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk sp AB HB SHUB gr t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind. Qed.
End Kinds.

Lemma upd_app_right : forall {X} (l1 l2 : list X) i x, (length l1 <= i)%nat -> upd (l1 ++ l2) i x = l1 ++ upd l2 (i - length l1) x.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [rewrite Nat.sub_0_r; reflexivity|].
  destruct i as [|i]; [lia|]. cbn. rewrite IH by lia. reflexivity.
Qed.
Lemma upd_app_left : forall {X} (l1 l2 : list X) i x, (i < length l1)%nat -> upd (l1 ++ l2) i x = upd l1 i x ++ l2.
Proof.
  induction l1 as [|y l1 IH]; intros l2 i x Hi; cbn in *; [lia|].
  destruct i as [|i]; [reflexivity|]. cbn. rewrite IH by lia. reflexivity.
Qed.

Lemma AQdr_drop_prim : forall R L st X m c k n b1 ctx l1 l2 drained pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_drop R pend') 0 0 L st (xrec st X c k l1 l2 drained) m.
Proof.
  intros R L st X m c k n b1 ctx l1 l2 drained pend' (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EP XB WF.
  unfold AQdr, qr_drop. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_drop_prim L st st X R c k n b1 ctx l1 l2 drained pend' CP EP XB WF eq_refl eq_refl).
Qed.

Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Definition AHr (R : qrconc) (cs : list achunk) : aholes := mkAHoles (AQdr R 0 0) (ASECc cs) AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

Definition rec_W (L : alayout) (sp : Z) (c k n nf mfa mfa' : Z) : list (Z * Z) :=
  let AB := aslot_addr L c k in let rz := rz_size n in let HB := AB + rz - 16 in let UB := AB + rz in
  ([(sp - 688, sp); (AB, AB + 8); (HB, HB + 4); (shad UB, shad UB + granules n); (al_t L + 2800, al_t L + 3168)]%Z)
  ++ cd_W L sp c nf mfa mfa'.

Definition arecyc1_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk) (c k n lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_rec1_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (pend' : list (achunk * Z)) (cs : list achunk) (c k n b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, k) :: pend' -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  recyc1_ret L RNG sp st c k n b1 ctx lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (rec_W L (bv_unsigned sp) c k n (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_drop R pend') cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ c_mapped_user (get_cls stX c) = c_mapped_user (get_cls st c) /\ c_allocated_user (get_cls stX c) = c_allocated_user (get_cls st c)
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Lemma read_qchunk : forall L st X m c k n b1 ctx l1 l2,
  alayout_ok L -> awf L st X -> x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2 ->
  aslots L st X m c -> aslot_shadow L st X m c ->
  let S := size_of_class c in let AB := aslot_addr L c k in let rz := rz_size n in let UB := AB + rz in
     rw_cells bsegs m (UB - 16) [C1 (Z_to_bv 8 3); C1 (Z_to_bv 8 b1); C2 (Z_to_bv 64 0); C4 (Z_to_bv 64 n); C8 (Z_to_bv 64 ctx)]
  /\ junk_at m UB (S - rz)
  /\ (16 < rz -> rw_cells bsegs m AB [C8 (Z_to_bv 64 AMAGIC); C8 (Z_to_bv 64 (UB - 16))] /\ junk_at m (AB + 16) (rz - 32))
  /\ rw_cells bsegs m (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen rz)))]
  /\ rw_cells bsegs m (shad UB) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n)))]
  /\ rw_cells bsegs m (shad UB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 0xfa) (Z.to_nat (shlen S - shlen rz - granules n)))].
Proof.
  intros L st X m c k n b1 ctx l1 l2 ALO WF XB [SL _] [SH _]. cbv zeta.
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  specialize (SL k KR). specialize (SH k KR). rewrite (busy_of_X_self_g L st X BQuar c k n b1 ctx l1 l2 XB WF) in SL, SH.
  unfold aslot_busy in SL. cbn [xb_st xb_class xb_n xb_b1 xb_ctx bany bstate_byte xb_alloc xb_slot] in SL.
  destruct SL as (LH & [stb [E HDR]] & UJ). injection E as <-.
  replace (aslot_addr L c k + rz_size n - 16) with (aslot_addr L c k + rz_size n + -16) by lia.
  split; [exact HDR|]. split; [exact UJ|]. split; [exact LH|].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & G2 & GE & G0 & GF & _).
  cbn [slot_shadow_bytes xb_n xb_st bany] in SH.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 _].
  pose proof (shlen_nonneg (rz_size n) ltac:(lia)) as SRZ. pose proof (shlen_nonneg (n + 7) ltac:(lia)) as SG7.
  replace (Z.to_nat (shlen (size_of_class c))) with
    (Z.to_nat (shlen (rz_size n)) + Z.to_nat (granules n) + Z.to_nat (shlen (size_of_class c) - shlen (rz_size n) - granules n))%nat in SH
    by (generalize SRZ SG7 GF; clear; unfold granules; intros; lia).
  destruct (cb_split3_gen m _ _ _ _ _ _ _ ltac:(apply repeat_length) ltac:(apply repeat_length) ltac:(apply repeat_length) SH) as (SHA & SHU & SHR).
  rewrite Z2Nat.id in SHU by lia. rewrite Z2Nat.id in SHR by lia. rewrite Z2Nat.id in SHR by (generalize SG7; clear; unfold granules; intros; lia).
  rewrite <- SE in SHU, SHR.
  split; [exact SHA|]. split; [exact SHU| exact SHR].
Qed.

Lemma pend_head_busy : forall L st X R m c n k pend',
  AQdr R 0 0 L st X m -> qr_pend R = (CPrim c n, k) :: pend' ->
  exists b1 ctx l1 l2, x_busy X = l1 ++ bany BQuar c k n b1 ctx :: l2.
Proof.
  intros L st X R m c n k pend' (_ & _ & _ & _ & _ & _ & CP & _) EP.
  destruct CP as (_ & _ & OK & _). unfold qr_entries in OK. rewrite EP in OK.
  assert (HOK : qentry_ok X (CPrim c n, k)).
  { eapply (proj1 (Forall_forall _ _) OK). rewrite !in_app_iff. right. right. right. left. reflexivity. }
  unfold qentry_ok in HOK. cbn [fst snd] in HOK. destruct HOK as (b1 & ctx & Hin).
  destruct (in_split _ _ Hin) as (l1 & l2 & E). exists b1, ctx, l1, l2. exact E.
Qed.

Lemma nf_bound : forall L st X c, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c
  /\ 4 * (c_num_freed (get_cls st c) + max_cached c / 2) <= K_FREEARR_MAX.
Proof.
  intros L st X c WF HC. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  split; [exact NFA|].
  pose proof (size_of_class_pos c HC) as [SZ _]. pose proof (ARecRep.TwinB.max_cached_range c) as (_ & MC & _).
  unfold K_FREEARR_MAX, K_FREEARR_OFF in *. generalize NFA A1 A2 SZ MC. clear. intros. Z.div_mod_to_equations. nia.
Qed.

Lemma cache_vals_lt : forall L st X c tail, awf L st X -> 1 <= c < K_NUM_CLASSES ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  Forall (fun w : word => bv_unsigned w < 2^31)
         (firstn (Z.to_nat (c_count (get_cls st c))) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail)).
Proof.
  intros L st X c tail WF HC LEN. pose proof WF as (_ & _ & _ & _ & _ & PERC & _).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  rewrite firstn_app, length_map. replace (Z.to_nat (c_count (get_cls st c)) - length (xc_cache (x_cls X c)))%nat with 0%nat by lia.
  rewrite firstn_O, app_nil_r. apply Forall_forall. intros w Hw.
  assert (Hw' : In w (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)))).
  { rewrite <- (firstn_skipn (Z.to_nat (c_count (get_cls st c))) (map _ _)). apply in_app_iff. left. exact Hw. }
  apply in_map_iff in Hw'. destruct Hw' as (k0 & <- & Hk).
  pose proof (RANGE k0 ltac:(apply in_app_iff; right; apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
  assert (B : 0 <= acompact c k0 < 2^28).
  { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
  rewrite unsigned_lit; lia.
Qed.

Lemma rec1_store : store_rec1_stmt.
Proof.
  unfold store_rec1_stmt.
  intros L RNG RNG' sp m m' st stX X R pend' cs c k n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BQuar c k n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c k n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.TwinB.max_cached_range c) as (MCR & MCH & MCE).

  destruct RR as (m1 & MU1 & WM1 & CDR & MAG' & HDR' & SHU'). cbv zeta in MU1.
  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *. set (rz := rz_size n) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.

  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.TwinB.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).

  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).

  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.
  pose proof (rz_size_facts n (proj1 N0)) as [RZ1 RZ2]. fold rz in RZ1, RZ2.
  pose proof (rounded_size_facts n (proj1 N0)) as (RS1 & RS2 & RS3 & RS4 & RS5).
  assert (FITr : rz + n <= S /\ rz <= S) by (subst S rz; clear -FIT0 RS1 RZ1 N0; lia). destruct FITr as [FITr RZS].
  pose proof (chunk_shadow_geo L st X c k n ALO WF HC KR (proj1 N0) FIT0) as (SE & SG2 & GE & SG0 & SGF & SHLO1 & SHHI1 & SHR1 & SHR2).
  fold S AB rz RB mu in SE, SG2, GE, SG0, SGF, SHLO1, SHHI1, SHR1, SHR2.

  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHUB := shad (AB + rz)) in *. set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA /\ SHUB = shad AB + shlen rz).
  { subst SHUB SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB rz half cnt nf' cnt'.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 SE RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16 & SHE0).
  assert (KF : reckf (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' AB S rz (granules n) (shad AB) SHUB (shad AB + shlen S) SHF0 SHF1).
  { unfold reckf. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    clear -CEIL LO SPR TL1 TL1u TL4u TL2 TL4 CL1 CL1u CL2 CL3 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 RZ1 RZS SHLO1 SE SG2 SG0 GE SGF SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). unfold granules in *.
    unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].     }
  assert (MUALL : munch (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
    - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 _]. subst AB rz SHUB. cbn [outside] in H13 |- *.
      pose proof (bv_unsigned_in_range 64 sp). clear -H13 H. lia.
    - unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
      apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
      subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof (wmono_trans _ _ _ _ WM1 WM2) as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  destruct (read_qchunk L st X m c k n b1 ctx l1 l2 ALO WF XB SLOTS0 SSH0) as (_ & UJ & LH & SHA & _ & SHR).
  fold S AB rz in UJ, LH, SHA, SHR. rewrite <- ?SHE0 in SHR.
  assert (HBE : AB + rz + -16 = AB + rz - 16) by (clear; lia).

  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  rewrite CPT in CH'.

  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }

  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply (aflag_cell_frame L _ _ _ MUALL WMALL); [exact EXH|]. fold RI.
    apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ SHUB + granules n <= shad FA /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SGF SHE0 SG0 GE. lia. }
  destruct FAB as (FB1 & FB2 & FB3 & FB4 & FB5 & FB6 & FB7).
  assert (SHB : shad RB <= SHUB /\ SHF1 <= shad (RB + 4294967296) /\ 0 <= granules n) by (clear -SH13 SHE0 SG2 SH5 FB2 GE SG0 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).
  destruct SHB as (SB1 & SB2 & SB3).

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr bsegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB3 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB2 SHE4 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (HBK : 16 < rz -> 32 <= rz) by (intros H16; clear -RZ2 H16; Z.div_mod_to_equations; lia).
  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16 DJ RZ1 RZS; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16 RZ1 RZS; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). fold S AB.

      assert (UJ' : junk_at m' (AB + rz) (S - rz)).
      { eapply junk_frame; [exact UJ | exact MUALL | exact WMALL |]. intros POS.
        apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
      pose proof (junk_of_cells m' _ _ HDR') as JH. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JH. fold AB rz in JH. rewrite ?HBE in JH.
      change (Z.of_nat 16) with 16 in JH.
      destruct (Z.lt_ge_cases 16 rz) as [RZG|RZE].
      + specialize (HBK RZG). destruct (LH RZG) as [_ LJ]. pose proof (junk_of_cells m' _ _ (MAG' RZG)) as JM. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in JM. change (Z.of_nat 16) with 16 in JM.
        assert (LJ' : junk_at m' (AB + 16) (rz - 32)).
        { eapply junk_frame; [exact LJ | exact MUALL | exact WMALL |]. intros POS.
          apply dj_app; [eapply (RK_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1 RZ1 RZS; lia | apply ICW_far; clear -G1 G2 A1 A2 RZ1 RZS RBE HC TSP; lia]. }
        replace S with (16 + ((rz - 32) + (16 + (S - rz)))) by (clear; lia).
        apply junk_merge; [exact JM | | clear; lia | clear -HBK RZS; lia].
        apply junk_merge; [exact LJ' | | clear -HBK; lia | clear -RZS; lia].
        replace (AB + 16 + (rz - 32)) with (AB + rz - 16) by (clear; lia).
        apply junk_merge; [exact JH | | clear; lia | clear -RZS; lia].
        replace (AB + rz - 16 + 16) with (AB + rz) by (clear; lia). exact UJ'.
      + assert (RZ16 : rz = 16) by (clear -RZE RZ1; lia). rewrite RZ16 in JH, UJ'.
        replace (AB + 16 - 16) with AB in JH by (clear; lia).
        replace S with (16 + (S - 16)) by (clear; lia). apply junk_merge; [exact JH | exact UJ' | clear; lia | clear -RZS RZ16; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slots_disjoint L c k' k ltac:(clear -Hk'; lia) (proj1 KR) NE' ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)
                  /\ (shad (aslot_addr L c k') + shlen S <= shad AB \/ shad AB + shlen S <= shad (aslot_addr L c k'))).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 DJ AL' AL16 SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4 SGF SHE0 SG2; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB1 FB2 FB3 FB4 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH10 SH11 SH12 SH13 SH14 SH15 SGF SHE0 SG2 SG0 GE; lia
                                | apply ICW_far; clear -POS FB2 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BQuar c k n b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      assert (SHA' : rw_cells bsegs m' (shad AB) [CB (Z.to_nat (shlen rz)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen rz)))]).
      { eapply cells_frame; [exact SHA | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SG2; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 FB5 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 GE SG0; lia]. }
      assert (SHR' : rw_cells bsegs m' (SHUB + granules n) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { eapply cells_frame; [exact SHR | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by (clear -SGF GE SG0; lia).
        apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SG2 SH12 SH13 FB2 SH1 SH2 SH3 SH4 SGF SHE0 GE SG0; lia
                      | apply ICW_far; clear -SG2 SHE0 SGF GE SG0 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3 SH12 SH13; lia]. }
      assert (C2pre : rw_cells bsegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz))) [CB (Z.to_nat (granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (granules n)))]).
      { rewrite Z2Nat.id by (clear -SG2; lia). rewrite <- SHE0. exact SHU'. }
      pose proof (cb_app m' _ _ _ _ _ SHA' C2pre) as C2.
      assert (C3pre : rw_cells bsegs m' (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) [CB (Z.to_nat (shlen S - shlen rz - granules n)) (repeat (Z_to_bv 8 250) (Z.to_nat (shlen S - shlen rz - granules n)))]).
      { replace (shad AB + Z.of_nat (Z.to_nat (shlen rz) + Z.to_nat (granules n))) with (SHUB + granules n) by (rewrite SHE0; clear -SG2 GE SG0; lia). exact SHR'. }
      pose proof (cb_app m' _ _ _ _ _ C2 C3pre) as C3.
      rewrite <- !repeat_app in C3.
      replace (Z.to_nat (shlen rz) + Z.to_nat (granules n) + Z.to_nat (shlen S - shlen rz - granules n))%nat with (Z.to_nat (shlen S)) in C3 by (clear -SG2 GE SG0 SGF; lia).
      exact C3. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 SGF SHE0 SG2; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u FB1 FB4 FB5 FB6 FB7 SG2 SG0 GE SGF SH10 SH11 SH12 SH13 SH1 SH2 SH3; lia]. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2; lia.
      - eapply (RK_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB1 SB2 SB3 SH3 SH4 SH2 SH1 SH13 FB5 SHE0 SG2 SGF FB3; lia. }
    assert (DJI : disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BQuar c k n b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ ((xb_alloc L b + size_of_class (xb_class b) <= RB + mu /\ (xb_alloc L b + size_of_class (xb_class b) <= AB \/ AB + S <= xb_alloc L b))
          \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - assert (NK : xb_slot b <> k) by (intros EK; exact (key_fresh_g L st X BQuar c k n b1 ctx l1 l2 XB WF b Hb EC EK)).
      pose proof (slots_disjoint L c (xb_slot b) k (proj1 KB) (proj1 KR) NK ltac:(clear -SZ16; fold S; lia)) as DJ. fold S AB in DJ.
      rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; lia|]. split; [clear -P4 A1 A2 RBE HC; lia|]. left. split; [clear -P4 A1; lia| exact DJ].
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk (bv_unsigned sp) AB (AB + rz - 16) SHUB (granules n) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL2 CL3 CL5 SCX; unfold AIMG_HI in *; lia. }

  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BQuar c k n b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128); (AB, AB + S);
              (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & O6 & O7 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_drop R pend') 0 0 L st X' m) by (subst X'; eapply AQdr_drop_prim; [exact HQ | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_drop R pend') 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity| subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity]. }
  assert (HS' : ASECc cs L st_r X' m').
  {
    set (WS3 := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 68); (RI + 69, RI + 128); (AB, AB + S);
                (FA + 4 * nf, FA + 536870912); (shad AB, shad AB + shlen S); (SHF0, shad RB + 536870912)]).
    assert (MUS3 : munch WS3 m m').
    { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WS3. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3a & O3b & O4 & O5 & O6 & O7 & _).
      apply outside_app. split.
      - cbn [outside]. clear -O1 O2 O3a O3b O4 O5 O6 O7 RZ1 RZS SHE0 SGF SH5 SB3 FB2 NEWB CAE HC SG2 GE SG0 SH10 SH9 SHE1 NEWM A5 A6.
        pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). repeat split; try exact I; lia.
      - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
    eapply (hs_frame _ (HL (qr_drop R pend') cs) L st st_r X X' m m' WS3); [exact HS | exact MUS3 | exact WMALL | | | exact SSM].
    - unfold sec_untouched, aknown. subst WS3. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE HC G5 G6; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5; lia |].
      apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; lia |].
      apply Forall_nil.
    - unfold c6_untouched. subst WS3. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
      assert (HCk : 1 <= c < K_NUM_CLASSES) by (unfold K_NUM_CLASSES; clear -HC; lia).
      assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
      { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
        clear -RSP ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_ri L c _ _ ALO HCk); [clear -RIE; subst RI; lia| clear -RIE; subst RI; lia| left; subst RI; clear; lia] |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_ri L c _ _ ALO HCk); [clear -RIE; subst RI; lia| clear -RIE; subst RI; lia| right; left; subst RI; clear; lia] |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.TwinB.RIP; clear -RSP RBE HC G5 G6; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.TwinB.RIP; clear -RSP RBE FAE HC A5; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 SH4 SB2 FB5 SHBx; lia |].
      apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5 SHBx; lia |].
      apply Forall_nil. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_drop R pend') cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }

  exists X', mfa'.
  split. { unfold rec_W. cbv zeta. fold AB rz. eapply munch_trans; [eapply munch_weaken; [| exact MU1] | eapply munch_weaken; [| exact MU2]].
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [H5 _]. cbn [outside] in H5 |- *. subst SHUB. clear -H5. lia.
           - unfold sub_fp. intros x Hx. apply outside_app in Hx. destruct Hx as [_ HW]. exact HW. }
  split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [rewrite GR; reflexivity|]. split; [rewrite GR; reflexivity|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BQuar c k n b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BQuar c k n b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

Theorem arecyc1 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (pend' : list (achunk * Z)) (cs : list achunk)
         (c kk n CBA lo : Z) (cbs : word),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pend R = (CPrim c n, kk) :: pend' ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - RECYC1_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 CBA -> a1 = Z_to_bv 64 (qhdr L (CPrim c n) kk) ->
  rw_cells bsegs m CBA [C8 (Z_to_bv 64 (al_t L + 208)); C8 cbs] -> bv_unsigned sp <= CBA -> CBA + 16 <= 2^47 ->
  rng RNG lo (bv_unsigned sp - lo) -> rng RNG CBA 16 ->
  (forall stX X' RNG' ms', arecyc1_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R pend' cs c kk n lo m stX X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 recyc1_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R pend' cs
         c kk n CBA lo cbs ALO ARNG AR EP MI ST CEIL LO TP Ha0 Ha1 CBC CB0 CB1 RSTK RCB KONT.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct (pend_head_busy L st X R m c n kk pend' HQ EP) as (b1 & ctx & l1 & l2 & XB).
  destruct (any_range L st X BQuar c kk n b1 ctx l1 l2 XB WF) as [HC KR].
  pose proof (any_facts L st X BQuar c kk n b1 ctx l1 l2 XB WF ltac:(discriminate)) as (N0 & FIT0 & B10 & AT0 & CTX0).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  destruct (read_qchunk L st X m c kk n b1 ctx l1 l2 ALO WF XB SLOTS SSH) as (HDR & UJ & MAG & SHA & SHU & SHR).
  destruct (slot_rng L st X c kk ALO WF HC KR RNG ARNG) as [RAB RSAB].
  pose proof (slot_geo L st X c kk ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).

  eapply (recyc1_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c kk n b1 ctx CBA lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta cbs (repeat (Z_to_bv 8 0xfd) (Z.to_nat (granules n))));
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ CBA _ => exact CBC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- rw_cells _ _ (aslot_addr _ _ _ + rz_size _ - 16) _ => exact HDR
       | |- 16 < _ -> _ => intros H16; exact (proj1 (MAG H16))
       | |- rw_cells _ _ (shad _) _ => exact SHU
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ CBA _ => exact RCB
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (aslot_addr _ _ _) _ => exact RAB
       | |- rng _ (shad (aslot_addr _ _ _)) _ => exact RSAB
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | rewrite Ha1; unfold qhdr; reflexivity]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- (_ + 1) * _ <= _ =>
           unfold ndist in KR; transitivity (c_allocated_user (get_cls st c) / size_of_class c * size_of_class c);
           [apply Z.mul_le_mono_nonneg_r; [clear -S1; lia| clear -KR; lia]
           | rewrite Z.mul_comm; pose proof (Z.mul_div_le (c_allocated_user (get_cls st c)) (size_of_class c) ltac:(clear -S1; lia)); clear -A1 H; lia]
       | |- 1 <= _ => first [assumption | idtac]; destruct (BUSY (bany BQuar c kk n b1 ctx) ltac:(rewrite XB; apply in_app_iff; right; left; reflexivity)) as [_ M]; cbn in M; clear -M; lia
       | |- rz_size _ + _ <= _ => pose proof (rounded_size_ge n); clear -FIT0 H; lia
       | |- 0 <= _ < _ => first [assumption | clear -CTX0; lia]
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- 0 <= _ => first [assumption | exact (proj1 KR)]
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.

  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (rec1_store L RNG RNG' sp m m' st stX X R pend' cs c kk n b1 ctx lo l1 l2 tail ALO ARNG AR EP XB CEIL LO CH LCH RR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & MU1 & AU1 & XS & XL).
  destruct RR as (m1 & _ & _ & CDR & _). destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold arecyc1_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|]. split; [exact MU1|]. split; [exact AU1|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
End ARecyc1P.

Module ARefillP_e.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARefill_iface.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AEmbFrame.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.

Section CANSECE. Context {rc : runConstT} {ov : annOV}.
Section RefillPE.
Variable H : aholes.
Hypothesis HL : ahole_laws H.

Definition refill_ret_e (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (c lo : Z) (m : amem)
    (st_r : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  ARefill_iface.TwinB.refill_ret H L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms'
  /\ a_emb st_r = a_emb st /\ a_exh st_r = a_exh st.

Definition refill_stmt_e : Prop :=
  forall {R} (k : astate -> bool -> AM R) (Q : R -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (c lo : Z),
  alayout_ok L -> arng L RNG st -> AREP H L st X m ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - AREFILL_STACK ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 (acache_addr L c) -> a2 = Z_to_bv 64 AINSTANCE -> a3 = Z_to_bv 64 c ->
  c = K_BATCH_CLASS -> c_count (get_cls st c) = 0 ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall st_r X' RNG' ms', refill_ret_e L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X c lo m st_r X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k (apop c st_r) true)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_refill_tree st c k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 0x42500) fc None m (seg_rom bsegs)).

Theorem arefillP_e : refill_stmt_e.
Proof.
  unfold refill_stmt_e.
  intros R k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X c lo
         ALO ARNG AR MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 HC24 CNT0 RSTK KONT.
  assert (HC : 1 <= c < K_NUM_CLASSES) by (rewrite HC24; unfold K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  unfold aflag_cell in EXH. replace (c =? K_BATCH_CLASS) with true in EXH by (symmetry; apply Z.eqb_eq; exact HC24).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof TL1 as TL1u; unfold sclr, KLS in TL1u. pose proof TL4 as TL4u; unfold iclr, AIMG_LO, AIMG_HI in TL4u.
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof CL1 as CL1u; unfold sclr, KLS in CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT as RT0.
  destruct RT0 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).

  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (aregion_info L c + 72) 8 48 RJ56 ltac:(lia) ltac:(lia)) as [STN8 _]. destruct (c8_of_junk m _ STN8) as [stn STN].
  destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(lia) ltac:(lia)) as [_ STM8].
  replace (al_t L + 2768 + 24) with (al_t L + 2792) in STM8 by lia. destruct (c8_of_junk m _ STM8) as [stm STM].
  destruct FJ as [fj FJ'].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH.
  assert (XC0 : xc_cache (x_cls X c) = []).
  { destruct (xc_cache (x_cls X c)) as [|y l] eqn:E; [reflexivity|]. exfalso. rewrite ?E in LENC. cbn [length] in LENC. clear -LENC CNT0. lia. }
  rewrite XC0 in CH, LCH. cbn [map app length] in CH, LCH.
  assert (NFA : c_num_freed (get_cls st c) <= c_allocated_user (get_cls st c) / size_of_class c).
  { rewrite <- LENF. apply NoDup_bound_length.
    - apply NoDup_app_remove_r in ND. exact ND.
    - intros k0 Hk. apply RANGE. apply in_app_iff. left. exact Hk.
    - unfold ndist in RANGE. apply Z.div_pos; [lia|]. pose proof (size_of_class_facts c HC); lia. }
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  assert (FL31 : Forall (fun w : word => bv_unsigned w < 2^31) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c)))).
  { apply Forall_forall. intros w Hw. apply in_map_iff in Hw. destruct Hw as (k0 & <- & Hk).
    pose proof (RANGE k0 ltac:(apply in_app_iff; left; exact Hk)) as KR. unfold ndist in KR.
    assert (B : 0 <= acompact c k0 < 2^28).
    { unfold acompact. unfold K_FREEARR_OFF in A2. generalize KR A1 A2 SZ16 SZM; clear; intros. Z.div_mod_to_equations. nia. }
    rewrite unsigned_lit; lia. }
  eapply refill_spec with (lo := lo) (L := L) (st := st) (cnt := fun j => c_count (get_cls st j)) (sj := sj) (stm := stm) (stn := stn) (fj := fj)
                          (fl := map (fun k => Z_to_bv 64 (acompact c k)) (xc_free (x_cls X c))) (chunks0 := tail);
  try lazymatch goal with
       | |- implS _ _ _ _ _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => clear -LO; lia
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- rw_cells _ _ (aregion_info _ _ + 68) _ => exact EXH
       | |- rw_cells _ _ (aregion_info _ _ + 72) _ => exact STN
       | |- rw_cells _ _ (afreearr _ _ + _) _ => exact FJ'
       | |- rw_cells _ _ (al_t _ + 2792) _ => exact STM
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ (afreearr _ _) _ => exact FL
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact FL31
       | |- length (map _ _) = _ => rewrite length_map; clear -LENF; lia
       | |- length _ = _ => first [exact LSJ | exact LCH]
       | |- azero _ (shad (aregion _ _ + _)) _ => exact AZU
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall st2, _ => idtac
       end.
  all: lazymatch goal with
       | |- forall _, _ => idtac
       | _ => first [assumption | clear -A1 A2 A3 A4 A5 A6 A7 NFA HC SP1 SP2 SP3 TL1u TL4u TL2 TL3 CL1 CL1u CL2 CNT0; unfold K_NUM_CLASSES in *; lia]
       end.

  intros st2 RNG' m' t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' RR.
  destruct (refill_store H HL L RNG RNG' sp m m' st st2 X c lo tail ALO ARNG AR HC HC24 CNT0 CEIL LO CH LCH RR)
    as (X' & AR' & ARNG' & CIN & CCNT & NPOS & XB & XC & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & GC & MU & WM).
  destruct RR as (m1 & _ & _ & TR & _).
  destruct TR as (FPLE & mu' & mfa' & ncnt & sj' & stm' & stn' & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & ST2E & _ & _ & MIT & STT & _).
  unfold KKref. rewrite (take_is_apop c (max_cached c / 2) st2).
  assert (EMB2 : a_emb st2 = a_emb st) by (destruct ST2E as [E|E]; rewrite E; exact (init_cache_emb st)).
  assert (EXH2 : a_exh st2 = a_exh st) by (destruct ST2E as [E|E]; rewrite E; unfold init_cache; destruct (a_cinit st); reflexivity).
  eapply KONT. unfold refill_ret_e. split; [| split; [exact EMB2| exact EXH2]].
  unfold ARefill_iface.TwinB.refill_ret. split; [exact FPLE|]. do 15 eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact CCNT|]. split; [exact NPOS|]. split; [exact XB|]. split; [exact XC|].
  split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|]. split; [exact L7|]. split; [exact L8|].
  exact GC.
Qed.
End RefillPE.
End CANSECE.
End ARefillP_e.

Module ACdeallocP.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase. Import LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics. Import LinuxProcessSemantics.LinuxProcessSem.MemImageType. Import LinuxProcessSemantics.LinuxProcessSem.State. Import LinuxProcessSemantics.LinuxProcessSem.Specs. Import LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude. Import LinuxProcessSemantics.Riscv.Instr. Import LinuxProcessSemantics.Riscv.Decode. Import LinuxProcessSemantics.Riscv.DecodeC. Import LinuxProcessSemantics.Riscv.Sem. Import LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.PropExec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.MState. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Mem. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Cells. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Exec. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Step. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Frame. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Arr. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Tac. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.ITree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Nodes. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.Decode. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALib.SysStep.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.MM_syscalls. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.WStr.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.ALibA.SysStepF.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.STree. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanCtrl. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Spec.AsanEmbed.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.BothW.BImg. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AProto.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABase.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKit2.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AKitR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ABytes.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AQConst.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AModelFacts.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepKit.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepFrame.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ALayout.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AHeapP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQ.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQP.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQR.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeGeo.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AFreeRead.TwinB.AFreeRead. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARecRep.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.ARepQD.TwinB. Import ARefillP. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.RT_stubs.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apoison.TwinB.F_apoison.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acache.TwinB.F_acache.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aalloc3.TwinB.F_aalloc3.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_ammap.TwinB.F_ammap. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_aensure.TwinB. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_apopulate.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_agetfrom.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_arefill. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_amaybe.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_agetfrom.TwinB.F_areturn. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_acdrain.TwinB.  Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arefill.TwinB.F_acdealloc. Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.F_arecyc1.TwinB. Import ARecyc1P.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.AsanW.AC6U.TwinB.
Import OSSVerify.Proofs.msgpack_c.unpack_pack_fuzzer.lib.Common.RunDraw.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Import Exc.
Open Scope Z_scope.

Notation Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI :=
  ([(sp - 688, sp); (t + 2784, t + 2792); (t + 2800, t + 3168);
    (CA, CA + 4); (CA + 16, CA + 80); (FA + 4 * nf, FA + mfa'); (SHF0, SHF1); (RI, RI + 8); (RI + 16, RI + 32); (RI + 72, RI + 128)]%Z) (only parsing).

Local Lemma sclr_int : forall a n, sclr a n -> 0 <= a -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ a + n <= 2147446784 + k * 18446744073709551616 /\ 17594333495296 * k <= a.
Proof. intros a n H G1 G2. unfold sclr, KLS in H. destruct H; [exists 0 | exists 1]; lia. Qed.
Local Lemma iclr_int : forall a n, iclr a n -> a + n <= 18446744073709551616 ->
  exists k, 0 <= k <= 1 /\ 4096 <= a /\ a + n <= 65536 + k * 18446744073709551616 /\ 6492160 * k <= a.
Proof. intros a n H G2. unfold iclr, AIMG_LO, AIMG_HI in H. destruct H as [? [?|?]]; [exists 0 | exists 1]; lia. Qed.
Local Lemma ablk_int {rc : runConstT} : forall lo hi, ablk lo hi ->
  exists k, 0 <= k <= 1 /\ 6492160 <= lo /\ 17594333495296 * k <= lo /\ hi <= 2147446784 + k * 18446744073709551616 /\ hi <= ATOP.
Proof. intros lo hi H. unfold ablk, KLS, AIMG_HI in H. pose proof atop_range. destruct H as [[? ?]|[? ?]]; [exists 0 | exists 1]; lia. Qed.
Local Ltac band_int H :=
  let k := fresh "k" H in let A := fresh "KA" H in let B := fresh "KB" H in let C := fresh "KC" H in let D := fresh "KD" H in
  let G1 := fresh "G" in let G2 := fresh "G" in
  lazymatch type of H with
  | sclr ?a ?n =>
      assert (G1 : 0 <= a) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia); assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (sclr_int a n H G1 G2) as (k & A & B & C); clear G1 G2
  | iclr ?a ?n =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | 4096 <= ?a /\ (?a + ?n <= _ \/ _ <= ?a) =>
      assert (G2 : a + n <= 18446744073709551616) by (atop_facts; unfold AIMG_HI, AIMG_LO, KLS in *; lia);
      destruct (iclr_int a n H G2) as (k & A & B & C & D); clear G2
  | ablk ?lo ?hi => let E := fresh "KE" H in destruct (ablk_int lo hi H) as (k & A & B & E & C & D)
  end.

Section CANSEC1. Context {rc : runConstT} {ov : annOV}.
Section Kinds0.
Variables (sp lo t ctx SB c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1 : Z).
Definition reckf0 : Prop :=
     (ATOP <= lo /\ lo <= sp - 688 /\ sp <= 2^64)
  /\ (sclr t 4096 /\ iclr t 4096 /\ t + 4096 <= ATOP /\ sclr ctx 65536 /\ 6492160 <= ctx /\ ctx + 65536 <= ATOP /\ (ctx + 4096 <= t \/ t + 4096 <= ctx))
  /\ (1 <= c <= 31 /\ CA = t + 208 + c * 80)
  /\ (17594333495296 <= SB /\ SB + 137438957568 <= ATOP /\ RB = SB + c * 4294967296 /\ FA = RB + 3758096384 /\ RI = SB + 137438953472 + c * 128)
  /\ (t + 4096 <= SB \/ SB + 137438957568 <= t) /\ (ctx + 65536 <= SB \/ SB + 137438957568 <= ctx)
  /\ (0 <= au /\ au <= mu /\ mu <= 3758096384 /\ 0 <= nf /\ 4 * nf <= mfa /\ mfa <= mfa' /\ mfa' <= 536870912)
  /\ (2201439137792 <= SHF0 /\ SHF0 <= SHF1 /\ SHF1 <= 17594333495296).
Hypothesis KF : reckf0.

Ltac kind0 := pose proof KF as KF'; unfold reckf0, AIMG_HI in *;
  destruct KF' as (F_lo & (Ft1 & Ft2 & Ft3 & Fc1 & Fc2 & Fc3 & Ftc) & F_c & F_sb & F_tsb & F_csb & F_mu & F_sh);
  band_int Ft2; band_int Ft1; band_int Fc1; clear Ft1 Ft2 Fc1;
  cbn [disjoint_from]; repeat (split; [lia|]); first [lia | exact I].

Lemma RK0_img : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_obj : forall A k, ((6492160 <= A /\ A + k <= 2147446784) \/ 17594333495296 <= A) -> A + k <= ATOP -> 0 <= k ->
  (A + k <= t \/ t + 4096 <= A) -> (A + k <= SB \/ SB + 137438957568 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tlow : forall A k, t <= A -> A + k <= t + 288 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_thigh : forall A k, t + 3168 <= A -> A + k <= t + 4096 -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_tstat : forall A k, t + 2768 <= A -> A + k <= t + 2800 -> 0 <= k -> (A + k <= t + 2784 \/ t + 2792 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_rec : forall A k, t + 288 <= A -> A + k <= t + 2768 -> 0 <= k -> (A + k <= CA \/ CA + 4 <= A) -> (A + k <= CA + 16 \/ CA + 80 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_reg_other : forall A k, SB <= A -> 0 <= k -> (A + k <= RB \/ RB + 4294967296 <= A) -> A + k <= SB + 137438953472 ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.

Lemma RK0_space_c : forall A k, RB <= A -> A + k <= RB + mu -> 0 <= k ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_gap : forall A k, RB + mu <= A -> A + k <= FA + 4 * nf -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_ri : forall A k, SB + 137438953472 <= A -> A + k <= SB + 137438957568 -> 0 <= k ->
  (A + k <= RI \/ RI + 8 <= A) -> (A + k <= RI + 16 \/ RI + 32 <= A) -> (A + k <= RI + 72 \/ RI + 128 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_sh : forall A k, 2201439137792 <= A -> A + k <= 17594333495296 -> 0 <= k ->
  (A + k <= SHF0 \/ SHF1 <= A) ->
  disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
Lemma RK0_stkhi : forall A k, sp <= A -> 0 <= k -> disjoint_from (Wk0 sp t CA FA nf mfa' SHF0 SHF1 RI) A k.
Proof. intros. kind0. Qed.
End Kinds0.

Lemma repeat_app3 : forall {X} (x : X) a b c, repeat x a ++ repeat x b ++ repeat x c = repeat x (a + b + c).
Proof. intros. rewrite !repeat_app. rewrite app_assoc. reflexivity. Qed.

Lemma AQdr_unbatch : forall R L st X m kb nb b1 ctx l1 l2 drained,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] -> qr_pend R = [] ->
  x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 -> awf L st X ->
  AQdr (qr_unbatch R) 0 0 L st (xrec st X K_BATCH_CLASS kb l1 l2 drained) m.
Proof.
  intros R L st X m kb nb b1 ctx l1 l2 drained (QC & MX & TC & GL & TB & IA & CP & NUM & NT) EB EP XB WF.
  unfold AQdr, qr_unbatch. cbn [qr_loc qr_glob qr_tmp qr_ia].
  split; [exact QC|]. split; [exact MX|]. split; [exact TC|]. split; [exact GL|]. split; [exact TB|]. split; [exact IA|].
  split; [| exact (conj NUM NT)].
  exact (qcoupled_rec_unbatch L st st X R kb nb b1 ctx l1 l2 drained CP EB EP XB WF eq_refl eq_refl).
Qed.

Section P.
Variables (ASECc : list achunk -> alayout -> astate -> aconc -> amem -> Prop)
          (AD : alayout -> amem -> Prop) (AF : alayout -> list ablock -> amem -> Prop).
Let AHr := AHr ASECc AD AF.
Hypothesis HL : forall R cs, ahole_laws (AHr R cs).

Definition acd24_ret (L : alayout) (RNG : footprint)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (st : astate) (X : aconc) (R : qrconc) (cs : list achunk) (lo : Z) (m : amem)
    (stX : astate) (X' : aconc) (RNG' : footprint) (ms' : machine_state) : Prop :=
  let c := K_BATCH_CLASS in
  fp_le RNG RNG' /\ exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m' (mfa' : Z),
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom bsegs)
    /\ munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m' /\ mem_inv bsegs m' /\ stk bsegs m' lo (bv_unsigned sp)
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Definition store_cd24_stmt : Prop :=
  forall (L : alayout) (RNG RNG' : footprint) (sp : word) (m m' : amem) (st stX : astate) (X : aconc) (R : qrconc)
         (cs : list achunk) (kb nb b1 ctx lo : Z) (l1 l2 : list xbusy) (tail : list word),
  let c := K_BATCH_CLASS in
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] -> x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2 ->
  ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  u32arr bsegs m (acache_addr L c + 16) (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) ->
  (length (xc_cache (x_cls X c)) + length tail = 16)%nat ->
  cdealloc_ret L RNG sp st c (abatch_addr L kb) lo (map (fun k => Z_to_bv 64 (acompact c k)) (xc_cache (x_cls X c)) ++ tail) m stX RNG' m' ->
  exists X' mfa',
       munch (cd_W L (bv_unsigned sp) c (c_num_freed (get_cls st c)) (c_mapped_free_array (get_cls st c)) mfa') m m'
    /\ wmono bsegs m m'
    /\ c_mapped_free_array (get_cls st c) <= mfa' <= K_FREEARR_MAX
    /\ AREP (AHr (qr_unbatch R) cs) L stX X' m' /\ arng L RNG' stX
    /\ a_cinit stX = true /\ a_live stX = a_live st /\ a_next stX = a_next st
    /\ a_qloc stX = a_qloc st /\ a_qloc_bytes stX = a_qloc_bytes st /\ a_qglob stX = a_qglob st /\ a_qglob_bytes stX = a_qglob_bytes st
    /\ a_nsec stX = a_nsec st /\ a_nres stX = a_nres st /\ a_ptr_array stX = a_ptr_array st /\ a_space_beg stX = a_space_beg st
    /\ (forall c', c' <> c -> get_cls stX c' = get_cls st c')
    /\ (forall b, In b (x_busy X') -> In b (x_busy X))
    /\ (forall b p, In b (x_busy X) -> xb_st b = BLive p -> In b (x_busy X')).

Lemma cd24_store : store_cd24_stmt.
Proof.
  unfold store_cd24_stmt.
  intros L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR.
  set (c := K_BATCH_CLASS) in *. set (k := kb) in *.

  pose proof AR as AR0. destruct AR0 as (WF & RT & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr] in HQ, HS, HD.
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (any_range L st X BBatch c k nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof SLOTS as SLOTS0. pose proof SSH as SSH0. destruct SLOTS as [SL UND]. destruct SSH as [SSL SUND].
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof (size_of_class_facts c HC) as [SZ16 SZM].
  pose proof (ARecRep.TwinB.max_cached_range c) as (MCR & MCH & MCE).

  destruct CDR as (FPLE & drained & mfa' & sj' & sta' & DR & GCX & STE & MFD & NEWB & NEWM & NEWMOD & MU2 & WM2 & MI' & ST' & RECS' & RECc' & CH' & MTX' & REG' & J72' & STATS' & LSJ' & STA' & DRA & FJ' & AZF' & MC').
  unfold K_NUM_CLASSES, K_FREEARR_MAX, K_FREEARR_MAP, K_FREEARR_OFF, K_USER_MAP, K_SPACE_SIZE, K_SPACE_EXTRA, K_ALIGN in *.
  change (2^37) with 137438953472 in *.

  set (S := size_of_class c) in *. set (half := max_cached c / 2) in *.
  set (mu := c_mapped_user (get_cls st c)) in *. set (au := c_allocated_user (get_cls st c)) in *.
  set (nf := c_num_freed (get_cls st c)) in *. set (mfa := c_mapped_free_array (get_cls st c)) in *. set (cnt := c_count (get_cls st c)) in *.
  set (nd := ndist st c) in *.
  set (nf' := if drained then nf + half else nf) in *. set (cnt' := if drained then cnt - half + 1 else cnt + 1) in *.
  set (X' := xrec st X c k l1 l2 drained).
  set (AB := aslot_addr L c k) in *.
  assert (GEO : aregion_info L c = al_space_beg L + 137438953472 + c * 128 /\ aregion L c = al_space_beg L + c * 4294967296
                /\ afreearr L c = al_space_beg L + c * 4294967296 + 3758096384 /\ acache_addr L c = al_t L + 208 + c * 80).
  { unfold aregion_info, afreearr, aregion, acache_addr, K_REGION, K_FREEARR_OFF, K_SPACE_SIZE, ARI_STRIDE. change (2^32) with 4294967296. change (2^37) with 137438953472. repeat split; reflexivity. }
  destruct GEO as (RIE & RBE & FAE & CAE).
  set (RB := aregion L c) in *. set (FA := afreearr L c) in *. set (RI := aregion_info L c) in *. set (CA := acache_addr L c) in *.

  assert (MCle : forall c', max_count st c' <= max_cached c') by (intros c'; unfold max_count; pose proof (ARecRep.TwinB.max_cached_range c'); destruct (a_cinit st); lia).
  assert (DRC : if drained then cnt = max_cached c else cnt < max_cached c).
  { rewrite DR. pose proof (MCle c) as M. unfold max_count in CNTB, M. fold cnt in CNTB.
    destruct (a_cinit st); cbn [andb]; [destruct (Z.eqb_spec cnt (max_cached c)); [exact e| lia] | lia]. }
  assert (HALF : 1 <= half <= 8 /\ max_cached c = 2 * half) by (subst half; clear -MCR MCH MCE; lia). destruct HALF as [HALF MC2].
  assert (CNT16 : 0 <= cnt <= 16 /\ cnt' - 1 <= cnt /\ 1 <= cnt' <= 16 /\ Z.of_nat (length (xc_cache (x_cls X c))) = cnt /\ nf <= nf' <= nf + 8).
  { subst cnt' nf'. fold cnt in CNTB, LENC. pose proof (MCle c). destruct drained; clear -CNTB LENC DRC HALF MC2 MCR H; lia. }
  destruct CNT16 as (CNT16 & CNTle & CNT1 & LENCc & NFle).

  set (st_r := put_cls c (mkAClass mu au nf' mfa' cnt') (init_cache st)) in *.
  assert (STR : stX = st_r) by (rewrite STE, GCX; reflexivity). subst stX.
  pose proof (init_cache_fields st) as (E1 & E2 & E3 & E4 & E5 & E6 & E7 & E8 & E9 & E10 & E11).
  assert (GR : get_cls st_r c = mkAClass mu au nf' mfa' cnt') by (subst st_r; apply get_cls_put_cls_eq).
  assert (GO : forall c', c' <> c -> get_cls st_r c' = get_cls st c') by (intros c' NE; subst st_r; rewrite (get_cls_put_cls_ne c c') by exact NE; apply init_cache_cls).
  assert (CIR : a_cinit st_r = true) by (subst st_r; cbn; exact E11).
  assert (NDR : ndist st_r c = nd) by (unfold ndist; rewrite GR; reflexivity).
  assert (EF : a_live st_r = a_live st /\ a_next st_r = a_next st /\ a_qloc st_r = a_qloc st /\ a_qloc_bytes st_r = a_qloc_bytes st
               /\ a_qglob st_r = a_qglob st /\ a_qglob_bytes st_r = a_qglob_bytes st /\ a_nsec st_r = a_nsec st /\ a_nres st_r = a_nres st
               /\ a_ptr_array st_r = a_ptr_array st /\ a_space_beg st_r = a_space_beg st).
  { subst st_r. destruct (put_cls_fields c (mkAClass mu au nf' mfa' cnt') (init_cache st)) as (P1 & P2 & P3 & P4 & P5 & P6 & P7 & P8 & P9 & P10 & _).
    rewrite P1, P2, P3, P4, P5, P6, P7, P8, P9, P10, E1, E2, E3, E4, E5, E6, E7, E8, E9, E10. repeat split; reflexivity. }
  destruct EF as (EF1 & EF2 & EF3 & EF4 & EF5 & EF6 & EF7 & EF8 & EF9 & EF10).

  pose proof (slot_geo L st X c k ALO WF HC KR) as (_ & _ & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).
  fold S AB RB mu au in AL16, G1, G2, G3, G4, G5, G6, G7, G8, R8, M8.

  assert (AU8 : au mod 8 = 0).
  { pose proof (proj2 (Z.div_exact au S ltac:(clear -SZ16; lia)) A3) as EA. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    rewrite ES in EA at 1. rewrite EA. replace (16 * (S / 16) * (au / S)) with ((2 * (S / 16) * (au / S)) * 8) by (clear; lia). apply Z_mod_mult. }
  set (SHF0 := shad (FA + mfa)) in *. set (SHF1 := SHF0 + shlen (mfa' - mfa)) in *.
  assert (SHE : SHF1 = shad (FA + mfa') /\ shad FA + shlen mfa = SHF0 /\ shad AB + shlen S <= shad (RB + au) /\ shad (RB + au) <= shad FA /\ shad FA <= SHF0 /\ SHF0 <= SHF1
                /\ SHF1 + shlen (536870912 - mfa') = shad (RB + 4294967296) /\ shad (RB + 4294967296) <= 17594333495296
                /\ shad RB = shad (al_space_beg L) + c * 536870912 /\ shad (RB + 4294967296) = shad (al_space_beg L) + (c + 1) * 536870912
                /\ shad (al_space_beg L) + 32 * 536870912 <= 17594333495296 /\ 2201439137792 <= shad RB /\ shad RB <= shad AB
                /\ shad (RB + au) + shlen (mu - au) = shad (RB + mu) /\ shad (RB + mu) <= shad FA
                /\ shad (RB + mu) + shlen (3758096384 - mu) = shad FA).
  { subst SHF1 SHF0. clearbody S mu au nf mfa nd RB FA RI CA AB half cnt nf' cnt' c k.
    generalize R8 AL16 SZM M8 A7 NEWMOD AU8 G1 G2 A1 A2 A5 A6 NEWB NEWM HC SP1 SP2 SP3 RBE FAE SZ16. clear. intros.
    rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. Z.div_mod_to_equations. lia. }
  destruct SHE as (SHE1 & SHE4 & SH1 & SH2 & SH3 & SH4 & SH5 & SH6 & SH9 & SH10 & SH11 & SH12 & SH13 & SH14 & SH15 & SH16).
  assert (KF : reckf0 (bv_unsigned sp) lo (al_t L) (al_ctx L) (al_space_beg L) c RB FA RI CA mu au nf mfa mfa' SHF0 SHF1).
  { unfold reckf0. pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
    pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)).
    clear -H H0 CEIL LO SPR TL1 TL1u TL4u TL2 CL1 CL1u CL3 CL2 CL5 HC CAE SP1 SP2 RBE FAE RIE TSP SCX A1 A2 A5 A6 NEWB NEWM G1 G2 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6 SH10 SH11.
    unfold c, K_BATCH_CLASS in *. unfold iclr, AIMG_LO, AIMG_HI in *; repeat match goal with H : _ /\ _ |- _ => destruct H end; repeat split; first [assumption | lia].     }
  assert (MUALL : munch (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) m m').
  { eapply munch_weaken; [| exact MU2].
    unfold sub_fp, cd_W. cbv zeta. fold nf mfa CA FA RI. intros x Hx. apply outside_app in Hx. destruct Hx as [H13 HW].
    apply outside_app. split; [cbn [outside] in H13 |- *; clear -H13; lia|]. apply outside_app. split; [exact HW|].
    subst SHF0 SHF1. cbn [outside] in H13 |- *. clear -H13. lia. }
  pose proof WM2 as WMALL.
  assert (ICW_far : forall A k, (A + k <= al_t L \/ al_t L + 4096 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }
  assert (ICW_t : forall A k, (A + k <= al_t L + 292 \/ al_t L + 2768 <= A) -> disjoint_from (ic_W L 1 31) A k).
  { intros A k0 HA. apply ic_W_disjoint_gen; [unfold acache_addr; clear -HA; lia | clear; cbn; lia | clear; lia]. }

  assert (CPT : (AB - RB) / 16 = acompact c k).
  { subst AB RB. unfold aslot_addr, acompact. fold S. pose proof (proj2 (Z.div_exact S 16 ltac:(clear; lia)) SZM) as ES.
    set (q := S / 16) in ES. replace (aregion L c + k * S - aregion L c) with (k * q * 16) by (rewrite ES; clear; nia). rewrite Z.div_mul by (clear; lia). reflexivity. }
  unfold abatch_addr in CH'. fold c AB in CH'. rewrite CPT in CH'.

  assert (RCUT : drained = true -> rcut st c = Z.to_nat (cnt - half) /\ (Z.to_nat (cnt - half) < length (xc_cache (x_cls X c)))%nat /\ Z.to_nat (cnt' - 1) = Z.to_nat (cnt - half)).
  { intros D. unfold rcut, rcnt, rhalf. fold cnt half. subst cnt'. rewrite D in DRC |- *. split; [reflexivity|]. clear -LENCc DRC HALF MC2. split; lia. }

  assert (ACc : acache_cells L st_r X' m' c).
  { unfold acache_cells. cbv zeta. fold CA. rewrite GR. cbn [c_count]. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_cache].
    unfold rcache'. pose proof RCUT as RC. destruct drained.
    - destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1. rewrite RC3 in CH'.
      exists (skipn (Datatypes.S (Z.to_nat (cnt - half))) (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c))) ++ tail).
      split; [exact RECc'|]. split.
      + rewrite upd_app_left in CH' by (rewrite length_map; exact RC2). rewrite upd_firstn_skipn in CH' by (rewrite length_map; exact RC2).
        rewrite map_app, <- List.firstn_map. cbn [map]. rewrite <- !app_assoc in CH' |- *. cbn [app] in CH' |- *. exact CH'.
      + rewrite !length_app, length_skipn, length_map, length_firstn. cbn [length]. clear -RC2 LCH. lia.
    - assert (TL : exists t0 tail', tail = t0 :: tail').
      { destruct tail as [|t0 tail']; [exfalso| exists t0, tail'; reflexivity]. cbn [length] in LCH. clear -LCH LENCc DRC MCR. lia. }
      destruct TL as (tw & tail' & ->). exists tail'.
      split; [exact RECc'|]. split.
      + subst cnt'. replace (Z.to_nat (cnt + 1 - 1)) with (length (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)))) in CH' by (rewrite length_map; clear -LENCc; lia).
        rewrite upd_app_right, Nat.sub_diag in CH' by (clear; lia). cbn [upd] in CH'. rewrite map_app. cbn [map]. rewrite <- app_assoc. cbn [app]. exact CH'.
      + rewrite length_app. cbn [length] in LCH |- *. clear -LCH. lia. }

  assert (RCc : aregion_cells L st_r m' c).
  { unfold aregion_cells. cbv zeta. fold RI. rewrite GR. cbn [c_num_freed c_mapped_free_array c_allocated_user c_mapped_user].
    pose proof MTX16 as M2. rw_split M2 1%nat M2a M2b. clear M2a.
    eapply cells_frame in M2b; [| exact MUALL | exact WMALL | cbn [cells_size csize Nat.add];
      apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]].
    split. { rw_join MTX' M2b M16. exact M16. }
    split; [exact REG'|].
    split. { eapply junk_frame; [exact RJ4 | exact MUALL | exact WMALL |]. intros _.
             apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
    split; [| exact J72'].
    eapply (aflag_cell_frame L _ _ _ MUALL WMALL); [exact EXH|]. fold RI.
    apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RIE; clear -HC SP1; lia | apply ICW_far; rewrite RIE; clear -HC SP1 TSP; lia]. }
  assert (FAB : 2201439137792 <= shad FA /\ SHF1 <= 17594333495296 /\ 0 <= shlen mfa /\ 0 <= shlen S
                /\ 0 <= shlen (mu - au) /\ 0 <= shlen (3758096384 - mu)).
  { pose proof (shlen_nonneg mfa ltac:(clear -A5 A6; lia)). pose proof (shlen_nonneg S ltac:(clear -SZ16; lia)). pose proof (shlen_nonneg (536870912 - mfa') ltac:(clear -NEWB; lia)).
    pose proof (shlen_nonneg (mu - au) ltac:(clear -A1; lia)). pose proof (shlen_nonneg (3758096384 - mu) ltac:(clear -A2; lia)).
    clear -H H0 H1 H2 H3 SH12 SH13 SH1 SH2 SH3 SH4 SH5 SH6. lia. }
  destruct FAB as (FB1 & FB2 & FB4 & FB5 & FB6 & FB7).
  assert (SB2 : SHF1 <= shad (RB + 4294967296)) by (clear -SH5 FB2 NEWB; pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)); lia).

  assert (FAc : afreearray L st_r X' m' c).
  { unfold afreearray. cbv zeta. fold FA. rewrite GR. cbn [c_num_freed c_mapped_free_array]. subst X'. rewrite (xrec_cls_self st X c k l1 l2 drained). cbn [xc_free].
    assert (FL' : u32arr bsegs m' FA (map (fun k0 : Z => Z_to_bv 64 (acompact c k0)) (xc_free (x_cls X c)))).
    { eapply u32arr_frame; [exact FL | exact MUALL | exact WMALL |]. rewrite length_map, LENF. fold nf.
      apply dj_app; [eapply (RK0_gap _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?FAE, ?RBE; clear -A1 A2 A5; lia | apply ICW_far; rewrite FAE; clear -A5 A6 HC TSP; lia]. }
    split; [| split; [exact FJ'|]].
    - unfold rfree'. pose proof RCUT as RC. destruct drained; [| exact FL'].
      destruct (RC eq_refl) as (RC1 & RC2 & RC3). rewrite RC1, map_app. apply u32arr_app; [exact FL'|].
      rewrite length_map, LENF. fold nf. specialize (DRA eq_refl).
      rewrite skipn_app, List.skipn_map, length_map in DRA. replace (Z.to_nat (cnt - half) - length (xc_cache (x_cls X c)))%nat with 0%nat in DRA by (clear -RC2; lia).
      rewrite skipn_O, firstn_app, length_map, length_skipn in DRA.
      replace (Z.to_nat half - (length (xc_cache (x_cls X c)) - Z.to_nat (cnt - half)))%nat with 0%nat in DRA by (clear -RC2 LENCc HALF MC2 DRC; lia).
      rewrite firstn_O, app_nil_r, firstn_all2 in DRA by (rewrite length_map, length_skipn; clear -RC2 LENCc HALF MC2 DRC; lia). exact DRA.
    - assert (FS1 : junk_at m' (shad FA) (shlen mfa)).
      { eapply junk_frame; [exact FSJ | exact MUALL | exact WMALL |]. intros _.
        apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -FB1 FB2 FB4 SHE4 SH3 SH4; lia
                      | apply ICW_far; clear -FB1 FB2 SHE4 SH3 SH4 TL1u; lia]. }
      destruct MFD as [Emfa|(_ & _ & Emfa & FI & _)].
      + rewrite Emfa. exact FS1.
      + replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -A7 NEWMOD NEWM A5 A6; Z.div_mod_to_equations; lia).
        apply junk_merge; [exact FS1 | rewrite SHE4; eapply fill_is_junk; exact FI | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia]. }

  assert (SLc : aslots L st_r X' m' c).
  { eapply (aslots_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SLOTS0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | |].
    - intros k' Hk' NE'. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|]. split.
      + destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
        apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -Q1 Q2 A1 SZ16; lia | apply ICW_far; clear -Q1 Q2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
      + intros b Hb. destruct (busy_of_Some_facts X c k' b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
    - intros POS. apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS A1 G2 SZ16; lia | apply ICW_far; clear -A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). fold S AB.

      specialize (SL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SL.
      unfold aslot_busy in SL. cbn [xb_st xb_class xb_slot bany xb_alloc] in SL. fold S AB in SL.
      eapply junk_frame; [exact SL | exact MUALL | exact WMALL |]. intros POS.
      apply dj_app; [eapply (RK0_space_c _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS G1 G2 A1; lia | apply ICW_far; clear -G1 G2 A1 A2 RBE HC TSP; unfold c, K_BATCH_CLASS in *; lia]. }

  assert (SSc : aslot_shadow L st_r X' m' c).
  { eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X X' c k); [exact SSH0 | exact NDR | rewrite GR; reflexivity | rewrite GR; reflexivity | | | | exact FB5].
    - intros k' Hk' NE'. fold S. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (right; congruence). split; [reflexivity|].
      destruct (slot_in_region L st c k' ltac:(clear -SZ16; fold S; lia) ltac:(clear -A1; fold au; lia) Hk') as (Q1 & Q2 & Q3). fold RB S au in Q1, Q2, Q3.
      pose proof (slot_aligned L c k' SAL HC) as AL'. fold S in AL'.
      assert (B : 2201439137792 <= shad (aslot_addr L c k') /\ shad (aslot_addr L c k') + shlen S <= shad (RB + au)).
      { rewrite !shad_div, !shlen_div in *. unfold ASHOFF in *. clear -Q1 Q2 AL' SZM SH12 R8 AU8. Z.div_mod_to_equations. lia. }
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -B FB2 FB5 SH2 SH3 SH4; lia | apply ICW_far; clear -B FB2 SH2 SH3 SH4 TL1 TL1u TL4u; lia].
    - intros POS. fold RB mu au in POS |- *. apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15; lia
                                | apply ICW_far; clear -POS FB2 FB5 FB6 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 TL1u; lia].
    - intros _. subst X'. rewrite (busy_of_xrec_self L st X BBatch c k nb b1 ctx l1 l2 drained XB WF). cbn [slot_shadow_bytes]. fold S AB.
      specialize (SSL k KR). rewrite (busy_of_X_self_g L st X BBatch c k nb b1 ctx l1 l2 XB WF) in SSL.
      cbn [slot_shadow_bytes xb_n xb_st bany] in SSL. fold S AB in SSL. rewrite <- !repeat_app in SSL.
      destruct (proj1 (proj1 SSL)) as [LWF _]. cbn [cell_wf] in LWF. rewrite repeat_length in LWF. rewrite LWF in SSL.
      eapply cells_frame; [exact SSL | exact MUALL | exact WMALL |]. cbn [cells_size csize]. rewrite Nat.add_0_r, Z2Nat.id by exact FB5.
      apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -SH12 SH13 FB2 SH1 SH2 SH3 SH4 FB5; lia
                    | apply ICW_far; clear -SH12 SH13 FB5 SH1 SH2 SH3 SH4 FB2 TL1 TL1u TL4u; lia]. }

  assert (AVc : ashadow_avail L st_r m' c).
  { unfold ashadow_avail. cbv zeta. rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA. split; [| exact AZF'].
    eapply azero_frame; [exact AZU | exact MUALL | exact WMALL |]. unfold K_FREEARR_OFF. intros POS.
    apply dj_app; [eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16; lia
                  | apply ICW_far; clear -POS FB2 FB5 FB6 FB7 SH1 SH2 SH3 SH4 SH12 SH13 SH14 SH15 SH16 TL1 TL1u TL4u; lia]. }

  assert (CLS' : forall c', 1 <= c' < 32 -> c' <> c ->
            aregion_cells L st_r m' c' /\ afreearray L st_r X' m' c' /\ aslots L st_r X' m' c' /\ aslot_shadow L st_r X' m' c' /\ ashadow_avail L st_r m' c' /\ acache_cells L st_r X' m' c').
  { intros c' Hc' NE. destruct (CLS c' Hc') as (RC2 & FA2 & SL2 & SS2). pose proof (AVL c' Hc') as AV2. destruct (CACHES c' Hc') as [tl (RH & RCH & RLEN)].
    destruct (PERC c' Hc') as (B1 & B2 & B3 & B4 & B5 & B6 & B7 & BLENF & BLENC & BCNTB & BND & BRANGE).
    pose proof (size_of_class_facts c' Hc') as [SZ' SZM'].
    pose proof (GO c' NE) as G'.
    pose proof (region_other_geo L c c' ALO HC Hc' NE) as REGD. fold RB in REGD.
    destruct REGD as (RD1 & RD2 & RD3 & RD4 & RD5 & RD6 & RD7 & RD8 & RD9 & RD10 & RD11).
    assert (DJR : forall A k, aregion L c' <= A -> A + k <= aregion L c' + 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [eapply (RK0_reg_other _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk RD1 RD2 RD3; lia
                                         | apply ICW_far; clear -HA HB Hk RD1 RD3 TSP; lia]. }
    assert (DJS : forall A k, shad (aregion L c') <= A -> A + k <= shad (aregion L c') + shlen 4294967296 -> 0 <= k ->
                   disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
    { intros A k0 HA HB Hk. apply dj_app; [| apply ICW_far; clear -HA HB Hk RD9 RD10 TL1u; lia].
      destruct RD8 as [LOW|HIGH].
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk LOW RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia.
      - eapply (RK0_sh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); clear -HA HB Hk HIGH RD9 RD10 SB2 SH3 SH4 SH2 SH1 SH13 FB5; lia. }
    assert (DJI : disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) (aregion_info L c') 128).
    { apply dj_app; [eapply (RK0_ri _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD5, ?RIE; clear -Hc' NE HC; lia | apply ICW_far; rewrite ?RD5; clear -Hc' SP1 TSP; lia]. }
    split; [| split; [| split; [| split; [| split]]]].
    - eapply (aregion_cells_frame L _ m m' MUALL WMALL st); [exact RC2 | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | exact DJI].
    - eapply (afreearray_frame L _ m m' MUALL WMALL st st_r X); [exact FA2 | rewrite G'; reflexivity | rewrite G'; reflexivity | subst X'; rewrite (xrec_cls_other st X c k l1 l2 drained c' NE); reflexivity
        | exact BLENF | exact B5 | | clear -B6; lia |].
      + apply DJR; rewrite ?RD4; clear -B5 B6 B2; lia.
      + apply DJS; rewrite ?RD11, ?shlen_div; try (clear -B2 B5 B6; Z.div_mod_to_equations; lia).
    - eapply (aslots_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SL2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | |].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|]. split.
        * destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
          apply DJR; [exact Q1 | clear -Q2 B1 B2; lia | clear -SZ'; lia].
        * intros b Hb. destruct (busy_of_Some_facts X c' k0 b Hb) as (BIn & BC & BK). split; [exact BC|]. split; [exact BK|]. exact (awf_fits L st X b WF BIn).
      + intros POS. apply DJR; clear -B1 B2 POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (aslot_shadow_update L _ m m' MUALL WMALL st st_r X _ c' (-1)); [exact SS2 | unfold ndist; rewrite G'; reflexivity | rewrite G'; reflexivity | rewrite G'; reflexivity | | | | rewrite shlen_div; clear -SZ'; Z.div_mod_to_equations; lia].
      + intros k0 Hk _. subst X'. rewrite (busy_of_xrec_other L st X BBatch c k nb b1 ctx l1 l2 drained XB WF) by (left; exact (not_eq_sym NE)). split; [reflexivity|].
        destruct (slot_in_region L st c' k0 ltac:(clear -SZ'; lia) ltac:(clear -B1; lia) Hk) as (Q1 & Q2 & Q3).
        apply DJS.
        * apply shad_mono. exact Q1.
        * rewrite !shad_div, !shlen_div in *. clear -Q1 Q2 B1 B2 RD7. Z.div_mod_to_equations. lia.
        * rewrite shlen_div. clear -SZ'; Z.div_mod_to_equations; lia.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros HK. exfalso. clear -HK. lia.
    - eapply (ashadow_avail_frame L _ m m' MUALL WMALL st); [exact AV2 | rewrite G'; reflexivity | rewrite G'; reflexivity | |]; unfold K_FREEARR_OFF, K_FREEARR_MAX.
      + intros POS. apply DJS.
        * apply shad_mono. clear -B1; lia.
        * rewrite !shad_div, !shlen_div in *. clear -B1 B2 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
      + intros POS. apply DJS.
        * apply shad_mono. rewrite RD4. clear -B5 B6; lia.
        * rewrite RD4. rewrite !shad_div, !shlen_div in *. clear -B5 B6 RD7. Z.div_mod_to_equations. lia.
        * clear -POS; lia.
    - unfold acache_cells. cbv zeta. rewrite G'. unfold max_count. rewrite CIR. subst X'. rewrite (xrec_cls_other st X c k l1 l2 drained c' NE). exists tl.
      split; [exact (RECS' c' ltac:(clear -Hc'; lia) NE)|]. split; [| exact RLEN].
      eapply u32arr_frame; [exact RCH | exact MUALL | exact WMALL |]. rewrite length_app, length_map.
      replace (Z.of_nat (length (xc_cache (x_cls X c')) + length tl)) with 16 by (clear -RLEN; lia).
      apply dj_app; [eapply (RK0_rec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); rewrite ?RD6, ?CAE; clear -Hc' NE HC; lia | change (4 * 16) with 64; apply ic_W_disjoint_chunks]. }

  assert (BB : forall b, In b (x_busy X') ->
      al_space_beg L <= xb_alloc L b /\ xb_alloc L b + size_of_class (xb_class b) <= al_space_beg L + 137438953472
      /\ (xb_alloc L b + size_of_class (xb_class b) <= RB + mu \/ xb_alloc L b + size_of_class (xb_class b) <= RB \/ RB + 4294967296 <= xb_alloc L b)).
  { intros b Hb. subst X'. pose proof (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb) as HbX. apply In_xrec in Hb.
    destruct (BUSY b HbX) as [CLB _].
    destruct (PERC (xb_class b) CLB) as (Q1 & Q2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & QR).
    pose proof (size_of_class_facts (xb_class b) CLB) as [QS _].
    assert (KB : 0 <= xb_slot b < ndist st (xb_class b)).
    { apply QR. apply in_app_iff. right. apply in_app_iff. right. unfold busy_slots. apply in_map_iff. exists b. split; [reflexivity|].
      apply filter_In. split; [exact HbX| apply Z.eqb_refl]. }
    pose proof (slot_in_region L st (xb_class b) (xb_slot b) ltac:(clear -QS; lia) (proj1 Q1) KB) as (P5 & P4 & P0).
    unfold xb_alloc.
    destruct (Z.eq_dec (xb_class b) c) as [EC|NC].
    - rewrite EC in P5, P4, Q1, Q2 |- *. fold RB au mu S in P5, P4, Q1, Q2.
      split; [clear -P5 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. split; [clear -P4 A1 A2 RBE HC; unfold c, K_BATCH_CLASS in *; lia|]. left. clear -P4 A1; lia.
    - pose proof (region_other_geo L c (xb_class b) ALO HC CLB NC) as (R1 & R2 & R3 & _). fold RB in R2.
      split; [clear -P5 R1; lia|]. split; [clear -P4 Q1 Q2 R3; lia|].
      right. destruct R2 as [D|D]; [left; clear -D P4 Q1 Q2; lia | right; clear -D P5; lia]. }

  assert (DJimg : forall A k, 65536 <= A -> 0 <= k -> A + k <= 6492160 ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [eapply (RK0_img _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); assumption | apply ICW_far; clear -H1 H3 TL4u; lia]. }
  assert (DJt : forall A k, al_t L <= A -> 0 <= k ->
            (A + k <= al_t L + 288 \/ (al_t L + 2768 <= A /\ A + k <= al_t L + 2784) \/ (al_t L + 2792 <= A /\ A + k <= al_t L + 2800) \/ (al_t L + 3168 <= A /\ A + k <= al_t L + 4096)) ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_t; clear -H3; lia].
    destruct H3 as [H3|[H3|[H3|H3]]];
      [ eapply (RK0_tlow _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_tstat _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)
      | eapply (RK0_thigh _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF)]; clear -H1 H2 H3; lia. }
  assert (DJctx : forall A k, al_ctx L <= A -> A + k <= al_ctx L + 4096 -> 0 <= k ->
            disjoint_from (Wk0 (bv_unsigned sp) (al_t L) CA FA nf mfa' SHF0 SHF1 RI ++ ic_W L 1 31) A k).
  { intros A k0 H1 H2 H3. apply dj_app; [| apply ICW_far; clear -H1 H2 H3 CL5; lia].
    eapply (RK0_obj _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ KF); atop_facts; clear -H1 H2 H3 CL1u CL3 CL2 CL5 SCX; unfold AIMG_HI in *; lia. }

  assert (WF' : awf L st_r X').
  { subst X'. eapply (awf_xrec L st X BBatch c k nb b1 ctx l1 l2 drained XB WF ltac:(intros p; discriminate) DRC st_r mfa');
      [exact EF10 | exact EF9 | exact CIR | exact EF1 | exact EF2 | exact GO | | clear -NEWB; unfold K_FREEARR_MAX; subst nf'; unfold rnf', rhalf; fold nf half; destruct drained; lia | exact NEWMOD].
    rewrite GR. unfold rnf', rcnt', rcnt, rhalf. fold nf half cnt. subst nf' cnt'. destruct drained; f_equal; lia. }
  assert (RT' : arep_rt L m').
  { eapply arep_rt_frame; [exact MUALL | exact WMALL | exact RT |]. unfold rt_hulls, ATP88, ATSD.
    repeat (apply Forall_cons; [cbn [fst snd]; first [apply DJimg; clear; lia | apply DJctx; clear; lia] |]). apply Forall_nil. }
  assert (INST' : ainstance L st_r m').
  { eapply ainstance_frame; [exact MUALL | exact WMALL | exact INST | exact EF8 | exact EF7 | | |]; apply DJimg; clear; unfold AINSTANCE; lia. }
  assert (THR' : athread L st_r X' m').
  { unfold athread. split; [| split; [| split; [| split; [| split]]]].
    - eapply cells_frame; [exact T0c | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - eapply cells_frame; [exact T40 | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia.
    - intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact ACc | exact (proj2 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))].
    - apply (junk_merge m' (al_t L + 2768) 16 16); [| | clear; lia | clear; lia].
      + destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [J16 _].
        eapply junk_frame; [exact J16 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
      + apply (junk_merge m' (al_t L + 2768 + 16) 8 8); [| | clear; lia | clear; lia].
        * replace (al_t L + 2768 + 16) with (al_t L + 2784) by (clear; lia). pose proof (junk_of_cells m' _ _ STA') as J. cbn in J. exact J.
        * destruct (junk_split m (al_t L + 2768) 24 8 CSTATS ltac:(clear; lia) ltac:(clear; lia)) as [_ J8].
          replace (al_t L + 2768 + 16 + 8) with (al_t L + 2768 + 24) by (clear; lia).
          eapply junk_frame; [exact J8 | exact MUALL | exact WMALL | intros _; apply DJt; clear; lia].
    - exists sj'. split; [exact STATS' | exact LSJ'].
    - eapply cells_frame; [exact UNW | exact MUALL | exact WMALL |]. cbn [cells_size csize Nat.add]. apply DJt; clear; lia. }

  pose proof (ao_space L ALO) as RSP.
  set (WH := [(bv_unsigned sp - 688, bv_unsigned sp); (al_t L + 208, al_t L + 3168); (RI, RI + 128);
              (FA + 4 * nf, FA + 536870912); (SHF0, shad RB + 536870912)]).
  assert (MUH : munch WH m m').
  { eapply munch_weaken; [| exact MUALL]. unfold sub_fp. intros x Hx. subst WH. cbn [outside] in Hx. destruct Hx as (O1 & O2 & O3 & O4 & O5 & _).
    apply outside_app. split.
    - cbn [outside]. clear -O1 O2 O3 O4 O5 SH5 FB2 NEWB CAE HC SH10 SH9 SHE1 NEWM A5 A6.
      pose proof (shlen_nonneg (536870912 - mfa') ltac:(lia)). unfold c, K_BATCH_CLASS in *. repeat split; try exact I; lia.
    - apply ic_W_outside; [unfold acache_addr; clear -O2; lia | clear; cbn; lia | clear; lia]. }
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR.
  assert (HQ0 : AQdr (qr_unbatch R) 0 0 L st X' m) by (subst X'; eapply AQdr_unbatch; [exact HQ | exact EB | exact EP | exact XB | exact WF]).
  assert (QU : quar_untouched L X' WH).
  { unfold quar_untouched. subst WH. unfold AINSTANCE in *.
    repeat (apply Forall_cons; [cbn [fst snd];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      split; [clear -CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia|];
      intros b Hb; destruct (BB b Hb) as (Bb1 & Bb2 & Bb3); destruct (xb_st b); [exact I| |];
      clear -Bb1 Bb2 Bb3 CEIL LO TL1 TL1u TL4u TL2 TSP SP1 SP2 RIE RBE FAE HC A1 A2 A5 G1 G2 G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 FB5 SB2 SH6 NEWB; unfold c, K_BATCH_CLASS in *; lia |]).
    apply Forall_nil. }
  assert (QSM : quar_same st st_r X' X').
  { unfold quar_same. rewrite EF3, EF4, EF5, EF6, EF10. repeat (split; [reflexivity|]).
    split; intros b Hb; destruct (xb_st b); first [exact I | exact Hb]. }
  assert (HQ' : AQdr (qr_unbatch R) 0 0 L st_r X' m').
  { eapply AQdr_frame; [exact HQ0 | exact MUH | exact WMALL | exact QU | exact QSM]. }
  assert (SU : sec_untouched L WH).
  { unfold sec_untouched, aknown. subst WH. unfold AINSTANCE, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 4 right; left; clear -Ha CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 5 right; left; clear -Ha TL1 TL1u TL4u TL2; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RIE HC; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; do 7 right; left; clear -Ha RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; intros a Ha; right; left; clear -Ha HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (SSM : sec_same st st_r).
  { unfold sec_same. rewrite EF7, EF8, EF9, EF1. split; [reflexivity|]. split; [reflexivity|]. split; [reflexivity|]. split; [intros; tauto|].
    split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); apply Permutation_refl|]. split; [subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity| subst st_r; unfold put_cls, set_cls, init_cache; destruct (a_cinit st); reflexivity]. }
  assert (HS' : ASECc cs L st_r X' m').
  { eapply (hs_frame _ (HL (qr_unbatch R) cs) L st st_r X X' m m'); [exact HS | exact MUH | exact WMALL | exact SU | | exact SSM].

    unfold c6_untouched. subst WH. unfold K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.
    assert (HCk : 1 <= c < K_NUM_CLASSES) by (unfold c, K_BATCH_CLASS, K_NUM_CLASSES; clear; lia).
    assert (SHBx : 0x7fff7000 <= shad (al_space_beg L) /\ shad (al_space_beg L) + 17179869696 <= 0x10007fff8000).
    { rewrite !shad_div. unfold ASHOFF. pose proof atop_range as ATRx. pose proof (ao_res L ALO) as (_ & _ & ORSx & _). pose proof (ao_res_hi L ALO) as ORHx.
      clear -RSP ORSx ORHx ATRx. Z.div_mod_to_equations. lia. }
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; left; clear -CEIL LO; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; right; left; clear; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_ri L c _ _ ALO HCk); [subst RI; clear; lia| subst RI; clear; lia| right; right; reflexivity] |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 3 right; left; unfold AC6U.TwinB.RIP; clear -RSP RBE FAE HC A5; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_cons; [cbn [fst snd]; apply (AC6U.TwinB.c6p_std L _ _ ALO); intros _; do 4 right; left; clear -HC SH9 SH10 SH11 SH13 SH1 SH2 SH3 FB5 SHBx; unfold c, K_BATCH_CLASS in *; lia |].
    apply Forall_nil. }
  assert (HD' : AD L m').
  { eapply (hd_frame _ (HL R cs) L m m'); [exact HD | exact MUH | exact WMALL |]. subst WH.
    pose proof (ao_nodes L ALO) as (_ & ON1 & ON3 & ONs & _). pose proof (ao_store L ALO) as (_ & OS1 & OS3 & OSs & _). unfold sclr, KLS in ONs, OSs.
    pose proof (ad_nodes_res L ALO) as DNR. pose proof (ad_store_res L ALO) as DSR. pose proof (ad_t_nodes L ALO) as DTN. pose proof (ad_t_store L ALO) as DTS.
    unfold adisj, K_SPACE_SIZE, K_SPACE_EXTRA in *. change (2^37) with 137438953472 in *.

    repeat (apply Forall_cons; [cbn [fst snd]; intros a Ha; split; [| split];
      [ clear -Ha CEIL LO TL4u TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 ON1 ON3 ONs DNR DTN; unfold c, K_BATCH_CLASS in *; lia
      | clear -Ha CEIL LO TL2 SP1 SP2 RSP RIE RBE FAE HC A5 A6 NEWB G5 G6 SH12 SH13 SH1 SH2 SH3 SH4 SH9 SH10 SB2 SH6 FB5 OS1 OS3 OSs DSR DTS; unfold c, K_BATCH_CLASS in *; lia ] |]). apply Forall_nil. }
  assert (AR' : AREP (AHr (qr_unbatch R) cs) L st_r X' m').
  { split; [exact WF'|]. split; [exact RT'|]. split; [exact INST'|]. split; [exact THR'|]. split.
    { intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE].
      - split; [exact RCc|]. split; [exact FAc|]. split; [exact SLc| exact SSc].
      - destruct (CLS' c' Hc' NE) as (Y1 & Y2 & Y3 & Y4 & Y5 & Y6). split; [exact Y1|]. split; [exact Y2|]. split; [exact Y3| exact Y4]. }
    split; [exact HQ'|]. split; [exact HS'|]. split; [exact HD'|].
    split; [eapply arelro_frame; [exact MUALL | exact HRO | apply DJimg; clear; unfold ARELRO_LO, ARELRO_HI; lia]|].
    split; [eapply arep_rt2_frame; [exact MUALL | exact WMALL | exact RT2 | | |]; apply DJimg; clear; lia|].
    split; [| eapply arep_rt3_frame; [exact MUALL | exact WMALL | exact RT3 |]; unfold rt3_hulls;
              repeat (apply Forall_cons; [cbn [fst snd]; apply DJimg; clear; lia |]); apply Forall_nil].
    intros c' Hc'. destruct (Z.eq_dec c' c) as [->|NE]; [exact AVc | exact (proj1 (proj2 (proj2 (proj2 (proj2 (CLS' c' Hc' NE))))))]. }

  assert (ARNG' : arng L RNG' st_r).
  { pose proof (arng_mono L RNG RNG' st FPLE ARNG) as AM.
    destruct AM as (Z1 & Z2 & Z3 & Z4 & Z5 & Z6 & Z7 & Z8 & Z9 & RC & RPA & RSC & RPSH).
    unfold arng. split; [exact Z1|]. split; [exact Z2|]. split; [exact Z3|]. split; [exact Z4|]. split; [exact Z5|].
    split; [exact Z6|]. split; [exact Z7|]. split; [exact Z8|]. split; [exact Z9|].
    split; [| split; [rewrite EF8; exact RPA| split; [rewrite (sec_chunks_of_eq st st_r EF1 EF3 EF5); exact RSC| exact RPSH]]].
    intros c' Hc'. cbv zeta. destruct (Z.eq_dec c' c) as [->|NE].
    - rewrite GR. cbn [c_mapped_user c_mapped_free_array]. fold RB FA.
      destruct (RC c HC) as (Q1 & Q2 & Q3 & Q4). fold RB FA mu mfa in Q1, Q2, Q3, Q4.
      split; [exact Q1|]. split; [exact Q2|]. split.
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q3|].
        replace mfa' with (mfa + (mfa' - mfa)) by (clear; lia). apply rng_merge; [exact BW | clear -A5 A6; lia | clear -NEWM; lia | exact Q3 | exact RF].
      + destruct MFD as [Emfa|(_ & _ & Emfa & _ & RF & RSF & BW)]; [rewrite Emfa; exact Q4|].
        assert (M8c : mfa mod 8 = 0 /\ mfa' mod 8 = 0) by (clear -A7 NEWMOD; Z.div_mod_to_equations; lia). destruct M8c as [M8c M8d].
        replace (shlen mfa') with (shlen mfa + shlen (mfa' - mfa)) by (rewrite !shlen_div; clear -M8c M8d; Z.div_mod_to_equations; lia).
        apply rng_merge; [exact BW | rewrite shlen_div; clear -A5 A6; Z.div_mod_to_equations; lia | rewrite shlen_div; clear -NEWM; Z.div_mod_to_equations; lia | exact Q4 |].
        rewrite SHE4. exact RSF.
    - rewrite (GO c' NE). exact (RC c' Hc'). }

  exists X', mfa'.
  split; [exact MU2|]. split; [exact WMALL|]. split; [clear -NEWB NEWM; lia|]. split; [exact AR'|]. split; [exact ARNG'|]. split; [exact CIR|].
  split; [exact EF1|]. split; [exact EF2|]. split; [exact EF3|]. split; [exact EF4|]. split; [exact EF5|]. split; [exact EF6|].
  split; [exact EF7|]. split; [exact EF8|]. split; [exact EF9|]. split; [exact EF10|]. split; [exact GO|].
  split; [intros b Hb; subst X'; exact (xrec_sub st X BBatch c k nb b1 ctx l1 l2 drained XB b Hb)|].
  intros b p Hb Sb. subst X'. exact (xrec_live st X BBatch c k nb b1 ctx l1 l2 drained XB ltac:(intros p'; discriminate) b p Hb Sb).
Qed.

Lemma pendb_busy : forall L st X R m kb,
  AQdr R 0 0 L st X m -> qr_pendb R = [kb] ->
  exists nb b1 ctx l1 l2, x_busy X = l1 ++ bany BBatch K_BATCH_CLASS kb nb b1 ctx :: l2.
Proof.
  intros L st X R m kb (_ & _ & _ & _ & _ & _ & CP & _) EB.
  destruct (qcoupled_rec_bslot_busy L st X R kb CP ltac:(unfold qr_bslots; rewrite EB; apply in_app_iff; right; left; reflexivity)) as (b & Hb & Sb & Cb & Kb).
  destruct (in_split _ _ Hb) as (l1 & l2 & E). destruct b as [bc bk bn bs bb1 bctx]. cbn in Sb, Cb, Kb. subst bs bc bk.
  exists bn, bb1, bctx, l1, l2. exact E.
Qed.

Theorem acdealloc24 :
  forall {RT} (k : astate -> AM RT) (Q : RT -> footprint -> machine_state -> Prop)
         (L : alayout) (RNG : footprint)
         (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
         (F : bvmap 5 word) (fc : bv 32) (m : amem) (st : astate) (X : aconc) (R : qrconc) (cs : list achunk)
         (kb lo : Z),
  alayout_ok L -> arng L RNG st -> AREP (AHr R cs) L st X m ->
  qr_pendb R = [kb] -> qr_pend R = [] ->
  mem_inv bsegs m ->
  stk bsegs m lo (bv_unsigned sp) -> ATOP <= lo -> lo <= bv_unsigned sp - 688 ->
  tp = Z_to_bv 64 ATP ->
  a0 = Z_to_bv 64 (al_t L + 208) -> a1 = Z_to_bv 64 AINSTANCE -> a2 = Z_to_bv 64 K_BATCH_CLASS -> a3 = Z_to_bv 64 (abatch_addr L kb) ->
  rng RNG lo (bv_unsigned sp - lo) ->
  (forall stX X' RNG' ms', acd24_ret L RNG ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc st X R cs lo m stX X' RNG' ms' ->
     implS bsegs RNG' (aembed ATOP (k stX)) (epostF Q) ms') ->
  implS bsegs RNG (aembed ATOP (cache_dealloc st K_BATCH_CLASS k)) (epostF Q)
        (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
            F (Z_to_bv 64 cdealloc_entry) fc None m (seg_rom bsegs)).
Proof.
  intros RT k Q L RNG ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m st X R cs
         kb lo ALO ARNG AR EB EP MI ST CEIL LO TP Ha0 Ha1 Ha2 Ha3 RSTK KONT.
  set (c := K_BATCH_CLASS) in *.
  pose proof AR as AR0. destruct AR0 as (WF & RT0 & INST & THR & CLS & HQ & HS & HD & HRO & RT2 & AVL & RT3).
  cbn [ah_quar ah_sec ah_depot AHr ARecyc1P.AHr] in HQ, HS, HD.
  destruct (pendb_busy L st X R m kb HQ EB) as (nb & b1 & ctx & l1 & l2 & XB). fold c in XB.
  destruct (any_range L st X BBatch c kb nb b1 ctx l1 l2 XB WF) as [HC KR].
  destruct THR as (T0c & T40 & CACHES & CSTATS & [sj [STATS LSJ]] & UNW).
  pose proof WF as WF0. destruct WF0 as (SBE & PAE & SAL & SLO & SHI & PERC & OUTC & BUSY & LIVE & FRESH & UNIQ).
  destruct (PERC c HC) as (A1 & A2 & A3 & A4 & A5 & A6 & A7 & LENF & LENC & CNTB & ND & RANGE).
  destruct (CLS c HC) as (RCELLS & FARR & SLOTS & SSH). destruct (AVL c HC) as [AZU AZF].
  destruct RCELLS as (MTX16 & REG & RJ4 & EXH & RJ56). destruct FARR as (FL & FJ & FSJ).
  pose proof (alayout_space L ALO) as (SP1 & SP2 & SP3 & SP4).
  pose proof (alayout_t L ALO) as (TL1 & TL2 & TL3 & TL4).
  pose proof (alayout_ctx L ALO) as (CL1 & CL2 & CL3 & CL4 & CL5).
  pose proof TL1 as TL1u. pose proof TL4 as TL4u. pose proof CL1 as CL1u. unfold sclr, iclr, KLS, AIMG_LO, AIMG_HI in TL1u, TL4u, CL1u.
  pose proof (alayout_res_disj L ALO) as [SCX TSP].
  pose proof ARNG as ARNG0. destruct ARNG0 as (RIMG & RT4 & RCTX & RNO & RSTO & RRI & RFK & RSFK & RDTLS & RCLS & RPA & RSECS & RPSH).
  destruct (RCLS c HC) as (RREG & RSREG & RFA & RSFA).
  pose proof RT0 as RT1.
  destruct RT1 as (GPG & GOT & GOT80 & RIC & LS1 & REAL & IMAX4 & FLG5 & FLG & HPP & SHB & CANP & TI & TK & INI2 & LAY & MCS & OOM3
                    & PGC & HK2 & CF8 & CF34 & CSMT & T88 & TSD & LS2 & CT8 & CT).
  destruct RT2 as (DPM & MLIM & RWCS).
  destruct INST as (I32 & I48 & I64 & I72 & I112 & I680 & I984 & I40 & I56).
  assert (MC : m3_cells L m).
  { unfold m3_cells, poison_cells, rmap_cells, AINSTANCE in *. repeat lazymatch goal with |- _ /\ _ => split end; assumption. }
  pose proof MTX16 as MTX. rw_split MTX 1%nat MTX MTXb. clear MTXb.
  destruct (junk_split m (al_t L + 2768) 16 16 CSTATS ltac:(lia) ltac:(lia)) as [_ CSb].
  destruct (junk_split m (al_t L + 2768 + 16) 8 8 CSb ltac:(lia) ltac:(lia)) as [CS8 _].
  replace (al_t L + 2768 + 16) with (al_t L + 2784) in CS8 by lia. destruct (c8_of_junk m _ CS8) as [sta STA].
  destruct (CACHES c HC) as [tail (RECc & CH & LCH)]. cbv zeta in CH. cbv zeta in LCH.
  pose proof (cache_vals_lt L st X c tail WF HC LCH) as CH31.
  destruct (nf_bound L st X c WF HC) as [NFA NFN].
  pose proof (slot_geo L st X c kb ALO WF HC KR) as (S1 & S2 & AL16 & G1 & G2 & G3 & G4 & G5 & G6 & G7 & G8 & R8 & M8).

  eapply (cdealloc_spec RNG k Q ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m L st c (abatch_addr L kb) lo
            sj (map (fun k0 => Z_to_bv 64 (acompact c k0)) (xc_cache (x_cls X c)) ++ tail) sta);
  try lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- stk _ _ _ _ => exact ST
       | |- ATOP <= _ => exact CEIL
       | |- _ <= bv_unsigned _ - _ => exact LO
       | |- mem_inv _ _ => exact MI
       | |- m3_cells _ _ => exact MC
       | |- rw_cells _ _ (aregion_info _ _) _ => exact MTX
       | |- rw_cells _ _ (aregion_info _ _ + 16) _ => exact REG
       | |- junk_at _ (aregion_info _ _ + 72) _ => exact RJ56
       | |- junk_at _ (afreearr _ _ + _) _ => exact FJ
       | |- rw_cells _ _ (al_t _ + 2784) _ => exact STA
       | |- u64arr _ _ _ _ => exact STATS
       | |- u32arr _ _ _ _ => exact CH
       | |- Forall _ _ => exact CH31
       | |- length (map _ _ ++ _) = _ => rewrite length_app, length_map; exact LCH
       | |- length _ = _ => exact LSJ
       | |- azero _ (shad (afreearr _ _ + _)) _ => exact AZF
       | |- a_space_beg _ = _ => exact SBE
       | |- rng_aimg _ => exact RIMG
       | |- rng _ _ (bv_unsigned _ - _) => exact RSTK
       | |- rng _ (aregion_info _ _) _ => eapply rng_sub'; [exact RRI|]; unfold aregion_info, ARI_STRIDE, K_SPACE_EXTRA; clear -HC; unfold K_NUM_CLASSES in HC; lia
       | |- rng _ (afreearr _ _) _ => exact RFA
       | |- rng _ (al_ctx _) _ => eapply rng_sub'; [exact RCTX|]; clear; lia
       | |- rng _ (al_t _) _ => exact RT4
       | |- @eq word _ _ => first [exact TP | exact Ha0 | exact Ha1 | exact Ha2 | exact Ha3]
       | |- _ \/ _ => first [exact CL5 | exact TSP | clear -SCX; unfold K_SPACE_SIZE, K_SPACE_EXTRA in *; lia]
       | |- forall j, _ -> arec_hdr _ _ _ _ _ _ => intros j Hj; destruct (CACHES j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as [tl (RH & _ & _)]; exact RH
       | |- forall j, _ -> 0 <= _ <= _ => intros j Hj; destruct (PERC j ltac:(unfold K_NUM_CLASSES; clear -Hj; lia)) as (_ & _ & _ & _ & _ & _ & _ & _ & _ & CB2 & _); exact CB2
       end.
  all: lazymatch goal with
       | |- forall stX RNG' m' t0', _ => idtac
       | |- aregion _ _ <= abatch_addr _ _ => exact G1
       | |- abatch_addr _ _ < aregion _ _ + _ => unfold ndist in KR; unfold K_REGION, K_FREEARR_OFF in *; change (2^32) with 4294967296; unfold abatch_addr; fold c; clear -G1 G2 G3 G4 S1; lia
       | |- al_ctx _ + 4096 <= _ => clear -CL2; atop_facts; lia
       | |- ?g => first [assumption | idtac "REMAINS" g]
       end.

  intros stX RNG' m' t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' CDR.
  destruct (cd24_store L RNG RNG' sp m m' st stX X R cs kb nb b1 ctx lo l1 l2 tail ALO ARNG AR EB EP XB CEIL LO CH LCH CDR)
    as (X' & mfa' & MU & WM & MFB & AR' & ARNG' & CIN & L1 & L2 & L3 & L4 & L5 & L6 & L7 & L8 & L9 & L10 & GC & XS & XL).
  destruct CDR as (FPLE & dr & mfa2 & sj2 & sta2 & _ & _ & _ & _ & _ & _ & _ & _ & _ & MIT & STT & _).
  eapply KONT. unfold acd24_ret. split; [exact FPLE|]. do 16 eexists. exists mfa'. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MIT|]. split; [exact STT|]. split; [exact MFB|]. split; [exact AR'|]. split; [exact ARNG'|].
  split; [exact CIN|]. split; [exact L1|]. split; [exact L2|]. split; [exact L3|]. split; [exact L4|]. split; [exact L5|]. split; [exact L6|].
  split; [exact L7|]. split; [exact L8|]. split; [exact L9|]. split; [exact L10|]. split; [exact GC|].
  split; [exact XS| exact XL].
Qed.
End P.
End CANSEC1.
End ACdeallocP.
End TwinB.
