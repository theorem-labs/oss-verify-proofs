(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_tr_scan1 Z_tr_cb3 Z_tr_bt1 Z_tr_bt2 Z_tr_bt10. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_tr_bt12. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_tr_bt13.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Lemma find_char : forall t s FC DL HP HL HM DP BC OL SL MC ML r,
  r = gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (ML - 1) -> 0 <= r -> 0 <= ML ->
  r <= ML - 1 /\ (forall j, r < j <= ML - 1 -> arr_get BC j = 0) /\ arr_get BC r <> 0.
Proof.
  intros until r. intros Er Hr HML. rewrite Er in Hr.
  destruct (find_spec (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL MC) (ML - 1) Hr) as (A & B & C). rewrite <- Er in A, B, C, Hr.
  split; [exact A|]. split.
  - intros j Hj. rewrite <- (bt_bl_count_get s t FC DL HP HL HM DP BC OL SL MC j). apply B. exact Hj.
  - destruct C as [C|C]; [exfalso; lia|]. rewrite bt_bl_count_get in C. exact C.
Qed.

Lemma lor_hi32 : forall x, 0 <= x -> Z.lor 4294967295 (x * 4294967296) = x * 4294967296 + 4294967295.
Proof.
  intros x Hx. rewrite Z.add_comm. symmetry. apply Z.add_nocarry_lor.
  change 4294967295 with (Z.ones 32). rewrite Z.land_comm, Z.land_ones by lia. change (2^32) with 4294967296. apply Z.mod_mul. lia.
Qed.

(* [comment removed for export] *)
Definition gl2R (L : dlay) (T ovf mc ML : Z) (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L + 2976 + ML * 2)) (wz ovf) (wz 18446744069414584320) (wz (dl_As L + 2976 + ML * 2)) (wz ((ML + 1) * 4294967296)) (wz 2) a5 a6 a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz ML) s10 s11 t3 t4 t5 t6.

Lemma wz_sub32 : forall x, wz (x * 4294967296 + 18446744069414584320) = wz ((x - 1) * 4294967296).
Proof.
  intros x. apply Z_to_bv_eqm. replace (x * 4294967296 + 18446744069414584320) with ((x - 1) * 4294967296 + 1 * 2^64) by lia.
  rewrite Z.mod_add by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Definition gl2fR (L : dlay) (T ovf mc ML A0 A6 : Z) (a7 : word) (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 (wz (dl_As L + 2976)) (wz (dl_As L + 2976 + ML * 2)) (wz A0) (wz 18446744069414584320) (wz (dl_As L + 2976 + ML * 2))
      (wz ((ML + 1) * 4294967296)) (wz 2) (wz ovf) (wz A6) a7
      (wz T) (wz mc) (wz (dl_As L + 5300)) s5 s6 (wz T) (wz mc) (wz ML) s10 s11 t3 t4 t5 t6.

(* [comment removed for export] *)
Lemma gl2_find : forall (d : nat) (P : machine_state -> Prop) (L : dlay) (T ovf mc ML b r A0 A6 : Z) (BC : arr) (a7 : word)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L ->
  Z.of_nat d = b - r -> 0 <= r -> b < 15 -> (forall j, r < j <= b -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 ->
  A0 = (b + 2) * 4294967296 -> A6 = dl_As L + 2976 + (b + 1) * 2 ->
  evt psegs P (MS (gl2fR L T ovf mc ML ((r + 1) * 4294967296) (dl_As L + 2976 + r * 2) (wz (arr_get BC r)) ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c2c8) fc None m (seg_rom psegs)) ->
  evt psegs P (MS (gl2fR L T ovf mc ML A0 A6 a7 ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c2b8) fc None m (seg_rom psegs)).
Proof.
  induction d as [|d IH]; intros until m; intros BLC MI LAY Ed Rr Rb Z0 NZ RV E0 E6 K; subst A0 A6.
  - assert (b = r) by lia. subst b.
    pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read psegs m _ (av16 BC 16) r _ (wa (dl_As L + 2976 + (r + 1) * 2 + -2)) BLC (av16_nth BC 16 r ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    unfold gl2fR. zs2. rewrite zx16_small by lia. zs2. zs2.
    zstep. br_cases K2; [exfalso; lia|].
    rewrite wz_sub32. reg_as ((r + 2 - 1) * 4294967296) ((r + 1) * 4294967296). reg_as (dl_As L + 2976 + (r + 1) * 2 + -2) (dl_As L + 2976 + r * 2).
    exact K.
  - pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
    pose proof (u16arr_read psegs m _ (av16 BC 16) b _ (wa (dl_As L + 2976 + (b + 1) * 2 + -2)) BLC (av16_nth BC 16 b ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDb.
    rewrite (Z0 b ltac:(lia)) in RDb.
    unfold gl2fR. zs2. rewrite zx16_small by lia. zs2. zs2.
    zstep. br_true.
    rewrite wz_sub32.
    eapply (IH P L T ovf mc ML (b - 1) r _ _ BC); [exact BLC| exact MI| exact LAY| lia| exact Rr| lia| intros j Hj; apply Z0; lia| exact NZ| exact RV| lia| lia| exact K].
Qed.

Lemma shr31 : forall x, 0 <= x -> Z.shiftr (x * 4294967296) 31 = x * 2.
Proof. intros. rewrite Z.shiftr_div_pow2 by lia. change (2^31) with 2147483648. replace (x * 4294967296) with (x * 2 * 2147483648) by lia. apply Z.div_mul. lia. Qed.
Lemma le2_wrap16 : forall x y, x = y -> le2 (wz x) = le2 (wz (wrap16 y)).
Proof. intros x y ->. apply le2_wz_mod. rewrite lo16_unsigned_wz, wrap16_mod, lo16_idem. reflexivity. Qed.

Notation Wg2 L := [(dl_As L + 2976, dl_As L + 3008)] (only parsing).

(* [comment removed for export] *)
Definition gl2_iter_post (L : dlay) (T ovf mc ML : Z) (BC' : arr)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 pcx m',
    ms' = MS (gl2R L T (ovf - 2) mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz pcx) fc None m' (seg_rom psegs)
    /\ munch (Wg2 L) m m' /\ wmono psegs m m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ ((pcx = 0x1c2ac /\ 0 < ovf - 2) \/ (pcx = 0x1c2f8 /\ ovf - 2 <= 0)).

Lemma gl2_iter : forall (L : dlay) (T ovf mc ML r : Z) (BC : arr)
    (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L -> arr_len BC = 16 ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> 0 <= r <= ML - 1 -> (forall j, r < j <= ML - 1 -> arr_get BC j = 0) -> arr_get BC r <> 0 -> 0 <= arr_get BC r < 65536 ->
  evt psegs (gl2_iter_post L T ovf mc ML (bl_adj ML BC r) ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 F fc m)
      (MS (gl2R L T ovf mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c2ac) fc None m (seg_rom psegs)).
Proof.
  intros until m. intros BLC MI LAY LBC RML Ro Rr Z0 NZ RV.
  pose proof (munch_refl (Wg2 L) m) as MU. pose proof (wmono_refl psegs m) as WM.
  unfold gl2R. zs2. zs2. zs2.
  eapply (gl2_find (Z.to_nat (ML - 1 - r)) _ L T ovf mc ML (ML - 1) r _ _ BC); [exact BLC| exact MI| exact LAY| lia| lia| lia| exact Z0| exact NZ| exact RV| lia| lia|].
  pose proof LAY as LAY0. lay_open LAY0. pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  unfold gl2fR. zs2. zs2.
  rewrite signed_wz, shr31 by lia.
  a16_store BLC BC 16 (dl_As L + 2976) r (wrap16 (arr_get BC r - 1)) ltac:(apply le2_wrap16; lia).
  set (BC1 := arr_set BC r (wrap16 (arr_get BC r - 1))) in *.
  match goal with H : u8arr psegs ?mm _ (u16s (av16 BC1 16)) |- _ =>
    pose proof (u16arr_read psegs mm _ (av16 BC1 16) (r + 1) _ (wa (dl_As L + 2976 + (r + 1) * 2)) H (av16_nth BC1 16 (r + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD1 end.
  zs2. zs2. zs2.
  a16_store BLC BC1 16 (dl_As L + 2976) (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2)) ltac:(apply le2_add_sx16).
  set (BC2 := arr_set BC1 (r + 1) (wrap16 (arr_get BC1 (r + 1) + 2))) in *.
  match goal with H : u8arr psegs ?mm _ (u16s (av16 BC2 16)) |- _ =>
    pose proof (u16arr_read psegs mm _ (av16 BC2 16) ML _ (wa (dl_As L + 2976 + ML * 2)) H (av16_nth BC2 16 ML ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RD2 end.
  zs2. zs2.
  a16_store BLC BC2 16 (dl_As L + 2976) ML (wrap16 (arr_get BC2 ML - 1)) ltac:(replace (arr_get BC2 ML - 1) with (arr_get BC2 ML + -1) by lia; apply le2_add_sx16).
  zs2. zstep.
  assert (EBA : bl_adj ML BC r = arr_set BC2 ML (wrap16 (arr_get BC2 ML - 1))) by reflexivity.
  br_cases K; reg_as (ovf + -2) (ovf - 2).
  - apply evt_done. unfold gl2_iter_post, gl2R. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. left. split; [reflexivity| lia].
  - apply evt_done. unfold gl2_iter_post, gl2R. do 5 eexists. split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|].
    split; [rewrite EBA; exact BLC|]. right. split; [reflexivity| lia].
Qed.

(* [comment removed for export] *)
Lemma bl_adj_len : forall ML BC r, arr_len (bl_adj ML BC r) = arr_len BC.
Proof. intros. unfold bl_adj. rewrite !arr_len_set. reflexivity. Qed.
Lemma arr_set_range16 : forall (a : arr) i v n, (forall j, 0 <= j < n -> 0 <= arr_get a j < 65536) -> forall j, 0 <= j < n -> 0 <= arr_get (arr_set a i (wrap16 v)) j < 65536.
Proof.
  intros a i v n H j Hj. rewrite arr_get_set. destruct ((i =? j) && arr_inb a i); [apply SendModel.wrap16_range'| apply H; exact Hj].
Qed.
Lemma bl_adj_range : forall ML BC r, (forall j, 0 <= j < 16 -> 0 <= arr_get BC j < 65536) -> forall j, 0 <= j < 16 -> 0 <= arr_get (bl_adj ML BC r) j < 65536.
Proof. intros ML BC r H. unfold bl_adj. apply arr_set_range16. apply arr_set_range16. apply arr_set_range16. exact H. Qed.

(* [comment removed for export] *)
Definition gl2_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP : arr) (OL SL : Z) (R : deflate_state)
    (ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists a5 a6 a7 BC' ovf' m',
    ms' = MS (gl2R L T ovf' mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c2f8) fc None m' (seg_rom psegs)
    /\ munch (Wg2 L) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' (dl_As L + 2976) (u16s (av16 BC' 16))
    /\ R = bt_upd s t FC DL HP HL HM DP BC' OL SL mc
    /\ arr_len BC' = 16 /\ (forall i, 0 <= i < 16 -> 0 <= arr_get BC' i < 65536).

Lemma gl2_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T ovf mc ML : Z) (FC DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL : Z) (R : deflate_state) (m0 : mem)
    (ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m (dl_As L + 2976) (u16s (av16 BC 16)) -> mem_inv psegs m -> dlay_ok L -> munch (Wg2 L) m0 m -> wmono psegs m0 m -> arr_len BC = 16 ->
  (forall i, 0 <= i < 16 -> 0 <= arr_get BC i < 65536) ->
  7 <= ML <= 15 -> 1 <= ovf <= 573 -> ovf <= 2 * Z.of_nat f ->
  R = gen_bitlen_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ML ovf ->
  gb2_ok ML f (bt_upd s t FC DL HP HL HM DP BC OL SL mc) ovf ->
  evt psegs (gl2_loop_post L s t T mc ML FC DL HP HL HM DP OL SL R ra sp gp tp t0 t1 t2 s5 s6 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (gl2R L T ovf mc ML ra sp gp tp t0 t1 t2 a5 a6 a7 s5 s6 s10 s11 t3 t4 t5 t6) F (wz 0x1c2ac) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros BLC MI LAY MU WM LBC RBC RML Ro Hf ER OK.
  { exfalso. lia. }
  pose proof (av16_zlength BC 16 ltac:(lia)) as L16.
  rewrite (GL2_step t ML) in ER. destruct (gb2_ok_step t ML f s FC DL HP HL HM DP BC OL SL mc ovf OK) as [Hr OK'].
  set (r := gen_bitlen_find (Z.to_nat ML) (bt_upd s t FC DL HP HL HM DP BC OL SL mc) (ML - 1)) in *.
  destruct (find_char t s FC DL HP HL HM DP BC OL SL mc ML r eq_refl Hr ltac:(lia)) as (Hr1 & Z0 & NZ).
  call (gl2_iter L T ovf mc ML r BC).
  1:{ exact BLC. } 1:{ exact MI. } 1:{ exact LAY. } 1:{ exact LBC. } 1:{ exact RML. } 1:{ exact Ro. } 1:{ lia. } 1:{ exact Z0. } 1:{ exact NZ. } 1:{ apply RBC. lia. }
  pose proof (av16_zlength (bl_adj ML BC r) 16 ltac:(lia)) as L16'.
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - rewrite (proj2 (Z.ltb_lt 0 (ovf - 2)) K) in ER.
    eapply (IH L s t T (ovf - 2) mc ML FC DL HP HL HM DP (bl_adj ML BC r) OL SL R m0);
      [eassumption| eassumption| exact LAY| exact MU| exact WM| rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC| exact RML| lia| lia| exact ER| apply OK'; exact K].
  - rewrite (proj2 (Z.ltb_ge 0 (ovf - 2))) in ER by lia.
    apply evt_done. unfold gl2_loop_post. do 3 eexists. exists (bl_adj ML BC r), (ovf - 2). eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER|].
    split; [rewrite bl_adj_len; exact LBC| apply bl_adj_range; exact RBC].
Qed.
