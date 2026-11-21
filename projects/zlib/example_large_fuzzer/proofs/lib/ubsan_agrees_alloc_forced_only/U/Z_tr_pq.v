(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1 RefBuildTree3.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Definition Z_PQDOWNHEAP : Z := 0x1e198.
Definition PQ_TRAP : Z := 0x1e3fc.
Definition PQ_HEAD : Z := 0x1e25c.
Definition PQ_CMP : Z := 0x1e328.
Definition PQ_CONT : Z := 0x1e39c.
Definition PQ_FIN : Z := 0x1e3d0.
Definition Z_PQ_STACK : Z := 64.
Local Notation ONES := 18446744073709551615.

Ltac h32_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok usegs _ A (av32 a n) idx (wa (A + 4 * idx)) ARR ltac:(rewrite av32_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le4 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (av32_write m0 A a n idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 4 * idx) with E in ARR' by lia;
      let LN := fresh "L32" in pose proof (av32_zlength (arr_set a idx v) n ltac:(lia)) as LN;
      let LA := fresh "LNH" in pose proof (arr_len_set a idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

Notation Wpq lo sp L := [(lo%Z, bv_unsigned sp); (dl_As L + 3008, dl_As L + 5300)] (only parsing).

Ltac decide_bools :=
  repeat match goal with
  | |- context [?a <? ?b] => first [rewrite (proj2 (Z.ltb_lt a b)) by lia | rewrite (proj2 (Z.ltb_ge a b)) by lia]
  | |- context [?a <=? ?b] => first [rewrite (proj2 (Z.leb_le a b)) by lia | rewrite (proj2 (Z.leb_gt a b)) by lia]
  | |- context [?a =? ?b] => first [rewrite (proj2 (Z.eqb_eq a b)) by lia | rewrite (proj2 (Z.eqb_neq a b)) by lia]
  end; cbn [andb orb negb].

(* [comment removed for export] *)
Lemma hz17 : forall T, 0 < T -> Z.b2z (0 <? T) = 1.
Proof. intros T H. rewrite (proj2 (Z.ltb_lt 0 T) H). reflexivity. Qed.
Lemma hz28 : forall T q, 0 < T -> q mod 2 = 0 -> Z.land (Z.b2z (0 <? T)) (Z.b2z (Z.land q 1 <? 1)) = 1.
Proof. intros T q H Hq. rewrite (proj2 (Z.ltb_lt 0 T) H). rewrite (land1_mod2 q Hq). reflexivity. Qed.
Lemma hz29 : forall T q i, 0 < T -> 0 < q -> T <= q -> 0 <= i < 2^63 ->
  Z.land (Z.lxor (Z.b2z (0 <? T)) (Z.b2z (q <? 1))) (Z.lxor (Z.lxor (Z.b2z (q <? T)) (Z.b2z (Z.lxor i 9223372036854775808 <? 9223372036854775808))) 1) = 1.
Proof. intros T q i HT Hq HTq Hi. rewrite xor_guard by lia. rewrite xor_guard_idx by lia. reflexivity. Qed.

(* [comment removed for export] *)
Definition upqR (L : dlay) (T v k j : Z) (x8 x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) :=
  mkR ra sp gp tp (wz (T + v * 4)) (wz (ONES - (dl_As L + 5308))) (wz (dl_As L + 5308 + v)) x8 x9
      (wz (dl_As L + 5308)) (wz T) (wz (dl_As L + 3008)) (wz (ONES - (dl_As L + 3008))) (wz v) (wz k) (wz (dl_As L + 5300)) (wz 1)
      x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 (wz 1) (wz 1) (wz 572) (wz j).

(* [comment removed for export] *)
Lemma upq_sel : forall (L : dlay) (T N k j q HL v : Z) (FC DL HP DP : arr)
    (x8 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= j <= HL -> HL < 573 ->
  evt usegs (fun ms' => exists x9' x18' x19' x20' x21' x22',
               ms' = MS (upqR L T v k j (wz (sel3 FC HL DP HP j)) x9' x18' x19' x20' x21' x22' ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_CMP) fc None m (seg_rom usegs))
      (MS (upqR L T v k j x8 (wz HL) x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_HEAD) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY AL4 RT1 RT2 RN PQ RFC RDP Ej Rj RHL. lay_open LAY. unfold upqR, PQ_HEAD, PQ_CMP.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  zs2. zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
  - pose proof (PQ j ltac:(lia)) as Rhj. pose proof (PQ (j + 1) ltac:(lia)) as Rhj1.
    pose proof (u32arr_read usegs m _ (av32 HP 573) j _ (wa (dl_As L + 3008 + j * 4)) HPA (av32_nth HP 573 j ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
    pose proof (u32arr_read usegs m _ (av32 HP 573) (j + 1) _ (wa (dl_As L + 3008 + (j + 1) * 4)) HPA (av32_nth HP 573 (j + 1) ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj1.
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP j) ltac:(lia)) as [RDfj _].
    destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP (j + 1)) ltac:(lia)) as [RDfj1 _].
    replace (T + 4 * arr_get HP j) with (T + arr_get HP j * 4) in RDfj by lia. replace (T + 4 * arr_get HP (j + 1)) with (T + arr_get HP (j + 1) * 4) in RDfj1 by lia.
    pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rhj1) as Rfj1.
    zs2. ustep PQ_TRAP. zs2. shl_norm. ustep PQ_TRAP. zs2. zs2.
        zs2. shl_norm. zs2. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
        zs2. shl_norm. zs2. zs2. zs2. shl_norm. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
        zs2. rewrite (zx16_small (arr_get FC (arr_get HP (j + 1)))) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP j))) by lia.
    zstep. br_cases K1.
    + (* [comment removed for export] *)
      zstep. br_cases_s K2.
      * (* [comment removed for export] *)
        zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
      * (* [comment removed for export] *)
        pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP j) _ (wa (dl_As L + 5308 + arr_get HP j)) DPA (av8_nth DP 573 (arr_get HP j) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
        pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP (j + 1)) _ (wa (dl_As L + 5308 + arr_get HP (j + 1))) DPA (av8_nth DP 573 (arr_get HP (j + 1)) ltac:(lia)) ltac:(lia) eq_refl) as RDdj1.
        pose proof (RDP (arr_get HP j) ltac:(lia)) as Rdj. pose proof (RDP (arr_get HP (j + 1)) ltac:(lia)) as Rdj1.
        do 4 ustep PQ_TRAP. zs2. zs2.
                zsb. rewrite (bv8_small (arr_get DP (arr_get HP (j + 1)))) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP j))) by lia.
        zs2. zstep. br_cases K3.
        -- zs2. zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
        -- zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
    + (* [comment removed for export] *)
      zs2. zs2. apply evt_done. unfold sel3, smal. decide_bools. do 6 eexists. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma upq_cmp : forall (L : dlay) (T N k jj j0 HL v : Z) (FC DL HP DP : arr)
    (x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  ct_readable [] m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= jj <= HL -> HL < 573 -> 0 <= v < N -> 1 <= k < 573 ->
  evt usegs (fun ms' => exists x9' x18' x19' x8v pcx,
               ms' = MS (upqR L T v k (arr_get HP jj) (wz x8v) x9' x18' x19' x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz pcx) fc None m (seg_rom usegs)
               /\ ((pcx = PQ_FIN /\ x8v = k * 4 /\ smal FC DP v (arr_get HP jj) = true) \/ (pcx = PQ_CONT /\ x8v = jj /\ smal FC DP v (arr_get HP jj) = false)))
      (MS (upqR L T v k j0 (wz jj) x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_CMP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA RDT MI LAY AL4 RT1 RT2 RN PQ RFC RDP Rj RHL Rv Rk. lay_open LAY. unfold upqR, PQ_CMP.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ jj Rj) as Rhj.
  pose proof (u32arr_read usegs m _ (av32 HP 573) jj _ (wa (dl_As L + 3008 + jj * 4)) HPA (av32_nth HP 573 jj ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDj.
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI (arr_get HP jj) ltac:(lia)) as [RDfj _].
  destruct (RDT m (munch_refl _ _) (wmono_refl _ _) MI v ltac:(lia)) as [RDfv _].
  replace (T + 4 * arr_get HP jj) with (T + arr_get HP jj * 4) in RDfj by lia. replace (T + 4 * v) with (T + v * 4) in RDfv by lia.
  pose proof (RFC _ Rhj) as Rfj. pose proof (RFC _ Rv) as Rfv.
  do 3 ustep PQ_TRAP. zs2. shl_norm. ustep PQ_TRAP. zs2. zs2.
  zs2. shl_norm. zs2. ustep PQ_TRAP. zs2. zs2. zs2. zs2. ustep PQ_TRAP. zs2. ustep PQ_TRAP.
  zs2. rewrite (zx16_small (arr_get FC v)) by lia. zs2. rewrite (zx16_small (arr_get FC (arr_get HP jj))) by lia.
  zstep. br_cases K1.
  - (* [comment removed for export] *)
    zs2. zs2. shl_norm. ustep PQ_TRAP.
    apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
  - zstep. br_cases_s K2.
    + (* [comment removed for export] *)
      apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
    + pose proof (u8arr_read usegs m _ (av8 DP 573) (arr_get HP jj) _ (wa (dl_As L + 5308 + arr_get HP jj)) DPA (av8_nth DP 573 (arr_get HP jj) ltac:(lia)) ltac:(lia) eq_refl) as RDdj.
      pose proof (u8arr_read usegs m _ (av8 DP 573) v _ (wa (dl_As L + 5308 + v)) DPA (av8_nth DP 573 v ltac:(lia)) ltac:(lia) eq_refl) as RDdv.
      pose proof (RDP (arr_get HP jj) ltac:(lia)) as Rdj. pose proof (RDP v ltac:(lia)) as Rdv.
      do 4 ustep PQ_TRAP. zs2.
      zsb. rewrite (bv8_small (arr_get DP v)) by lia. zsb. rewrite (bv8_small (arr_get DP (arr_get HP jj))) by lia.
      zstep. br_cases K3.
      * (* [comment removed for export] *)
        zs2. shl_norm. zstep. br_true.
        apply evt_done. do 5 eexists. split; [reflexivity|]. left. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
      * apply evt_done. do 5 eexists. split; [reflexivity|]. right. split; [reflexivity|]. split; [reflexivity|]. unfold smal. decide_bools. reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
Definition fuel_ok (f : nat) (j HL : Z) : Prop := HL < j * 2 ^ Z.of_nat f.
Lemma fuel_ok_0 : forall j HL, fuel_ok 0 j HL -> HL < j.
Proof. unfold fuel_ok. intros j HL H. change (2 ^ Z.of_nat 0) with 1 in H. lia. Qed.
Lemma fuel_ok_S : forall f j j' HL, fuel_ok (S f) j HL -> 2 * j <= j' -> 0 < j -> fuel_ok f j' HL.
Proof.
  unfold fuel_ok. intros f j j' HL H Hj Hp. rewrite Nat2Z.inj_succ, Z.pow_succ_r in H by lia.
  assert (0 < 2 ^ Z.of_nat f) by (apply Z.pow_pos_nonneg; lia). nia.
Qed.
Lemma pq_out : forall f X t v k j, ds_heap_len X < j -> pqdownheap_loop f X t v k j = (X, k).
Proof. intros [|f] X t v k j H; [reflexivity|]. cbn [pqdownheap_loop]. rewrite (proj2 (Z.leb_gt _ _) H). reflexivity. Qed.
Lemma pqdownheap_flat : forall s t FC DL HP HL HM DP BC OL SL MC k,
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k
  = heap_set (fst (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)))
             (snd (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2))) (arr_get HP k).
Proof.
  intros. unfold pqdownheap. rewrite bt_heap_get. rewrite Z.shiftl_mul_pow2 by lia. change (2 ^ 1) with 2.
  destruct (pqdownheap_loop 32 _ t (arr_get HP k) k (k * 2)); reflexivity.
Qed.

Notation Wh L := [(dl_As L + 3008, dl_As L + 5300)] (only parsing).

Definition upq_loop_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists x9 x18 x19 x20 x21 x22 jv HP' k' m',
    ms' = MS (upqR L T v k' jv (wz (k' * 4)) x9 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_FIN) fc None m' (seg_rom usegs)
    /\ munch (Wh L) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL HP' HL HM DP BC OL SL MC, k')
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) /\ 1 <= k' <= HL.

Lemma upq_loop : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM v : Z) (FC DL DP BC : arr) (OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (HP : arr) (k j q : Z)
    (x8 x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wh L) m0 T FC DL N -> mem_inv usegs m -> dlay_ok L -> munch (Wh L) m0 m -> wmono usegs m0 m ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  j = 2 * q -> 1 <= k -> k < j -> j <= HL -> HL < 573 -> 0 <= v < N -> fuel_ok f j HL ->
  R = pqdownheap_loop f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t v k j ->
  evt usegs (upq_loop_post L s t T N HL HM v FC DL DP BC OL SL MC R ra sp gp tp s7 s8 s9 s10 s11 F fc m0)
      (MS (upqR L T v k j x8 (wz HL) x18 x19 x20 x21 x22 ra sp gp tp s7 s8 s9 s10 s11) F (wz PQ_HEAD) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros HPA DPA GC RDT MI LAY MU WM AL4 RT1 RT2 RN LHP PQ RFC RDP Ej Rk Rkj Rj RHL Rv FU ER.
  - apply fuel_ok_0 in FU. lia.
  - assert (RDTm : ct_readable [] m T FC DL N) by (eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; tauto]).
    pose proof (RefBuildTree3.sel3_range FC HL DP HP j ltac:(lia)) as Rs3.
    rewrite RefBuildTree3.loop3_S_sel in ER by lia.
    eapply evt_cut; [eapply (upq_sel L T N k j q HL v FC DL HP DP); try eassumption; lia|]. intros ms' (x9' & x18' & x19' & x20' & x21' & x22' & ->).
    eapply evt_cut; [eapply (upq_cmp L T N k (sel3 FC HL DP HP j) j HL v FC DL HP DP); try eassumption; lia|].
    intros ms' (x9'' & x18'' & x19'' & x8v & pcx & -> & [(-> & -> & SM)|(-> & -> & SM)]); rewrite SM in ER.
    + (* [comment removed for export] *)
      apply evt_done. unfold upq_loop_post. do 10 eexists.
      split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
      split; [exact ER|]. split; [exact LHP|]. split; [exact PQ| lia].
    + (* [comment removed for export] *)
      set (j' := sel3 FC HL DP HP j) in *.
      pose proof (PQ j' ltac:(lia)) as Rhj. lay_open LAY.
      pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
      unfold upqR, PQ_CONT. zs2. shl_norm. ustep PQ_TRAP. zs2.
      h32_store HPA HP 573 (dl_As L + 3008) k (arr_get HP j') ltac:(reflexivity).
      zs2. zs2. shl_norm. strip32. zs2. shl_norm. zs2. reg_as (j' + 0) j'.
      zstep. br_cases K.
      * (* [comment removed for export] *)
        eapply (IH L s t T N HL HM v FC DL DP BC OL SL MC R m0 (arr_set HP k (arr_get HP j')) j' (j' * 2) j');
          [exact HPA| exact DPA| exact GC| exact RDT| eassumption| assumption| exact MU| exact WM| exact AL4| exact RT1| exact RT2| exact RN| rewrite arr_len_set; exact LHP
          | | exact RFC| exact RDP| lia| lia| lia| lia| exact RHL| exact Rv| eapply fuel_ok_S; [exact FU| lia| lia]| exact ER].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
      * (* [comment removed for export] *)
        rewrite pq_out in ER by (rewrite bt_heap_len; lia).
        zs2. zs2. shl_norm. ustep PQ_TRAP.
        apply evt_done. unfold upq_loop_post, upqR. do 10 eexists.
        split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
        split; [exact ER|]. split; [rewrite arr_len_set; exact LHP|]. split; [|lia].
        intros i Hi. destruct (Z.eq_dec k i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rhj| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
Definition pqdownheap_post (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 HP' m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (ret_pc ra) fc None m' (seg_rom usegs)
    /\ munch (Wpq lo sp L) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ stk usegs m' lo (bv_unsigned sp)
    /\ u32arr usegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr usegs m' (dl_As L + 5308) (av8 DP 573)
    /\ rw_cells usegs m' (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)]
    /\ pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k = bt_upd s t FC DL HP' HL HM DP BC OL SL MC
    /\ arr_len HP' = 573 /\ (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N).

(* [comment removed for export] *)
Lemma upq_fin : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k k' v lo : Z) (FC DL HP HP' DP BC : arr) (OL SL MC : Z) (junk : list byte) (m0 : mem)
    (ra sp gp tp t0 t1 t2 s0 s1 x9 a0 a1 a3 a5 a6 a7 s2 s3 s4 s5 s6 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP' 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] -> mem_inv usegs m -> dlay_ok L ->
  munch (Wpq lo sp L) m0 m -> wmono usegs m0 m ->
  stk usegs m lo (bv_unsigned sp + -64) -> rw_cells usegs m (bv_unsigned sp + -64) [CB 8 junk; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0] ->
  lo <= bv_unsigned sp - 64 -> dlay_below L lo (bv_unsigned sp) ->
  arr_len HP' = 573 -> (forall i, 1 <= i <= HL -> 0 <= arr_get HP' i < N) -> 1 <= k' <= HL -> HL < 573 -> 0 <= v < N ->
  pqdownheap (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t k = bt_upd s t FC DL (arr_set HP' k' v) HL HM DP BC OL SL MC ->
  evt usegs (pqdownheap_post L s t T N HL HM k lo FC DL HP DP BC OL SL MC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m0)
      (MS (mkR ra (wz (bv_unsigned sp + -64)) gp tp t0 t1 t2 (wz (k' * 4)) x9 a0 a1 (wz (dl_As L + 3008)) a3 (wz v) a5 a6 a7 x18 x19 x20 x21 x22 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (wz PQ_FIN) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC MI LAY MU WM STK FR LO BEL LHP PQ Rk RHL Rv EQ. unfold PQ_FIN.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0.
  pose proof (av32_zlength HP' 573 ltac:(lia)) as L32.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + -64)) = bv_unsigned sp + -64) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  zs2.
  h32_store HPA HP' 573 (dl_As L + 3008) k' v ltac:(reflexivity).
  do 7 zstep. zstep. zstep.
  release_frame FR STK (bv_unsigned sp).
  apply evt_done. unfold pqdownheap_post. do 17 eexists.
  split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact STK|].
  split; [exact HPA|]. split; [eassumption|]. split; [eassumption|]. split; [exact EQ|].
  split; [rewrite arr_len_set; exact LHP|].
  intros i Hi. destruct (Z.eq_dec k' i) as [<-|NE]; [rewrite arr_get_set_same by lia; exact Rv| rewrite arr_get_set_other by exact NE; apply PQ; exact Hi].
Qed.

Lemma pqdownheap_spec : forall (L : dlay) (s : deflate_state) (t : tree_id) (T N HL HM k lo : Z) (FC DL HP DP BC : arr) (OL SL MC : Z)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u32arr usegs m (dl_As L + 3008) (av32 HP 573) -> u8arr usegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells usegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  ct_readable (Wpq lo sp L) m T FC DL N -> mem_inv usegs m -> dlay_ok L ->
  stk usegs m lo (bv_unsigned sp) -> lo <= bv_unsigned sp - Z_PQ_STACK -> dlay_below L lo (bv_unsigned sp) ->
  T mod 4 = 0 -> dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> N <= 573 -> arr_len HP = 573 ->
  (forall i, 1 <= i <= HL -> 0 <= arr_get HP i < N) -> (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) -> (forall i, 0 <= i < 573 -> 0 <= arr_get DP i < 256) ->
  1 <= k <= HL -> HL < 573 ->
  a0 = wz (dl_As L) -> a1 = wz T -> a2 = wz k ->
  evt usegs (pqdownheap_post L s t T N HL HM k lo FC DL HP DP BC OL SL MC ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m)
      (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz Z_PQDOWNHEAP) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros HPA DPA GC RDT MI LAY STK LO BEL AL4 RT1 RT2 RN LHP PQ RFC RDP Rk RHL -> -> ->. unfold Z_PQDOWNHEAP, Z_PQ_STACK in *.
  pose proof (munch_refl (Wpq lo sp L) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof LAY as LAY0. lay_open LAY0. pose proof BEL as BEL0. below_open BEL0. pose proof (lo_s _ LAY) as BK. unfold blk_ok in BK.
  pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  pose proof (PQ k ltac:(lia)) as Rv.
  carve_frame 64%nat STK.
  do 8 zstep.
  do 2 ustep PQ_TRAP. zs2. zs2. rewrite (Z.mod_small k 4294967296) by lia.
  do 2 ustep PQ_TRAP. zs2. zs2. reg_as (dl_As L + 2047 + 961) (dl_As L + 3008). zs2. shl_norm. ustep PQ_TRAP. ustep PQ_TRAP.
  zs2. zs2. zs2. zs2.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    pose proof (u32arr_read usegs mm _ (av32 HP 573) k _ (wa (dl_As L + 3008 + k * 4)) HPA (av32_nth HP 573 k ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDk end.
  zs2. zs2. zs2. shl_norm. strip32.
  zstep. br_cases K.
  - (* [comment removed for export] *)
    zs2. zs2. zs2. zs2. shl_norm. zs2. shl_norm. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2. zs2.
    rewrite (zb_lxor_ones (dl_As L + 5308)) by lia.
    rewrite hz29 by lia. rewrite hz28 by first [lia | Z.div_mod_to_equations; lia]. rewrite xor_guard by lia. rewrite hz17 by lia.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (upq_loop 32 L s t T N HL HM (arr_get HP k) FC DL DP BC OL SL MC
              (pqdownheap_loop 32 (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t (arr_get HP k) k (k * 2)) mm HP k (k * 2) k) end.
    1:{ exact HPA. } 1:{ exact DPA. } 1:{ exact GC. }
    1:{ eapply ct_readable_rebase; [exact RDT| exact MU| exact WM| intros xx Hxx; cbn [outside] in *; intuition lia]. }
    1:{ eassumption. } 1:{ exact LAY. } 1:{ apply munch_refl. } 1:{ apply wmono_refl. } 1:{ exact AL4. } 1:{ exact RT1. } 1:{ exact RT2. } 1:{ exact RN. } 1:{ exact LHP. }
    1:{ exact PQ. } 1:{ exact RFC. } 1:{ exact RDP. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ lia. } 1:{ exact RHL. } 1:{ exact Rv. }
    1:{ unfold fuel_ok. change (2 ^ Z.of_nat 32) with 4294967296. lia. } 1:{ reflexivity. }
    match goal with E : pqdownheap_loop _ _ _ _ _ _ = (bt_upd _ _ _ _ ?hp _ _ _ _ _ _ _, ?kk), H : u32arr usegs ?mm _ (av32 ?hp 573), HD : u8arr usegs ?mm _ (av8 DP 573),
                     HG : rw_cells usegs ?mm (dl_As L + 5300) _, HL' : arr_len ?hp = 573, HQ : forall i, 1 <= i <= HL -> 0 <= arr_get ?hp i < N |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      unfold upqR;
      eapply (upq_fin L s t T N HL HM k kk (arr_get HP k) lo FC DL HP hp DP BC OL SL MC);
        [exact H| exact HD| exact HG| eassumption| exact LAY| exact MU| exact WM| exact STK| exact FR| lia| exact BEL| exact HL'| exact HQ| lia| exact RHL| exact Rv|
         rewrite pqdownheap_flat, E; cbn [fst snd]; rewrite bt_heap_set; reflexivity] end.
  - (* [comment removed for export] *)
    zs2. shl_norm. zstep. br_true.
    eapply (upq_fin L s t T N HL HM k k (arr_get HP k) lo FC DL HP HP DP BC OL SL MC);
      [exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact STK| exact FR| lia| exact BEL| exact LHP| exact PQ| lia| exact RHL| exact Rv|].
    rewrite pqdownheap_flat, pq_out by (rewrite bt_heap_len; lia). cbn [fst snd]. rewrite bt_heap_set. reflexivity.
Qed.
