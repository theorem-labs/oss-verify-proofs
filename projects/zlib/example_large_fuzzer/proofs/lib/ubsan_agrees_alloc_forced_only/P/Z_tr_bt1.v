(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import Tac Image ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.P Require Import Z_kit Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees TreeModel BuildTreeModel RefBuildTree1.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)
Ltac h32_store ARR a n A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u32arr_store_ok psegs _ A (av32 a n) idx (wa (A + 4 * idx)) ARR ltac:(rewrite av32_length; lia) eq_refl) as SOK;
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

(* [comment removed for export] *)
Definition bt1R (L : dlay) (T E n mc dsc stp : Z) (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) :=
  mkR ra sp gp tp (wz (T + 4 * E + 2)) t1 t2 s0 (wz (dl_As L)) a0 (wz dsc) (wz stp) (wz 4096) (wz n) (wz (dl_As L + 3008)) (wz (dl_As L + 5308 + n)) (wz (T + 4 * n + 2))
      (wz T) (wz mc) (wz (dl_As L + 5300)) (wz (dl_As L + 2047)) s6 s7 s8 s9 s10 s11 t3 t4 t5 t6.

Notation Wbt1 L T N := [(T%Z, (T + 4 * N)%Z); (dl_As L + 3008, dl_As L + 5881)] (only parsing).

Definition bt_loop1_post (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z)
    (ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t1 t2 DL' HP' HL' DP' mc' m',
    ms' = MS (bt1R L T (sd_elems t) (sd_elems t) mc' dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bd28) fc None m' (seg_rom psegs)
    /\ munch (Wbt1 L T N) m0 m' /\ wmono psegs m0 m' /\ mem_inv psegs m'
    /\ u8arr psegs m' T (u16s (avct FC DL' N)) /\ u32arr psegs m' (dl_As L + 3008) (av32 HP' 573) /\ u8arr psegs m' (dl_As L + 5308) (av8 DP' 573)
    /\ rw_cells psegs m' (dl_As L + 5300) [C4 (wz HL'); C4 (wz HM)]
    /\ R = (bt_upd s t FC DL' HP' HL' HM DP' BC OL SL MC, mc')
    /\ arr_len DL' = N /\ arr_len HP' = 573 /\ arr_len DP' = 573 /\ 0 <= HL' <= sd_elems t /\ -1 <= mc' < sd_elems t.

Lemma bt_loop1 : forall (f : nat) (L : dlay) (s : deflate_state) (t : tree_id) (T N dsc stp : Z) (FC BC : arr) (HM OL SL MC : Z) (R : deflate_state * Z) (m0 : mem)
    (DL HP : arr) (HL : Z) (DP : arr) (n mc : Z)
    (ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr psegs m T (u16s (avct FC DL N)) -> u32arr psegs m (dl_As L + 3008) (av32 HP 573) -> u8arr psegs m (dl_As L + 5308) (av8 DP 573) ->
  rw_cells psegs m (dl_As L + 5300) [C4 (wz HL); C4 (wz HM)] ->
  mem_inv psegs m -> dlay_ok L -> munch (Wbt1 L T N) m0 m -> wmono psegs m0 m ->
  dl_As L + 212 <= T -> T + 4 * N <= dl_As L + 2904 -> sd_elems t < N -> arr_len FC = N -> arr_len DL = N -> arr_len HP = 573 -> arr_len DP = 573 ->
  (forall i, 0 <= i < N -> 0 <= arr_get FC i < 65536) ->
  0 <= HL <= n -> 0 <= n -> Z.of_nat (S f) = sd_elems t - n -> -1 <= mc < sd_elems t ->
  R = L1 t (bt_upd s t FC DL HP HL HM DP BC OL SL MC) n mc ->
  evt psegs (bt_loop1_post L s t T N dsc stp FC BC HM OL SL MC R ra sp gp tp s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 F fc m0)
      (MS (bt1R L T (sd_elems t) n mc dsc stp ra sp gp tp t1 t2 s0 a0 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6) F (wz 0x1bcf0) fc None m (seg_rom psegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR HPA DPA GC MI LAY MU WM RT1 RT2 REN LFC LDL LHP LDP RFC RHL Rn Ef Rmc ER.
  all: pose proof (RefBuildTree1.elems_range t) as RE.
  all: lay_open LAY.
  all: rewrite RefBuildTree1.L1_step in ER by lia.
  all: pose proof (RFC n ltac:(lia)) as Rf.
  all: pose proof (u16arr_read psegs m T (avct FC DL N) (2 * n) _ (wa (T + 4 * n + 2 + -2)) ARR (avct_nth_fc FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDf.
  all: pose proof (avct_zlength FC DL N ltac:(lia)) as LCT; pose proof (av32_zlength HP 573 ltac:(lia)) as L32; pose proof (av8_zlength DP 573 ltac:(lia)) as L8.
  all: unfold bt1R; zs2; rewrite zx16_small by lia; zstep; br_cases_s K.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [|exfalso; lia].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite RefBuildTree1.L1_end in ER.
    apply evt_done. unfold bt_loop1_post, bt1R. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. zs2. shl_norm. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [exfalso; lia|].
    replace (n + 1) with (sd_elems t) in * by lia. rewrite RefBuildTree1.L1_end in ER.
    apply evt_done. unfold bt_loop1_post, bt1R. do 8 eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [exact ARR|]. split; [exact HPA|]. split; [exact DPA|]. split; [exact GC|].
    split; [exact ER|]. rewrite ?arr_len_set. repeat split; lia.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ _) K) in ER. cbn [negb] in ER.
    ct_store_dl ARR FC DL N T n (wrap16 0) ltac:(reflexivity).
    zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [exfalso; lia|].
    eapply (IH L s t T N dsc stp FC BC HM OL SL MC R m0 (arr_set DL n (wrap16 0)) HP HL DP (n + 1) mc);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact REN| exact LFC| rewrite arr_len_set; exact LDL
      | exact LHP| exact LDP| exact RFC| lia| lia| lia| exact Rmc| exact ER].
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_neq _ _) K) in ER. cbn [negb] in ER.
    zs2. zs2. zs2. shl_norm. zs2. zs2.
    h32_store HPA HP 573 (dl_As L + 3008) (HL + 1) n ltac:(reflexivity).
    pb_store DPA DP 573 (dl_As L + 5308) n (wrap8 0) ltac:(reflexivity).
    zs2. zs2. zs2. zs2. reg_as (T + 4 * n + 6) (T + 4 * (n + 1) + 2). reg_as (dl_As L + 5308 + n + 1) (dl_As L + 5308 + (n + 1)).
    zstep. br_cases_s K2; [|exfalso; lia].
    eapply (IH L s t T N dsc stp FC BC HM OL SL MC R m0 DL (arr_set HP (HL + 1) n) (HL + 1) (arr_set DP n (wrap8 0)) (n + 1) n);
      [exact ARR| exact HPA| exact DPA| exact GC| eassumption| exact LAY| exact MU| exact WM| exact RT1| exact RT2| exact REN| exact LFC| exact LDL
      | rewrite arr_len_set; exact LHP| rewrite arr_len_set; exact LDP| exact RFC| lia| lia| lia| lia| exact ER].
Qed.
