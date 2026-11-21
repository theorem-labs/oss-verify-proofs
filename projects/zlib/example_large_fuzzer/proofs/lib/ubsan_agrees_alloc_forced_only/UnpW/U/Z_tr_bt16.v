(* reloc-zl14c *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.Lib Require Import Tac Image. From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Lib Require Import ZBridge Arr.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.P Require Import Z_kit Z_tr_bt13 Z_tr_bt14 Z_tr_bt16.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.UnpW.U Require Import Z_dview Z_drep Z_dkit Z_trees_iface Z_tr_bt_iface Z_tr_kit Z_tr_rod Z_tr_emit Z_ukit Z_tr_bt_mid.
From OSSVerify.Proofs.zlib.example_large_fuzzer.lib.ubsan_agrees_alloc_forced_only.Z Require Import ZIface DeflateState Trees SendModel TreeModel BuildTreeModel GenBitlenModel GenCodesModel.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Notation wz := (Z_to_bv 64).

(* [comment removed for export] *)

Definition GC_HEAD : Z := 0x1d6dc.
Local Notation ONES := 18446744073709551615.

(* [comment removed for export] *)
Lemma uncl_write : forall m A w0 nc i (w : word) v,
  u8arr usegs m A (u16s (ncl w0 nc)) -> 1 <= i < 16 -> arr_len nc = 16 -> le2 w = le2 (wz v) ->
  u8arr usegs (write_to_mem m (wa (A + 2 * i)) (le2 w)) A (u16s (ncl w0 (arr_set nc i v))).
Proof.
  intros m A w0 nc i w v ARR Hi Hn E.
  assert (EQ : u16s (ncl w0 (arr_set nc i v)) = u16s (upd (ncl w0 nc) (Z.to_nat i) w)).
  { unfold ncl. rewrite <- av16_upd by lia. rewrite (upd_comm (av16 nc 16) (Z.to_nat i) 0%nat) by lia. apply u16s_upd_le2. symmetry. exact E. }
  rewrite EQ. apply (u16arr_write usegs); [exact ARR|]. rewrite ncl_length. lia.
Qed.

Ltac unc_store ARR w0 nc A idx v EQ :=
  let SOK := fresh "SOK" in
  pose proof (u16arr_store_ok usegs _ A (ncl w0 nc) idx (wa (A + 2 * idx)) ARR ltac:(rewrite ncl_length; lia) eq_refl) as SOK;
  zstep;
  lazymatch goal with
  | |- evt _ _ (MS _ _ _ _ _ (write_to_mem ?m0 ?a0 (le2 ?w)) _) =>
      let E := addr_expr a0 in
      let ARR' := fresh "ARRn" in
      pose proof (uncl_write m0 A w0 nc idx w v ARR ltac:(lia) ltac:(lia) ltac:(EQ)) as ARR';
      replace (A + 2 * idx) with E in ARR' by lia;
      let LN := fresh "LNC" in pose proof (ncl_zlength w0 (arr_set nc idx v)) as LN;
      let LA := fresh "LNB" in pose proof (arr_len_set nc idx v) as LA;
      clear ARR; store_done; rename ARR' into ARR
  end.

(* [comment removed for export] *)
Definition ugcR (T n mc : Z) (sp : word) (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) :=
  mkR ra sp gp tp t0 t1 t2 s0 s1 (wz n) (wz (bv_unsigned sp + 72)) (wz 16) (wz (ONES - (bv_unsigned sp + 72))) (wz 2147483647) (wz 1) a6 a7
      s2 s3 s4 s5 (wz T) s7 s8 s9 s10 s11 t3 (wz mc) t5 t6.

(* [comment removed for export] *)
Definition ugc_brl_post (T n mc v : Z) (sp a6 : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 a7 m',
    ms' = MS (ugcR T n mc sp ra gp tp t0 t1 (wz v) s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d730) fc None m' (seg_rom usegs)
    /\ munch [] m m' /\ wmono usegs m m' /\ mem_inv usegs m'.

Lemma ugc_brl : forall (d : nat) (T n mc c r l : Z) (sp a6 t2 : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  mem_inv usegs m -> Z.of_nat d = l - 1 -> 1 <= l <= 15 -> 0 <= c < 65536 -> res_ok r l ->
  evt usegs (ugc_brl_post T n mc (brl c r l) sp a6 ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 F fc m)
      (MS (ugcR T n mc sp ra gp tp (wz c) (wz (l + 1)) t2 s0 s1 a6 (wz r) s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d718) fc None m (seg_rom usegs)).
Proof.
  induction d as [|d IH]; intros until m; intros MI Ed Rl Rc RO.
  - assert (l = 1) by lia. subst l.
    pose proof (res_ok_lor c r 1 ltac:(lia) RO) as RB. pose proof (res_ok_bound r 1 ltac:(lia) RO) as Rr.
    unfold ugcR. zs2. zs2. zs2. zs2. shl_norm. zs2. rewrite srliw1 by lia. zstep. br_cases K; [exfalso; lia|].
    rewrite land1_mod, (Z.lor_comm r). rewrite <- (brl_last c r) by lia.
    apply evt_done. unfold ugc_brl_post, ugcR. do 4 eexists. split; [reflexivity|]. split; [apply munch_refl|]. split; [apply wmono_refl| exact MI].
  - pose proof (res_ok_lor c r l ltac:(lia) RO) as RB. pose proof (res_ok_bound r l ltac:(lia) RO) as Rr. pose proof (res_ok_step c r l ltac:(lia) RO) as RO'.
    pose proof (brl_step c r l ltac:(lia) ltac:(lia) ltac:(lia) ltac:(lia)) as ES. change (2 ^ 1) with 2 in ES, RO'.
    unfold ugcR. zs2. zs2. zs2. zs2. shl_norm. zs2. rewrite srliw1 by lia. zstep. br_cases K; [|exfalso; lia].
    rewrite land1_mod. change (2 ^ 1) with 2. rewrite (Z.lor_comm r). reg_as l (l - 1 + 1). rewrite ES.
    eapply evt_mono; [eapply (IH T n mc (c / 2) (Z.lor (c mod 2) r * 2) (l - 1)); [exact MI| lia| lia| Z.div_mod_to_equations; lia| exact RO']|].
    intros ms' H. exact H.
Qed.

Notation uWgc T N sp := [(T%Z, (T + 4 * N)%Z); (bv_unsigned sp + 72, bv_unsigned sp + 104)] (only parsing).

(* [comment removed for export] *)
Definition ugc_iter_post (T N n mc : Z) (w0 : word) (FC' DL nc' : arr) (sp : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 pcx m',
    ms' = MS (ugcR T (n + 1) mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz pcx) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m m' /\ wmono usegs m m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 nc'))
    /\ ((pcx = 0x1d6dc /\ n + 1 <= mc) \/ (pcx = 0x1d744 /\ n = mc)).

Ltac ugc_latch MU WM ARR NCA :=
  let K3 := fresh "K3" in
  ustep BT_TRAP; zs2; zs2; zstep; br_cases K3;
  apply evt_done; unfold ugc_iter_post, ugcR; do 8 eexists; (split; [reflexivity|]); (split; [exact MU|]); (split; [exact WM|]); (split; [eassumption|]);
  (split; [exact ARR|]); (split; [exact NCA|]); first [left; split; [reflexivity| lia] | right; split; [reflexivity| lia]].

Lemma ugc_iter : forall (T N n mc : Z) (w0 : word) (FC DL nc : arr) (sp : word)
    (ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (bv_unsigned sp + 72) (u16s (ncl w0 nc)) ->
  rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] -> mem_inv usegs m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  0 <= n <= mc -> mc < N -> 0 <= arr_get DL n <= 15 -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  evt usegs (ugc_iter_post T N n mc w0
               (if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) DL
               (if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1)))
               sp ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m)
      (MS (ugcR T n mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d6dc) fc None m (seg_rom usegs)).
Proof.
  intros until m. intros ARR NCA CT MI RT0 SEP RSP RN LFC LDL LNC Rn Rmc Rl RNC.
  pose proof (munch_refl (uWgc T N sp) m) as MU. pose proof (wmono_refl usegs m) as WM.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  assert (ESP : bv_unsigned (wz (bv_unsigned sp + 72)) = bv_unsigned sp + 72) by (apply unsigned_lit; pose proof (bv_unsigned_in_range 64 sp); unfold bv_modulus in *; lia).
  pose proof (u16arr_read usegs m T (avct FC DL N) (2 * n + 1) _ (wa (T + n * 4 + 2)) ARR (avct_nth_dl FC DL N n ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDl.
  unfold ugcR. zs2. shl_norm. zs2. ustep BT_TRAP. zs2. zs2. rewrite zx16_small by lia. zstep. br_cases K.
  - (* [comment removed for export] *)
    rewrite (proj2 (Z.eqb_eq _ 0) K).
    ugc_latch MU WM ARR NCA.
  - rewrite (proj2 (Z.eqb_neq _ 0) K).
    set (len := arr_get DL n) in *.
    pose proof (RNC len ltac:(lia)) as Rc.
    pose proof (u16arr_read usegs m _ (ncl w0 nc) len _ (wa (bv_unsigned sp + 72 + len * 2)) NCA (ncl_nth w0 nc len ltac:(lia)) ltac:(lia) ltac:(f_equal; lia)) as RDc.
    ustep BT_TRAP. zs2. shl_norm. ustep BT_TRAP. zs2. zs2. zs2. rewrite zx16_small by lia. zs2.
    unc_store NCA w0 nc (bv_unsigned sp + 72) len (wrap16 (arr_get nc len + 1)) ltac:(apply le2_wrap16; reflexivity).
    zs2.
    match goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      call (ugc_brl (Z.to_nat (len - 1)) T n mc (arr_get nc len) 0 len sp) end.
    1:{ eassumption. } 1:{ lia. } 1:{ lia. } 1:{ exact Rc. } 1:{ apply res_ok_0. lia. }
    rewrite <- bi_reverse_brl by lia.
    unfold ugcR.
    ct_store_fc ARR FC DL N T n (wrap16 (bi_reverse (arr_get nc len) len)) ltac:(apply le2_wrap16; reflexivity).

    ugc_latch MU WM ARR NCA.
Qed.

(* [comment removed for export] *)
Definition ugc_loop_post (s : deflate_state) (t : tree_id) (T N mc : Z) (w0 : word) (DL HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (sp : word)
    (ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m0 : mem) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a6 a7 t3 FC' nc' m',
    ms' = MS (ugcR T (mc + 1) mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d744) fc None m' (seg_rom usegs)
    /\ munch (uWgc T N sp) m0 m' /\ wmono usegs m0 m' /\ mem_inv usegs m'
    /\ u8arr usegs m' T (u16s (avct FC' DL N)) /\ u8arr usegs m' (bv_unsigned sp + 72) (u16s (ncl w0 nc'))
    /\ R = bt_upd s t FC' DL HP HL HM DP BC OL SL MC /\ arr_len FC' = N.

Lemma ugc_loop : forall (f : nat) (s : deflate_state) (t : tree_id) (T N n mc : Z) (w0 : word) (FC DL nc HP : arr) (HL HM : Z) (DP BC : arr) (OL SL MC : Z) (R : deflate_state) (m0 : mem)
    (sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32) (m : mem),
  u8arr usegs m T (u16s (avct FC DL N)) -> u8arr usegs m (bv_unsigned sp + 72) (u16s (ncl w0 nc)) ->
  rw_cells usegs m (bv_unsigned sp + 48) [C8 (wz (ONES - T))] -> mem_inv usegs m ->
  munch (uWgc T N sp) m0 m -> wmono usegs m0 m ->
  0 < T -> T + 4 * N <= bv_unsigned sp -> bv_unsigned sp + 208 < 2^63 ->
  0 <= N <= 573 -> arr_len FC = N -> arr_len DL = N -> arr_len nc = 16 ->
  Z.of_nat f = mc + 1 - n -> 0 <= n <= mc -> mc < N -> (forall i, 0 <= i <= mc -> 0 <= arr_get DL i <= 15) -> (forall k, 1 <= k <= 15 -> 0 <= arr_get nc k < 65536) ->
  R = gen_codes_loop2 f (bt_upd s t FC DL HP HL HM DP BC OL SL MC) t nc mc n ->
  evt usegs (ugc_loop_post s t T N mc w0 DL HP HL HM DP BC OL SL MC R sp ra gp tp s0 s1 s2 s3 s4 s5 s7 s8 s9 s10 s11 t5 t6 F fc m0)
      (MS (ugcR T n mc sp ra gp tp t0 t1 t2 s0 s1 a6 a7 s2 s3 s4 s5 s7 s8 s9 s10 s11 t3 t5 t6) F (wz 0x1d6dc) fc None m (seg_rom usegs)).
Proof.
  induction f as [|f IH]; intros until m; intros ARR NCA CT MI MU WM RT0 SEP RSP RN LFC LDL LNC Ef Rn Rmc RDL RNC ER.
  { exfalso. lia. }
  pose proof (gc2_model' s t FC DL HP HL HM DP BC OL SL MC f nc mc n R ER ltac:(lia)) as ER'. clear ER.
  pose proof (avct_zlength FC DL N ltac:(lia)) as LCT. pose proof (ncl_zlength w0 nc) as LNCZ.
  set (FC' := if arr_get DL n =? 0 then FC else arr_set FC n (wrap16 (bi_reverse (arr_get nc (arr_get DL n)) (arr_get DL n)))) in *.
  set (nc' := if arr_get DL n =? 0 then nc else arr_set nc (arr_get DL n) (wrap16 (arr_get nc (arr_get DL n) + 1))) in *.
  assert (LFC' : arr_len FC' = N) by (subst FC'; destruct (arr_get DL n =? 0); [exact LFC| rewrite arr_len_set; exact LFC]).
  assert (LNC' : arr_len nc' = 16) by (subst nc'; destruct (arr_get DL n =? 0); [exact LNC| rewrite arr_len_set; exact LNC]).
  assert (RNC' : forall k, 1 <= k <= 15 -> 0 <= arr_get nc' k < 65536).
  { intros k Hk. subst nc'. destruct (arr_get DL n =? 0); [apply RNC; exact Hk|].
    destruct (Z.eq_dec (arr_get DL n) k) as [<-|NE]; [rewrite arr_get_set_same by (pose proof (RDL n ltac:(lia)); lia); apply SendModel.wrap16_range'| rewrite arr_get_set_other by exact NE; apply RNC; exact Hk]. }
  pose proof (avct_zlength FC' DL N ltac:(lia)) as LCT'. pose proof (ncl_zlength w0 nc') as LNCZ'.
  call (ugc_iter T N n mc w0 FC DL nc sp).
  1:{ exact ARR. } 1:{ exact NCA. } 1:{ exact CT. } 1:{ exact MI. } 1:{ exact RT0. } 1:{ exact SEP. } 1:{ exact RSP. } 1:{ exact RN. } 1:{ exact LFC. } 1:{ exact LDL. } 1:{ exact LNC. }
  1:{ exact Rn. } 1:{ exact Rmc. } 1:{ apply RDL. lia. } 1:{ exact RNC. }
  match goal with H : _ \/ _ |- _ => destruct H as [[-> K]|[-> K]] end.
  - match goal with HC : rw_cells usegs ?mm (bv_unsigned sp + 48) _ |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
      eapply (IH s t T N (n + 1) mc w0 FC' DL nc' HP HL HM DP BC OL SL MC R m0);
        [eassumption| eassumption| exact HC| eassumption| exact MU| exact WM| exact RT0| exact SEP| exact RSP| exact RN| exact LFC'| exact LDL| exact LNC'| lia| lia| exact Rmc| exact RDL| exact RNC'| exact ER'] end.
  - rewrite gc2_out in ER' by lia. subst n.
    apply evt_done. unfold ugc_loop_post. do 6 eexists. exists FC', nc'. eexists.
    split; [reflexivity|]. split; [exact MU|]. split; [exact WM|]. split; [eassumption|]. split; [eassumption|]. split; [eassumption|]. split; [exact ER'| exact LFC'].
Qed.
