(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Lib Require Import Tac ImageA Arr Walk.
From OssFuzzTheorems.Proofs.openssl.pem.lib.Malloc Require Import MallocKit_AB.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Shadow.
From OssFuzzTheorems.Proofs.openssl.pem.lib.A Require Import Layout R_small R_m2s R_cache_defs R_glue_defs R_sec_defs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
(* [comment removed for export] *)
Local Definition zidle (P : Prop) : Prop := P.
Local Ltac zidle1 H := let T := type of H in change (zidle T) in H.
Local Ltac zidle_nsp H A sp := lazymatch A with context [bv_unsigned sp] => fail | _ => zidle1 H end.
Local Ltac zidle_begin sp n MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?m _) =>
    pose proof (munch_refl [(bv_unsigned sp - n, bv_unsigned sp)]%Z m) as MUz; pose proof (wmono_refl segs m) as WMz;
    repeat match goal with
    | H : rw_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : ro_cells segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u32arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u64arr segs m ?A _ |- _ => zidle_nsp H A sp
    | H : bytes_at segs m ?A _ |- _ => zidle_nsp H A sp
    | H : u8ro segs m ?A _ |- _ => zidle_nsp H A sp
    end
  end.
Local Ltac zidle_end MUz WMz :=
  lazymatch goal with |- evt ?segs _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch type of MUz with munch _ ?m _ =>
      try unfold zidle in *; transport_after_call segs m mm MUz WMz; clear MUz WMz end end.
(* [comment removed for export] *)
Local Ltac zidle_end_m m :=
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mm _) =>
    lazymatch goal with MU : munch _ m mm, WM : wmono _ m mm |- _ =>
      unfold zidle in *; transport_after_call asegs m mm MU WM end end.
Import ListNotations.
(* [comment removed for export] *)
Local Ltac Z.euclidean_division_equations_cleanup ::= idtac.
Open Scope bv_scope.
Notation mem := (word -> option byte).

Definition gbb_entry : Z := 0x19d308.

(* [comment removed for export] *)
Definition gbb_step (p acc ch : Z) : Z := if ((ch <=? p) && (acc <? ch))%Z then ch else acc.
Fixpoint gbb_fold (p acc : Z) (l : list Z) : Z :=
  match l with [] => acc | ch :: l' => gbb_fold p (gbb_step p acc ch) l' end.

Lemma gbb_fold_app : forall p l1 l2 acc, gbb_fold p acc (l1 ++ l2) = gbb_fold p (gbb_fold p acc l1) l2.
Proof. intros p l1. induction l1 as [|x l1 IH]; intros l2 acc; cbn; [reflexivity| apply IH]. Qed.

Lemma gbb_fold_range : forall p l acc, (0 <= acc <= p)%Z -> Forall (fun ch => 0 <= ch)%Z l -> (0 <= gbb_fold p acc l <= p)%Z.
Proof.
  intros p l. induction l as [|ch l IH]; intros acc Ha Hl; cbn [gbb_fold]; [exact Ha|].
  inversion Hl as [|? ? Hc Hl']; subst. apply IH; [|exact Hl'].
  unfold gbb_step. destruct (ch <=? p)%Z eqn:E1; [apply Z.leb_le in E1| apply Z.leb_gt in E1];
    destruct (acc <? ch)%Z; cbn [andb]; lia.
Qed.

Lemma gbb_fold_max : forall p MB l acc, (MB <= p)%Z -> (acc <= MB)%Z -> Forall (fun ch => ch <= p -> ch <= MB)%Z l ->
  (In MB l \/ acc = MB) -> gbb_fold p acc l = MB.
Proof.
  intros p MB l. induction l as [|ch l IH]; intros acc Hp Ha Hl Hin; cbn [gbb_fold].
  - destruct Hin as [[]| ->]. reflexivity.
  - inversion Hl as [|? ? Hc Hl']; subst. apply IH; [exact Hp| | exact Hl'|].
    + unfold gbb_step. destruct (ch <=? p)%Z eqn:E1; [apply Z.leb_le in E1| apply Z.leb_gt in E1];
        destruct (acc <? ch)%Z; cbn [andb]; lia.
    + destruct Hin as [[E|H]|E]; [right| left; exact H| right].
      * subst ch. unfold gbb_step. rewrite (proj2 (Z.leb_le MB p) Hp). cbn [andb].
        destruct (acc <? MB)%Z eqn:E2; [reflexivity| apply Z.ltb_ge in E2; lia].
      * subst acc. unfold gbb_step. destruct (ch <=? p)%Z eqn:E1; cbn [andb]; [|reflexivity].
        apply Z.leb_le in E1. destruct (MB <? ch)%Z eqn:E2; [apply Z.ltb_lt in E2; specialize (Hc E1); lia| reflexivity].
Qed.

Lemma firstn_map_step : forall (ws : list word) j w, nth_error ws (Z.to_nat j) = Some w -> (0 <= j)%Z ->
  firstn (Z.to_nat (j + 1)) (map bv_unsigned ws) = firstn (Z.to_nat j) (map bv_unsigned ws) ++ [bv_unsigned w].
Proof.
  intros ws j w Hw Hj. replace (Z.to_nat (j + 1)) with (S (Z.to_nat j)) by lia.
  assert (Hw' : nth_error (map bv_unsigned ws) (Z.to_nat j) = Some (bv_unsigned w)) by (rewrite nth_error_map, Hw; reflexivity).
  clear Hw. revert ws Hw'. induction (Z.to_nat j) as [|k IH]; intros ws Hw'; destruct ws as [|x ws]; cbn in *; try discriminate.
  - injection Hw' as <-. reflexivity.
  - f_equal. apply IH. exact Hw'.
Qed.

Lemma Forall_unsigned : forall (l : list word), Forall (fun ch => 0 <= ch)%Z (map bv_unsigned l).
Proof.
  induction l as [|x l IH]; cbn; constructor; [|exact IH].
  pose proof (bv_unsigned_in_range 64 x). lia.
Qed.

Lemma Forall_firstn_Z : forall (P : Z -> Prop) (l : list Z) k, Forall P l -> Forall P (firstn k l).
Proof.
  intros P l k H. revert k. induction H as [|x l Hx Hl IH]; intros [|k]; cbn; try constructor; auto.
Qed.

Lemma land4095_aligned : forall x, (0 <= x)%Z -> (x mod 4096 = 0)%Z -> Z.land x 4095 = 0%Z.
Proof.
  intros x Hx Hm. change 4095%Z with (Z.ones 12). rewrite Z.land_ones by lia. change (2 ^ 12)%Z with 4096%Z. exact Hm.
Qed.

(* [comment removed for export] *)
Section LOOP.
Variables (ra sp gp tp t1 t2 s0 s1 a0 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word) (F : bvmap 5 word) (fc : bv 32).
Variables (m : mem) (PAB n p : Z) (ws : list word) (Q : machine_state -> Prop).
Hypothesis ARR : u64arr asegs m PAB ws.
Hypothesis Hn : (1 <= n <= Z.of_nat (length ws))%Z.
Hypothesis HPAB : (0 < PAB /\ PAB + 8 * Z.of_nat (length ws) <= 2^63)%Z.
Hypothesis Hp : (0 <= p < 2^63)%Z.
Hypothesis K : forall (a2' a5' a6' a7' t0' : word),
  evt asegs Q
    (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 p) a2' (Z_to_bv 64 (gbb_fold p 0 (firstn (Z.to_nat n) (map bv_unsigned ws))))
             (Z_to_bv 64 (PAB + 8 * n)) a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d3a0) fc None m (seg_rom asegs)).

Lemma gbb_loop : forall k j (a5 a6 a7 t0 : word), Z.to_nat (n - j) = k -> (0 <= j < n)%Z ->
  evt asegs Q
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PAB + 8 * j))
             (Z_to_bv 64 (gbb_fold p 0 (firstn (Z.to_nat j) (map bv_unsigned ws)))) (Z_to_bv 64 (PAB + 8 * n))
             a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x19d374) fc None m (seg_rom asegs)).
Proof using ARR Hn HPAB Hp K.
  induction k as [|k IH]; intros j a5 a6 a7 t0 Hk Hj; [lia|].
  destruct (nth_error ws (Z.to_nat j)) as [w|] eqn:Hw; [| apply nth_error_None in Hw; lia].
  pose proof (u64arr_read asegs m PAB ws j w (Z_to_bv 64 (PAB + 8 * j)) ARR Hw ltac:(lia) ltac:(reflexivity)) as RD.
  pose proof (firstn_map_step ws j w Hw ltac:(lia)) as EF.
  pose proof (gbb_fold_range p (firstn (Z.to_nat j) (map bv_unsigned ws)) 0 ltac:(lia)
                (Forall_firstn_Z _ _ _ (Forall_unsigned ws))) as RA.
  set (acc := gbb_fold p 0 (firstn (Z.to_nat j) (map bv_unsigned ws))) in *.
  assert (EA : gbb_fold p 0 (firstn (Z.to_nat (j + 1)) (map bv_unsigned ws)) = gbb_step p acc (bv_unsigned w)).
  { rewrite EF, gbb_fold_app. reflexivity. }
  clearbody acc.
  pose proof (bv_unsigned_in_range 64 w) as RW. unfold bv_modulus in RW. cbn [Z.of_N] in RW.
  do 4 zstep. clear RD.
  zstep.
  (* [comment removed for export] *)
  assert (TAIL : forall (a3v : word) (a5' a6' a7' t0' : word), a3v = Z_to_bv 64 (gbb_step p acc (bv_unsigned w)) ->
    evt asegs Q
      (MS (mkR ra sp gp tp t0' t1 t2 s0 s1 a0 (Z_to_bv 64 p) (Z_to_bv 64 (PAB + 8 * j)) a3v (Z_to_bv 64 (PAB + 8 * n))
               a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
          F (Z_to_bv 64 0x19d36c) fc None m (seg_rom asegs))).
  { intros a3v a5' a6' a7' t0' ->. rewrite <- EA.
    zstep. zstep.
    destruct (Z.eq_dec (j + 1) n) as [Ej|Nj].
    - ifT. replace (Z.to_nat (j + 1)) with (Z.to_nat n) by lia. apply K.
    - ifF. replace (PAB + 8 * j + 8)%Z with (PAB + 8 * (j + 1))%Z by lia. apply (IH (j + 1)%Z); lia. }
  destruct (Z.le_gt_cases (bv_unsigned w) p) as [Hle|Hgt].
  - destruct (Z.lt_ge_cases acc (bv_unsigned w)) as [Hlt|Hge].
    + ifT. zstep. ifF. do 2 zstep. apply TAIL.
      unfold gbb_step. rewrite (proj2 (Z.leb_le _ _) Hle), (proj2 (Z.ltb_lt _ _) Hlt). cbn [andb].
      symmetry. apply Z_to_bv_bv_unsigned.
    + ifF. zstep. zstep. ifF. do 3 zstep. apply TAIL.
      unfold gbb_step. rewrite (proj2 (Z.ltb_ge _ _) Hge). rewrite Bool.andb_false_r. reflexivity.
  - if_cases K1.
    + zstep. ifT. apply TAIL.
      unfold gbb_step. rewrite (proj2 (Z.leb_gt _ _) Hgt). reflexivity.
    + zstep. zstep. ifT. apply TAIL.
      unfold gbb_step. rewrite (proj2 (Z.leb_gt _ _) Hgt). reflexivity.
Qed.
End LOOP.

(* [comment removed for export] *)
Definition gbb_mem (PAB nres n : Z) (ws : list word) (MB MSZ SZ IDX : Z) (m : mem) : Prop :=
  sec_page m /\ sec_core m PAB nres n /\ sec_pad m /\ u64arr asegs m PAB ws /\ shdr m MB MSZ SZ IDX.

Definition gbb_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (res : Z) (K : mem -> Prop) (lo : Z) (m : mem) : machine_state -> Prop :=
  fun ms' => exists (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (m' : mem),
    ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 res) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11
                  t3' t4' t5' t6') F (ret_pc ra) fc None m' (seg_rom asegs)
    /\ munch [(i_sec_mutex, i_sec_mutex + 4); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m m' /\ wmono asegs m m'
    /\ mem_inv asegs m' /\ stk asegs m' lo (bv_unsigned sp) /\ K m'.

(* [comment removed for export] *)
Lemma gbb_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo PAB nres n : Z) (ws : list word) (MB MSZ SZ IDX p : Z),
  gbb_mem PAB nres n ws MB MSZ SZ IDX m ->
  (0 < PAB)%Z -> (PAB + 8 * Z.of_nat (length ws) <= lo)%Z ->
  hide (PAB + 8 * Z.of_nat (length ws) <= img_hull_lo \/ img_hull_hi <= PAB)%Z ->
  (1 <= n <= Z.of_nat (length ws))%Z ->
  In MB (firstn (Z.to_nat n) (map bv_unsigned ws)) ->
  Forall (fun ch => ch <= p -> ch <= MB)%Z (firstn (Z.to_nat n) (map bv_unsigned ws)) ->
  (0 < MB)%Z -> (MB mod 4096 = 0)%Z -> (MB + MSZ <= lo)%Z -> (MB + 4096 <= p < MB + MSZ)%Z ->
  hide (MB + MSZ <= img_hull_lo \/ img_hull_hi <= MB)%Z ->
  stk asegs m lo (bv_unsigned sp) -> (kHighShadowEnd + 8 <= lo)%Z -> (lo <= bv_unsigned sp - 32)%Z -> (bv_unsigned sp <= 2^47)%Z ->
  mem_inv asegs m ->
  evt asegs (gbb_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (MB + 4096)
               (gbb_mem PAB nres n ws MB MSZ SZ IDX) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 SEC) (Z_to_bv 64 p) a2 a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 gbb_entry) fc None m (seg_rom asegs)).
Proof.
  intros until p. intros (PG & (CH & NR & MX) & PAD & ARR & HD) HPAB HPABl HPABs Hn HIN HMAX HMB0 HMBal HMBl Hp HMBs
    ST HLOH HLO HSP MI.
  pose proof (lockw_of m MX PAD) as LW. clear MX PAD.
  unfold hide, img_hull_lo, img_hull_hi in HPABs, HMBs.
  unfold sec_page, shdr in *.
  change i_sec_mutex with 6723456%Z in *. change i_sec_page with 6722840%Z in *. change i_sec_chunks with 6722848%Z in *.
  change i_sec_nres with 6722888%Z in *. change SEC with 6722840%Z.
  unfold kHighShadowEnd, gbb_entry in *.
  pose proof (munch_refl [(6723456, 6723456 + 4); (bv_unsigned sp - 32, bv_unsigned sp)]%Z m) as MU.
  pose proof (wmono_refl asegs m) as WM.
  carve_frame 32%nat ST.
  zidle_begin sp 32%Z MUz WMz.
  do 4 zstep.
  zidle_end MUz WMz.
  do 5 zstep.
  assert (AMO : amo_aligned AW (Z_to_bv 64 6723456) = true) by (vm_compute; reflexivity).
  amo_step AMO.
  replace (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0) by (vm_compute; reflexivity).
  do 4 zstep.
  amo_step AMO; try fix_lit_store.
  zstep. ifF.
  zstep. zstep. ifF.
  zstep. zstep. ifF.
  do 5 zstep.
  replace (PAB + n ≪ 3)%Z with (PAB + 8 * n)%Z by (rewrite Z.shiftl_mul_pow2 by lia; lia).
  replace (Z_to_bv 64 PAB) with (Z_to_bv 64 (PAB + 8 * 0)) by (f_equal; lia).
  eapply gbb_loop with (k := Z.to_nat (n - 0)) (j := 0%Z).
  all: cycle 5.
  all: try (exact ARR || lia || reflexivity).
  intros a2' a5' a6' a7' t0'.
  rewrite (gbb_fold_max p MB _ 0 ltac:(lia) ltac:(lia) HMAX (or_introl HIN)).
  zstep. ifF.
  zstep. zstep. ifF.
  do 2 zstep. zstep. ifF.
  zstep. ifF.
  zstep. ifF.
  do 3 zstep.
  rewrite (Z.land_comm 4095 MB), (land4095_aligned MB) by lia.
  zstep. ifF.
  do 2 zstep.
  zstep.
  apply lockw_to1 in LW. change i_sec_mutex with 6723456%Z in LW.
  zstep; fix_lit_store.
  do 6 zstep.
  rewrite (Z.add_comm 4096 MB).
  release_frame FR ST (bv_unsigned sp).
  change 6723456%Z with i_sec_mutex in LW. apply lockw_split in LW. destruct LW as [MX PAD].
  assert (KM : gbb_mem PAB nres n ws MB MSZ SZ IDX m1).
  { unfold gbb_mem. split; [exact PG|]. split; [split; [exact CH| split; [exact NR| exact MX]]|].
    split; [exact PAD|]. split; [exact ARR| exact HD]. }
  apply evt_done. unfold gbb_post. do 15 eexists.
  split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact ST| exact KM].
Qed.
