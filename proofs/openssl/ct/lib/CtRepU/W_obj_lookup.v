(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem Bytes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim ApObjTab ApObj.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac ApCells ApRepDefs ApRep ApWalkTac ApObjRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

Definition MEMCMP : Z := 0x2bd74c.
Definition OBJ_CMP_FN : Z := 0xfcaac.        (* [comment removed for export] *)
Definition OBJ_CMP : Z := 0x10e1f8.
Definition OSSL_BSEARCH : Z := 0xecef4.
Definition OSSL_OBJ_OBJ2NID : Z := 0xfbfcc.
Definition OBJ_OBJ2NID : Z := 0xfbd8c.
Definition OBJ_NID2OBJ : Z := 0xfb33c.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition zbytes (bs : list byte) : list Z := map bv_unsigned bs.

Lemma bytes_cmp_skip : forall (xs ys : list Z) i,
  (i <= length xs)%nat -> (i <= length ys)%nat ->
  (forall j, (j < i)%nat -> nth_error xs j = nth_error ys j) ->
  bytes_cmp xs ys = bytes_cmp (skipn i xs) (skipn i ys).
Proof.
  intros xs ys i. revert xs ys. induction i as [|i IH]; intros xs ys Hx Hy HE; [reflexivity|].
  destruct xs as [|x xs]; [cbn in Hx; lia|]. destruct ys as [|y ys]; [cbn in Hy; lia|].
  pose proof (HE 0%nat ltac:(lia)) as E0. cbn in E0. injection E0 as ->.
  cbn [bytes_cmp skipn]. rewrite Z.eqb_refl. apply IH; [cbn in Hx; lia| cbn in Hy; lia|].
  intros j Hj. apply (HE (S j)). lia.
Qed.

Lemma bytes_cmp_range : forall xs ys, Forall (fun x => 0 <= x < 256) xs -> Forall (fun y => 0 <= y < 256) ys -> -255 <= bytes_cmp xs ys <= 255.
Proof.
  induction xs as [|x xs IH]; intros ys HX HY; [cbn; lia|]. destruct ys as [|y ys]; [cbn; lia|].
  inversion HX; inversion HY; subst. cbn [bytes_cmp]. destruct (Z.eqb_spec x y); [apply IH; assumption| lia].
Qed.

Lemma zbytes_range : forall bs, Forall (fun x => 0 <= x < 256) (zbytes bs).
Proof.
  induction bs as [|b bs IH]; [constructor|]. cbn. constructor; [| exact IH].
  pose proof (bv_unsigned_in_range 8 b) as R. unfold bv_modulus in R. cbn in R. lia.
Qed.

Lemma skipn_nth_cons : forall {T} (l : list T) n x, nth_error l n = Some x -> skipn n l = x :: skipn (S n) l.
Proof.
  induction l as [|y l IH]; intros [|n] x H; cbn in H; try discriminate.
  - injection H as ->. reflexivity.
  - cbn. exact (IH n x H).
Qed.

Lemma land_M64_small : forall x, 0 <= x < 2^64 -> Z.land x 18446744073709551615 = x.
Proof. intros x Hx. rewrite <- unsigned_lit_land. apply unsigned_lit. exact Hx. Qed.

Lemma memcmp_loop : forall ra sp gp tp t0 t1 t2 s0 s1 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (A B : Z) (xs ys : list byte) (k : nat) (i : Z) (a3 a4 : word),
  mem_inv ctusegs m -> bytes_at ctusegs m A xs -> bytes_at ctusegs m B ys -> length ys = length xs ->
  Z.to_nat (Z.of_nat (length xs) - i) = k -> 0 <= i < Z.of_nat (length xs) ->
  bytes_cmp (zbytes xs) (zbytes ys) = bytes_cmp (skipn (Z.to_nat i) (zbytes xs)) (skipn (Z.to_nat i) (zbytes ys)) ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (bytes_cmp (zbytes xs) (zbytes ys))) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m (seg_rom ctusegs))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 (A + i)) (Z_to_bv 64 (B + i)) (Z_to_bv 64 (Z.of_nat (length xs) - i)) a3 a4 a5 a6 a7
             s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 0x2bd750) fc None m (seg_rom ctusegs)).
Proof.
  intros until k. induction k as [|k IH]; intros i a3 a4 MI HX HY LEN Hk Hi HC; [lia|].
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HY) as YB.
  pose proof (munch_refl []%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  destruct (nth_error xs (Z.to_nat i)) as [x|] eqn:EX; [| apply nth_error_None in EX; lia].
  destruct (nth_error ys (Z.to_nat i)) as [y|] eqn:EY; [| apply nth_error_None in EY; lia].
  pose proof (u8ro_read ctusegs m A xs i x _ HX EX ltac:(lia) eq_refl) as RDX.
  pose proof (u8ro_read ctusegs m B ys i y _ HY EY ltac:(lia) eq_refl) as RDY.
  pose proof (bv_unsigned_in_range 8 x) as XR. unfold bv_modulus in XR. cbn in XR.
  pose proof (bv_unsigned_in_range 8 y) as YR. unfold bv_modulus in YR. cbn in YR.
  assert (SX : skipn (Z.to_nat i) (zbytes xs) = bv_unsigned x :: skipn (Z.to_nat (i + 1)) (zbytes xs)).
  { unfold zbytes. rewrite !skipn_map. rewrite (skipn_nth_cons _ _ _ EX). replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. }
  assert (SY : skipn (Z.to_nat i) (zbytes ys) = bv_unsigned y :: skipn (Z.to_nat (i + 1)) (zbytes ys)).
  { unfold zbytes. rewrite !skipn_map. rewrite (skipn_nth_cons _ _ _ EY). replace (Z.to_nat (i + 1)) with (S (Z.to_nat i)) by lia. reflexivity. }
  rewrite SX, SY in HC. cbn [bytes_cmp] in HC.
  zstep. zstep.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    (* [comment removed for export] *)
    zstep. zstep.
    destruct (Z.eqb_spec (bv_unsigned x) (bv_unsigned y)) as [E|NE]; [exfalso; exact (K E)|].
    rewrite HC. finish.
  - (* [comment removed for export] *)
    assert (E : bv_unsigned x = bv_unsigned y) by (rewrite K; reflexivity).
    rewrite E, Z.eqb_refl in HC.
    zstep. zstep. zstep.
    zstep. if_cases K2; zify_cond K2.
    + replace (Z.of_nat (length xs) - i + -1) with (Z.of_nat (length xs) - (i + 1)) by lia.
      replace (A + i + 1) with (A + (i + 1)) by lia. replace (B + i + 1) with (B + (i + 1)) by lia.
      apply IH; try assumption; try lia.
    + (* [comment removed for export] *)
      (* [comment removed for export] *)
      zstep. zstep.
      assert (Hend : i + 1 = Z.of_nat (length xs)) by (rewrite ?unsigned_lit in K2 by lia; lia).
      rewrite HC. rewrite !skipn_all2 by (unfold zbytes; rewrite length_map; lia). cbn [bytes_cmp]. finish.
Qed.

Definition memcmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m (seg_rom ctusegs).

(* [comment removed for export] *)
Lemma memcmp_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (xs ys : list byte),
  mem_inv ctusegs m -> bytes_at ctusegs m (bv_unsigned a0) xs -> bytes_at ctusegs m (bv_unsigned a1) ys ->
  length ys = length xs -> a2 = Z_to_bv 64 (Z.of_nat (length xs)) -> Z.of_nat (length xs) < 2^63 ->
  evt ctusegs (memcmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc (bytes_cmp (zbytes xs) (zbytes ys)) m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 MEMCMP) fc None m (seg_rom ctusegs)).
Proof.
  intros until ys. intros MI HX HY LEN -> LT. unfold MEMCMP, memcmp_post.
  pose proof (bytes_at_bound _ _ _ _ HX) as XB. pose proof (bytes_at_bound _ _ _ _ HY) as YB.
  pose proof (munch_refl []%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  zstep. if_cases K; zify_cond K.
  - (* [comment removed for export] *)
    zstep. zstep.
    assert (X0 : length xs = 0%nat) by (rewrite ?land_M64_small in K by lia; lia).
    destruct xs; [| cbn in X0; lia]. destruct ys; [| cbn in LEN; lia]. cbn [zbytes map bytes_cmp]. finish.
  - rewrite ?land_M64_small in K by lia.
    setreg 10%Z (Z_to_bv 64 (bv_unsigned a0 + 0)) ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    setreg 11%Z (Z_to_bv 64 (bv_unsigned a1 + 0)) ltac:(rewrite Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity).
    setreg 12%Z (Z_to_bv 64 (Z.of_nat (length xs) - 0)) ltac:(f_equal; lia).
    eapply memcmp_loop; try eassumption; try lia. all: cbn [Z.to_nat skipn]. all: reflexivity.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_entry (m : mem) (i idx ED : Z) : Prop :=
  let '(nid, content, lnlen) := tab_entry i in
  0 <= idx < NUM_NID /\ 0 <= ED /\ ED + zlength content <= IMG_LO /\ 0 <= nid < 2^31 /\
  ro_cells ctusegs m (P_OBJ_OBJS_VA + 4 * i) [C4 (wz idx)] /\
  ro_cells ctusegs m (P_NID_OBJS_VA + 40 * idx + 16) [C4 (wz nid); C4 (wz (zlength content)); C8 (wz ED)] /\
  bytes_at ctusegs m ED (map (Z_to_bv 8) content) /\ Forall (fun c => 0 <= c < 256) content /\
  idx = nid /\ ro_cells ctusegs m (P_NID_OBJS_VA + 40 * idx + 32) [C4 (wz 0)]      (* [comment removed for export] *)
  /\ (0 < zlength content -> 0 < nid).                                                (* [comment removed for export] *)
Definition obj_table_ok (m : mem) : Prop := forall i, 0 <= i < NUM_OBJ -> exists idx ED, obj_entry m i idx ED.

Lemma zbytes_of_Z : forall content, Forall (fun c => 0 <= c < 256) content -> zbytes (map (Z_to_bv 8) content) = content.
Proof.
  induction content as [|c cs IH]; intros H; [reflexivity|]. inversion H; subst. cbn. f_equal; [| apply IH; assumption].
  apply Z_to_bv_small. unfold bv_modulus. cbn. lia.
Qed.
Lemma zlength_zbytes : forall bs, zlength (zbytes bs) = Z.of_nat (length bs).
Proof. intros. unfold zlength, zbytes. rewrite length_map. reflexivity. Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint bytes_eqb (xs ys : list byte) : bool :=
  match xs, ys with
  | [], [] => true
  | x :: xs', y :: ys' => bv_eqb x y && bytes_eqb xs' ys'
  | _, _ => false
  end.
Lemma bytes_eqb_eq : forall xs ys, bytes_eqb xs ys = true -> xs = ys.
Proof.
  induction xs as [|x xs IH]; intros [|y ys] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. unfold bv_eqb in H1. apply Z.eqb_eq in H1. apply bv_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.

Definition obj_entry_check (i : Z) : bool :=
  let '(nid, content, lnlen) := tab_entry i in
  match image_bytes ctusegs (P_OBJ_OBJS_VA + 4 * i) 4 with
  | Some ib =>
      let idx := le_val (zbytes ib) in
      match image_bytes ctusegs (P_NID_OBJS_VA + 40 * idx + 16) 16 with
      | Some fb =>
          let ED := le_val (zbytes (skipn 8 fb)) in
          (0 <=? idx) && (idx <? NUM_NID) && (0 <=? nid) && (nid <? 2^31) && (0 <=? ED) && (ED + zlength content <=? IMG_LO)
          && bytes_eqb ib (le4 (wz idx))
          && bytes_eqb fb (le4 (wz nid) ++ le4 (wz (zlength content)) ++ le8 (wz ED))
          && ro_bytes_b ctusegs (P_OBJ_OBJS_VA + 4 * i) ib
          && ro_bytes_b ctusegs ED (map (Z_to_bv 8) content)
          && forallb (fun c => (0 <=? c) && (c <? 256)) content
          && (idx =? nid)
          && match image_bytes ctusegs (P_NID_OBJS_VA + 40 * idx + 32) 4 with Some zb => bytes_eqb zb (le4 (wz 0)) | None => false end
          && ((zlength content =? 0) || (0 <? nid))
      | None => false
      end
  | None => false
  end.

Fixpoint zrange (k : nat) (z : Z) : list Z := match k with O => [] | S k' => z :: zrange k' (z + 1) end.
Lemma zrange_In : forall k z x, z <= x < z + Z.of_nat k -> In x (zrange k z).
Proof.
  induction k as [|k IH]; intros z x H; [lia|]. cbn. destruct (Z.eq_dec z x); [left; exact e| right]. apply IH. lia.
Qed.

Lemma obj_table_check : forallb obj_entry_check (zrange 1352 0) = true.
Proof. vm_compute. reflexivity. Qed.

Lemma ro_cells_recast : forall m A cs cs',
  ro_cells ctusegs m A cs -> cells_wf cs' -> cells_bytes cs' = cells_bytes cs -> ro_cells ctusegs m A cs'.
Proof. intros m A cs cs' [Hwf Hb] Hwf' Eb. split; [exact Hwf'| rewrite Eb; exact Hb]. Qed.

Lemma obj_entry_check_sound : forall m i, mem_inv ctusegs m -> ap_img m -> 0 <= i < NUM_OBJ -> obj_entry_check i = true -> exists idx ED, obj_entry m i idx ED.
Proof.
  intros m i MI IMG I0 H. unfold obj_entry_check in H. unfold obj_entry.
  destruct (tab_entry i) as [[nid content] lnlen].
  destruct (image_bytes ctusegs (P_OBJ_OBJS_VA + 4 * i) 4) as [ib|] eqn:IB; [|discriminate].
  set (idx := le_val (zbytes ib)) in H.
  destruct (image_bytes ctusegs (P_NID_OBJS_VA + 40 * idx + 16) 16) as [fb|] eqn:FB; [|discriminate].
  set (ED := le_val (zbytes (skipn 8 fb))) in H.
  repeat (apply andb_prop in H; destruct H as [H ?X]).
  rename X into NZ, X0 into ZB, X1 into INID, X2 into CR, X3 into ROC, X4 into ROI, X5 into EFB, X6 into EIB, X7 into EDL, X8 into ED0, X9 into NIDH, X10 into NID0, X11 into IDXH.
  apply Z.eqb_eq in INID.
  destruct (image_bytes ctusegs (P_NID_OBJS_VA + 40 * idx + 32) 4) as [zb|] eqn:ZBI; [|discriminate]. apply bytes_eqb_eq in ZB.
  pose proof (image_bytes_length _ _ _ _ ZBI) as ZBL.
  apply Z.leb_le in H. apply Z.ltb_lt in IDXH. apply Z.leb_le in NID0. apply Z.ltb_lt in NIDH. apply Z.leb_le in ED0. apply Z.leb_le in EDL.
  apply bytes_eqb_eq in EIB. apply bytes_eqb_eq in EFB.
  pose proof (image_bytes_length _ _ _ _ IB) as IBL. pose proof (image_bytes_length _ _ _ _ FB) as FBL.
  assert (CRF : Forall (fun c => 0 <= c < 256) content).
  { apply Forall_forall. intros c Hc. apply (proj1 (forallb_forall _ _) CR) in Hc. apply andb_prop in Hc. destruct Hc as [H1 H2].
    apply Z.leb_le in H1. apply Z.ltb_lt in H2. lia. }
  exists idx, ED. unfold NUM_NID, NUM_OBJ, IMG_LO, P_OBJ_OBJS_VA, P_NID_OBJS_VA in *.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { eapply ro_cells_recast; [eapply (ro_cells_image ctusegs m _ ib MI ROI); [lia| rewrite IBL; lia]| cbn; tauto| ].
           cbn [cells_bytes cbytes]. rewrite !app_nil_r. symmetry. exact EIB. }
  split. { eapply ro_cells_recast; [eapply (ap_img_ro_cells m _ 16%nat fb IMG); [unfold IMG_LO; lia| unfold IMG_HI; lia| exact FB]| cbn; tauto| ].
           cbn [cells_bytes cbytes]. rewrite !app_nil_r. symmetry. rewrite EFB. rewrite <- ?app_assoc. reflexivity. }
  split. { pose proof (ro_cells_image ctusegs m ED (map (Z_to_bv 8) content) MI ROC ltac:(lia) ltac:(rewrite length_map; unfold zlength in EDL; lia)) as [_ HB].
           cbn [cells_bytes cbytes] in HB. rewrite ?app_nil_r in HB. exact HB. }
  split; [exact CRF|]. split; [exact INID|].
  split. { eapply ro_cells_recast; [eapply (ap_img_ro_cells m _ 4%nat zb IMG); [unfold IMG_LO; lia| unfold IMG_HI; lia| exact ZBI]| cbn; tauto| ].
           cbn [cells_bytes cbytes]. rewrite !app_nil_r. symmetry. exact ZB. }
  intros HC. apply Bool.orb_prop in NZ. destruct NZ as [NZ|NZ]; [apply Z.eqb_eq in NZ; lia| apply Z.ltb_lt in NZ; exact NZ].
Qed.

Theorem obj_table_ok_intro : forall m, mem_inv ctusegs m -> ap_img m -> obj_table_ok m.
Proof.
  intros m MI IMG i Hi. apply obj_entry_check_sound; [exact MI| exact IMG| exact Hi|].
  apply (proj1 (forallb_forall _ _) obj_table_check). apply zrange_In. unfold NUM_OBJ in Hi. lia.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition obj_cmp_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma obj_cmp_fn_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo KP KA KD knid : Z) (kb : list byte) (i idx ED : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  rw_cells ctusegs m KP [C8 (wz KA)] -> bv_unsigned sp <= KP -> KP mod 8 = 0 ->
  rw_cells ctusegs m (KA + 16) [C4 (wz knid); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] ->
  (bv_unsigned sp <= KA + 16 \/ KA + 32 <= lo) -> KA mod 8 = 0 -> 0 < KA -> Z.of_nat (length kb) < 2^31 ->
  bytes_at ctusegs m KD kb -> KD + Z.of_nat (length kb) <= lo ->
  0 <= i < NUM_OBJ -> obj_entry m i idx ED ->
  a0 = wz KP -> a1 = wz (P_OBJ_OBJS_VA + 4 * i) ->
  evt ctusegs (obj_cmp_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (obj_cmp (zbytes kb) (snd (fst (tab_entry i)))) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OBJ_CMP_FN) fc None m (seg_rom ctusegs)).
Proof.
  intros until ED. intros ST MI GLO LO HKP KPS KP8 HKA KAS KA8 KA0 KL HKB KDL Hi HE -> ->.
  unfold OBJ_CMP_FN, GLOBALS_TOP, MallocRep.wz, obj_cmp_post in *.
  unfold obj_entry in HE. destruct (tab_entry i) as [[nid content] lnlen] eqn:TE. cbn [fst snd].
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ).
  unfold NUM_NID, NUM_OBJ, IMG_LO, P_OBJ_OBJS_VA, P_NID_OBJS_VA, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HKP) as KPB. pose proof (rw_cells_bound _ _ _ _ HKA) as KAB. cbn in KPB, KAB.
  pose proof (bytes_at_bound _ _ _ _ HKB) as KDB. pose proof (bytes_at_bound _ _ _ _ HEB) as EDB. rewrite length_map in EDB.
  pose proof (proj1 (Forall_forall _ _) CR) as CR'.
  assert (CL : zlength content = Z.of_nat (length content)) by reflexivity.
  remember (map (Z_to_bv 8) content) as eb eqn:EB.
  assert (EBL : Z.of_nat (length eb) = zlength content) by (subst eb; rewrite length_map; reflexivity).
  assert (EDL' : ED + Z.of_nat (length eb) <= 2898472) by lia.
  (* [comment removed for export] *)
  replace (262212 + 4 * i) with (4 * i + 262212) in RO1 by lia.
  carve_frame 16%nat ST. do 4 zstep.
  setreg 11%Z (Z_to_bv 64 (4 * i + 262212)) ltac:(f_equal; lia).
  ub. zstep. zstep.
  setreg 11%Z (Z_to_bv 64 (2898056 + 40 * idx)) ltac:(symmetry; apply bv_eq; rewrite ?usx32_small by lia; rewrite ?unsigned_lit by lia; bv_solve).
  do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  (* [comment removed for export] *)
  carve_frame 16%nat ST. do 4 zstep. ub.
  zstep. zstep. rewrite ?sx32_small by lia. zstep. zstep. ub. zstep. rewrite ?bk_swrap32_small by lia.
  zstep. if_cases K0; zify_cond K0.
  - (* [comment removed for export] *)
    change 18446744073709551615 with (Z.ones 64) in K0. rewrite Z.land_ones in K0 by lia.
    assert (LE : Z.of_nat (length kb) = zlength content) by (revert K0; rewrite !Z.land_ones, Z.add_0_r by lia; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; cbn [Z.of_N]; intros K0; Z.div_mod_to_equations; lia). clear K0.
    zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      zstep. zstep. do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
      replace (obj_cmp (zbytes kb) content) with 0.
      2:{ unfold obj_cmp. rewrite zlength_zbytes, LE, Z.sub_diag. cbn [Z.eqb].
          destruct kb; [| cbn in K1; lia]. destruct content; [reflexivity| rewrite CL in LE; cbn in LE; lia]. }
      finish.
    + zstep. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep. zstep.
      eapply evt_mono; [eapply memcmp_spec with (xs := kb) (ys := eb);
        [assumption| rewrite unsigned_lit by lia; eassumption| rewrite unsigned_lit by lia; exact HEB| subst eb; rewrite length_map; lia| f_equal; lia| lia]|].
      unfold memcmp_post. intros ms' PO.
      destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & ->).
      subst eb. rewrite (zbytes_of_Z content CR). unfold obj_cmp. rewrite zlength_zbytes, LE, Z.sub_diag. cbn [Z.eqb].
      do 15 eexists. split; [reflexivity|]. auto.
  - (* [comment removed for export] *)
    assert (NE : Z.of_nat (length kb) - zlength content <> 0) by (intros E0; apply K0; replace (Z.of_nat (length kb) + - zlength content) with 0 by lia; reflexivity). clear K0.
    do 4 zstep. setreg 10%Z (Z_to_bv 64 (Z.of_nat (length kb) - zlength content)) ltac:(f_equal; try change 18446744073709551615 with (Z.ones 64); rewrite ?Z.land_ones, ?Z.add_0_r by lia; unfold bv_swrap, bv_wrap, bv_half_modulus, bv_modulus; cbn [Z.of_N]; Z.div_mod_to_equations; lia). release_frame FR ST (bv_unsigned sp). zstep.
    replace (obj_cmp (zbytes kb) content) with (Z.of_nat (length kb) - zlength content).
    2:{ unfold obj_cmp. rewrite zlength_zbytes. destruct (Z.eqb_spec (Z.of_nat (length kb) - zlength content) 0); [lia| reflexivity]. }
    finish.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint obj_bsearch_idx (fuel : nat) (key : list Z) (l h : Z) {struct fuel} : option Z :=
  match fuel with
  | O => None
  | S fuel' =>
      if l <? h then
        let i := l + (h - l) / 2 in
        let c := obj_cmp key (snd (fst (tab_entry i))) in
        if c <? 0 then obj_bsearch_idx fuel' key l i
        else if 0 <? c then obj_bsearch_idx fuel' key (i + 1) h
        else Some i
      else None
  end.

Lemma obj_bsearch_loop_idx : forall fuel key l h,
  obj_bsearch_loop fuel key l h
  = match obj_bsearch_idx fuel key l h with Some i => Some (fst (fst (tab_entry i)), snd (tab_entry i)) | None => None end.
Proof.
  induction fuel as [|fuel IH]; intros key l h; cbn [obj_bsearch_loop obj_bsearch_idx]; [reflexivity|].
  destruct (l <? h); [|reflexivity]. cbv zeta.
  destruct (tab_entry (l + (h - l) / 2)) as [[nid content] lnlen] eqn:TE. cbn [fst snd].
  destruct (obj_cmp key content <? 0); [apply IH|]. destruct (0 <? obj_cmp key content); [apply IH|]. rewrite TE. reflexivity.
Qed.

Lemma obj_bsearch_idx_range : forall fuel key l h i, obj_bsearch_idx fuel key l h = Some i -> l <= i < h.
Proof.
  induction fuel as [|fuel IH]; intros key l h i H; cbn [obj_bsearch_idx] in H; [discriminate|].
  destruct (Z.ltb_spec l h); [|discriminate]. cbv zeta in H.
  destruct (obj_cmp key (snd (fst (tab_entry (l + (h - l) / 2)))) <? 0).
  - apply IH in H. Z.div_mod_to_equations. lia.
  - destruct (0 <? obj_cmp key (snd (fst (tab_entry (l + (h - l) / 2))))).
    + apply IH in H. Z.div_mod_to_equations. lia.
    + injection H as <-. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma OBJ_BSEARCH_FUEL_eq : OBJ_BSEARCH_FUEL = 32%nat. Proof. reflexivity. Qed.
#[local] Opaque OBJ_BSEARCH_FUEL.

Definition bsearch_res (r : option Z) : Z := match r with Some i => P_OBJ_OBJS_VA + 4 * i | None => 0 end.

Definition OSSL_BSEARCH_STACK : Z := 128.

Definition bsearch_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - OSSL_BSEARCH_STACK, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma srl31_small : forall d, 0 <= d < 2^31 -> bv_swrap 32 (Z.shiftr (bv_wrap 32 d) 31) = 0.
Proof.
  intros d Hd. rewrite bv_wrap_small by (unfold bv_modulus; cbn; lia).
  rewrite Z.shiftr_div_pow2, Z.div_small by lia. apply bk_swrap32_small. lia.
Qed.
Lemma sra1_small : forall d, 0 <= d < 2^31 -> bv_swrap 32 (Z.shiftr (bv_swrap 32 d) 1) = d / 2.
Proof.
  intros d Hd. rewrite (bk_swrap32_small d) by lia. rewrite Z.shiftr_div_pow2 by lia. change (2^1) with 2.
  apply bk_swrap32_small. Z.div_mod_to_equations. lia.
Qed.

(* [comment removed for export] *)
Lemma disjoint_from_high : forall W a n, Forall (fun iv => a + n <= fst iv) W -> disjoint_from W a n.
Proof. induction W as [|[u v] W IH]; intros a n H; cbn; [exact I|]. inversion H; subst. cbn in *. split; [lia| apply IH; assumption]. Qed.

Lemma obj_entry_transport : forall m m' W i idx ED,
  obj_entry m i idx ED -> munch W m m' -> Forall (fun iv => GLOBALS_TOP <= fst iv) W -> 0 <= i < NUM_OBJ -> obj_entry m' i idx ED.
Proof.
  intros m m' W i idx ED HE MU HW Hi. unfold obj_entry in *. destruct (tab_entry i) as [[nid content] lnlen].
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ).
  unfold NUM_NID, NUM_OBJ, IMG_LO, P_OBJ_OBJS_VA, P_NID_OBJS_VA, GLOBALS_TOP in *.
  pose proof (bytes_at_bound _ _ _ _ HEB) as EDB. rewrite length_map in EDB.
  assert (CL : Z.of_nat (length content) = zlength content) by reflexivity.
  split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|].
  split. { eapply ro_cells_transport; [exact RO1| exact MU|]. apply disjoint_from_high. eapply Forall_impl; [| exact HW]. intros [u v] Hu. cbn in *. lia. }
  split. { eapply ro_cells_transport; [exact RO2| exact MU|]. apply disjoint_from_high. eapply Forall_impl; [| exact HW]. intros [u v] Hu. cbn in *. lia. }
  split. { eapply bytes_at_transport; [exact HEB| exact MU|]. apply disjoint_from_high. eapply Forall_impl; [| exact HW]. intros [u v] Hu.
           rewrite length_map. cbn in *. lia. }
  split; [exact CR|]. split; [exact INID|]. split; [| exact NZ].
  eapply ro_cells_transport; [exact ROF| exact MU|]. apply disjoint_from_high. eapply Forall_impl; [| exact HW]. intros [u v] Hu. cbn in *. lia.
Qed.
Lemma obj_table_ok_transport : forall m m' W,
  obj_table_ok m -> munch W m m' -> Forall (fun iv => GLOBALS_TOP <= fst iv) W -> obj_table_ok m'.
Proof. intros m m' W T MU HW i Hi. destruct (T i Hi) as (idx & ED & HE). exists idx, ED. eapply obj_entry_transport; eauto. Qed.

Lemma obj_cmp_range : forall kb content, Z.of_nat (length kb) < 2^31 -> 0 <= zlength content < 2^31 -> Forall (fun c => 0 <= c < 256) content ->
  -2^31 < obj_cmp (zbytes kb) content < 2^31.
Proof.
  intros kb content H1 H2 CR. unfold obj_cmp. rewrite zlength_zbytes.
  destruct (Z.eqb_spec (Z.of_nat (length kb) - zlength content) 0); [| lia].
  pose proof (bytes_cmp_range (zbytes kb) content (zbytes_range kb) CR). lia.
Qed.

Lemma sign_land64 : forall c, -2^63 <= c < 2^63 -> (2^63 <= Z.land c 18446744073709551615 <-> c < 0).
Proof.
  intros c Hc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  Z.div_mod_to_equations. lia.
Qed.
Lemma land64_zero : forall c, -2^63 <= c < 2^63 -> (Z.land c 18446744073709551615 = 0 <-> c = 0).
Proof.
  intros c Hc. change 18446744073709551615 with (Z.ones 64). rewrite Z.land_ones by lia.
  Z.div_mod_to_equations. lia.
Qed.

Section BsearchLoop.
  Variables (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32).
  Variables (m0 : word -> option byte) (lo KP KA KD knid : Z) (kb : list byte).
  Hypothesis GLO : GLOBALS_TOP <= lo.
  Hypothesis LO : lo <= bv_unsigned sp - OSSL_BSEARCH_STACK.
  Hypothesis KPS : bv_unsigned sp <= KP.
  Hypothesis KAS : bv_unsigned sp <= KA + 16 \/ KA + 32 <= lo.
  Hypothesis KL : Z.of_nat (length kb) < 2^31.
  Hypothesis KDL : KD + Z.of_nat (length kb) <= lo.
  Hypothesis KP8 : KP mod 8 = 0.
  Hypothesis KA8 : KA mod 8 = 0.
  Hypothesis KA0 : 0 < KA.

  (* [comment removed for export] *)
  Lemma bsearch_loop : forall (fuel : nat) (l h : Z) (rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 : word) (j8 : list byte) (m : word -> option byte),
    h - l < 2 ^ Z.of_nat fuel -> 0 <= l < h -> h <= NUM_OBJ ->
    stk ctusegs m lo (bv_unsigned sp - 112) -> mem_inv ctusegs m -> obj_table_ok m ->
    rw_cells ctusegs m KP [C8 (wz KA)] ->
    rw_cells ctusegs m (KA + 16) [C4 (wz knid); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] ->
    bytes_at ctusegs m KD kb ->
    rw_cells ctusegs m (bv_unsigned sp - 112) [CB 8 j8; C8 s11; C8 s10; C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
    munch [(bv_unsigned sp - OSSL_BSEARCH_STACK, bv_unsigned sp)]%Z m0 m -> wmono ctusegs m0 m ->
    evt ctusegs (bsearch_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                   (bsearch_res (obj_bsearch_idx fuel (zbytes kb) l h)) lo m0)
      (MS (mkR rax (Z_to_bv 64 (bv_unsigned sp - 112)) gp tp t0 t1 t2 sp (Z_to_bv 64 P_OBJ_OBJS_VA)
               a0 a1 a2 a3 a4 a5 a6 a7
               (Z_to_bv 64 4) (Z_to_bv 64 0) (Z_to_bv 64 OBJ_CMP_FN) (Z_to_bv 64 KP) (Z_to_bv 64 0) x23 (Z_to_bv 64 h) (Z_to_bv 64 1) x26 (Z_to_bv 64 l)
               t3 t4 t5 t6)
          F (Z_to_bv 64 0xecf5c) fc None m (seg_rom ctusegs)).
  Proof using GLO LO KPS KAS KL KDL KP8 KA8 KA0.
    induction fuel as [|fuel IH]; intros l h rax t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x23 x26 t3 t4 t5 t6 j8 m FU LH HN ST MI TOK HKP HKA HKB FR MU WM.
    { cbn in FU. lia. }
    unfold OSSL_BSEARCH_STACK, NUM_OBJ, GLOBALS_TOP, P_OBJ_OBJS_VA, OBJ_CMP_FN, MallocRep.wz in *.
    pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
    rewrite Nat2Z.inj_succ, Z.pow_succ_r in FU by lia.
    set (i := l + (h - l) / 2).
    assert (IR : l <= i < h) by (subst i; Z.div_mod_to_equations; lia).
    destruct (TOK i ltac:(unfold NUM_OBJ; lia)) as (idx & ED & HE).
    cbn [obj_bsearch_idx]. replace (l <? h) with true by (symmetry; apply Z.ltb_lt; lia). cbv zeta. fold i.
    (* [comment removed for export] *)
    do 25 (first [ ub1 | zstep ]; try udecide;
           repeat first [ rewrite (srl31_small (h + - l)) by lia | rewrite (sra1_small (h + - l)) by lia | rewrite Z.add_0_r
                        | rewrite land_M64_small by (Z.div_mod_to_equations; lia) | rewrite bk_swrap32_small by (Z.div_mod_to_equations; lia) ]).
    change (h + - l) with (h - l). fold i.
    (* [comment removed for export] *)
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into mc end.
    assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 112)) = bv_unsigned sp - 112) by (apply unsigned_lit; lia).
    pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z mc) as MUm.
    eapply evt_cut.
    { eapply obj_cmp_fn_spec with (lo := lo) (KA := KA) (KD := KD) (knid := knid) (kb := kb) (i := i) (idx := idx) (ED := ED);
        [ rewrite ESP; exact ST | exact MI | unfold GLOBALS_TOP; lia | rewrite ESP; lia | exact HKP | rewrite ESP; lia | exact KP8 | exact HKA
        | rewrite ESP; lia | exact KA8 | exact KA0 | exact KL | exact HKB | exact KDL | unfold NUM_OBJ; lia | exact HE | reflexivity | unfold P_OBJ_OBJS_VA, i; f_equal; lia ]. }
    unfold obj_cmp_post.
    post_call_esp ESP mc. rewrite ?ESP in *.
    match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end.
    lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
    assert (TOK2 : obj_table_ok m2).
    { eapply obj_table_ok_transport; [exact TOK| exact MUm|]. constructor; [cbn; unfold GLOBALS_TOP; lia| constructor]. }
    assert (CR : -2^31 < obj_cmp (zbytes kb) (snd (fst (tab_entry i))) < 2^31).
    { pose proof HE as HE'. unfold obj_entry in HE'. destruct (tab_entry i) as [[nid content] lnlen]. cbn [fst snd].
      destruct HE' as (_ & ED0 & EDL & _ & _ & _ & _ & CRF & _ & _). apply obj_cmp_range; [exact KL| unfold IMG_LO, zlength in *; lia| exact CRF]. }
    set (c := obj_cmp (zbytes kb) (snd (fst (tab_entry i)))) in *.
    zstep.
    zstep. if_cases K1; zify_cond K1.
    - (* [comment removed for export] *)
      assert (CN : c < 0) by (apply (proj1 (sign_land64 c ltac:(lia))); exact K1). clear K1.
      replace (c <? 0) with true by (symmetry; apply Z.ltb_lt; exact CN).
      zstep. zstep. if_cases K2; zify_cond K2.
      + (* [comment removed for export] *)
        rewrite signed_small in K2 by lia. rewrite signed_small in K2 by lia.
        eapply IH; try eassumption; try lia.
      + (* [comment removed for export] *)
        rewrite signed_small in K2 by lia. rewrite signed_small in K2 by lia.
        assert (EI : i = l) by lia.
        replace (obj_bsearch_idx fuel (zbytes kb) l i) with (@None Z)
          by (destruct fuel; cbn [obj_bsearch_idx]; [reflexivity|]; replace (l <? i) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
        do 19 (first [ ub1 | zstep ]; try udecide). release_frame FR ST2 (bv_unsigned sp). zstep.
        replace (bv_unsigned sp - 112 + 112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
        unfold bsearch_post, bsearch_res. finish.
    - assert (CN : 0 <= c) by (pose proof (sign_land64 c ltac:(lia)) as SL; lia). clear K1.
      replace (c <? 0) with false by (symmetry; apply Z.ltb_ge; lia).
      zstep. if_cases K3; zify_cond K3.
      + (* [comment removed for export] *)
        assert (C0 : c = 0) by (first [exact K3 | apply (proj1 (land64_zero c ltac:(lia))); exact K3]). clear K3.
        replace (0 <? c) with false by (symmetry; apply Z.ltb_ge; lia).
        do 17 (first [ ub1 | zstep ]; try udecide). release_frame FR ST2 (bv_unsigned sp). zstep.
        replace (bv_unsigned sp - 112 + 112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
        setreg 10%Z (Z_to_bv 64 (P_OBJ_OBJS_VA + 4 * i)) ltac:(f_equal; unfold P_OBJ_OBJS_VA; lia).
        unfold bsearch_post, bsearch_res, P_OBJ_OBJS_VA. finish.
      + (* [comment removed for export] *)
        assert (CP : 0 < c) by (pose proof (land64_zero c ltac:(lia)) as LZ; first [lia | exfalso; apply K3; lia]). clear K3.
        replace (0 <? c) with true by (symmetry; apply Z.ltb_lt; lia).
        do 5 (first [ ub1 | zstep ]; try udecide). if_cases K4; zify_cond K4.
        * rewrite signed_small in K4 by lia. rewrite signed_small in K4 by lia.
          eapply IH; try eassumption; try lia; subst i; Z.div_mod_to_equations; lia.
        * rewrite signed_small in K4 by lia. rewrite signed_small in K4 by lia.
          replace (obj_bsearch_idx fuel (zbytes kb) (i + 1) h) with (@None Z)
            by (destruct fuel; cbn [obj_bsearch_idx]; [reflexivity|]; replace (i + 1 <? h) with false by (symmetry; apply Z.ltb_ge; lia); reflexivity).
          do 19 (first [ ub1 | zstep ]; try udecide). release_frame FR ST2 (bv_unsigned sp). zstep.
          replace (bv_unsigned sp - 112 + 112) with (bv_unsigned sp) by lia. rewrite (Z_to_bv_bv_unsigned sp).
          unfold bsearch_post, bsearch_res. finish.
  Qed.
End BsearchLoop.

Lemma ossl_bsearch_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo KP KA KD knid : Z) (kb : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - OSSL_BSEARCH_STACK ->
  obj_table_ok m ->
  rw_cells ctusegs m KP [C8 (wz KA)] -> bv_unsigned sp <= KP -> KP mod 8 = 0 ->
  rw_cells ctusegs m (KA + 16) [C4 (wz knid); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] ->
  (bv_unsigned sp <= KA + 16 \/ KA + 32 <= lo) -> KA mod 8 = 0 -> 0 < KA -> Z.of_nat (length kb) < 2^31 ->
  bytes_at ctusegs m KD kb -> KD + Z.of_nat (length kb) <= lo ->
  a0 = wz KP -> a1 = wz P_OBJ_OBJS_VA -> a2 = wz NUM_OBJ -> a3 = wz 4 -> a4 = wz OBJ_CMP_FN -> a5 = wz 0 -> a6 = wz 0 ->
  evt ctusegs (bsearch_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc
                 (bsearch_res (obj_bsearch_idx OBJ_BSEARCH_FUEL (zbytes kb) 0 NUM_OBJ)) lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_BSEARCH) fc None m (seg_rom ctusegs)).
Proof.
  intros until kb. intros ST MI GLO LO TOK HKP KPS KP8 HKA KAS KA8 KA0 KL HKB KDL -> -> -> -> -> -> ->.
  unfold OSSL_BSEARCH, OSSL_BSEARCH_STACK, GLOBALS_TOP, NUM_OBJ, P_OBJ_OBJS_VA, OBJ_CMP_FN, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HKP) as KPB. pose proof (rw_cells_bound _ _ _ _ HKA) as KAB. cbn in KPB, KAB.
  pose proof (bytes_at_bound _ _ _ _ HKB) as KDB.
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 112%nat ST. do 26 (first [ ub1 | zstep ]; try udecide).
  setreg 25%Z (Z_to_bv 64 1) ltac:(first [ f_equal; vm_compute; reflexivity | apply bv_eq; vm_compute; reflexivity ]).
  replace (bv_unsigned sp + -112) with (bv_unsigned sp - 112) in * by lia.
  eapply (bsearch_loop ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc m lo KP KA KD knid kb
            ltac:(unfold GLOBALS_TOP; lia) ltac:(unfold OSSL_BSEARCH_STACK; lia) KPS KAS KL KDL KP8 KA8 KA0 OBJ_BSEARCH_FUEL 0 NUM_OBJ);
    try eassumption.
  all: rewrite ?OBJ_BSEARCH_FUEL_eq; unfold NUM_OBJ; cbn -[Z.pow]; try lia.
  eapply obj_table_ok_transport; [exact TOK| exact MU|]. constructor; [cbn; unfold GLOBALS_TOP; lia| constructor].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition OSSL_OBJ_OBJ2NID_STACK : Z := 64 + OSSL_BSEARCH_STACK.

Definition obj2nid_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (r : Z) (W : list (Z * Z)) (lo : Z) (m : word -> option byte) : machine_state -> Prop :=
  fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 r) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch W m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma obj_lookup_idx : forall key nid lnlen,
  obj_lookup key = Some (nid, lnlen) ->
  exists i, obj_bsearch_idx OBJ_BSEARCH_FUEL key 0 NUM_OBJ = Some i /\ fst (fst (tab_entry i)) = nid /\ snd (tab_entry i) = lnlen /\ 0 <= i < NUM_OBJ.
Proof.
  intros key nid lnlen. unfold obj_lookup. generalize OBJ_BSEARCH_FUEL as fu. intros fu H.   (* [comment removed for export] *)
  rewrite obj_bsearch_loop_idx in H.
  destruct (obj_bsearch_idx fu key 0 NUM_OBJ) as [i|] eqn:E; [|discriminate].
  injection H as H1 H2. exists i. split; [reflexivity|]. split; [exact H1|]. split; [exact H2|].
  exact (obj_bsearch_idx_range _ _ _ _ _ E).
Qed.

Lemma ossl_obj_obj2nid_hit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo KA KD : Z) (kb : list byte) (nid lnlen : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - OSSL_OBJ_OBJ2NID_STACK -> bv_unsigned sp mod 16 = 0 ->
  obj_table_ok m ->
  rw_cells ctusegs m (KA + 16) [C4 (wz 0); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] ->
  (bv_unsigned sp <= KA + 16 \/ KA + 32 <= lo) -> KA mod 8 = 0 -> 0 < KA -> 0 < Z.of_nat (length kb) < 2^31 ->
  bytes_at ctusegs m KD kb -> KD + Z.of_nat (length kb) <= lo ->
  obj_lookup (zbytes kb) = Some (nid, lnlen) ->
  a0 = wz KA ->
  evt ctusegs (obj2nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nid
                 [(bv_unsigned sp - OSSL_OBJ_OBJ2NID_STACK, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_OBJ_OBJ2NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until lnlen. intros ST MI GLO LO SPA TOK HKA KAS KAL KA0 KL HKB KDL LK ->.
  unfold OSSL_OBJ_OBJ2NID, OSSL_OBJ_OBJ2NID_STACK, OSSL_BSEARCH_STACK, GLOBALS_TOP, MallocRep.wz, obj2nid_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HKA) as KAB. cbn in KAB. pose proof (bytes_at_bound _ _ _ _ HKB) as KDB.
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  destruct (obj_lookup_idx _ _ _ LK) as (i & BI & NID & LNL & IR).
  carve_frame 64%nat ST. do 7 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?land_M64_small in K0 by lia; lia|]. clear K0.
  zstep. uchk.
  zstep. change (sx32 (Z_to_bv 64 0)) with (Z_to_bv 64 0).
  zstep. if_cases K1; zify_cond K1; [exfalso; apply K1; reflexivity|]. clear K1.
  zstep. setreg 10%Z (Z_to_bv 64 (Z.of_nat (length kb))) ltac:(symmetry; apply sx32_small; lia).
  zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit, ?land_M64_small in K2 by lia; lia|]. clear K2.
  do 10 zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 64)) = bv_unsigned sp - 64) by (apply unsigned_lit; lia).
  (* [comment removed for export] *)
  lazymatch type of FR with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (firstn 1%nat cs) with ?cs1 => lazymatch eval cbv in (skipn 1%nat cs) with ?cs2 => change cs with (cs1 ++ cs2) in FR end end end.
  apply rw_cells_app in FR. destruct FR as [FR1 FR2]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR2.
  lazymatch type of FR2 with rw_cells _ _ _ ?cs =>
    lazymatch eval cbv in (firstn 1%nat cs) with ?cs1 => lazymatch eval cbv in (skipn 1%nat cs) with ?cs2 => change cs with (cs1 ++ cs2) in FR2 end end end.
  apply rw_cells_app in FR2. destruct FR2 as [FK FR3]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ] in FR3.
  replace (bv_unsigned sp + -64 + 24) with (bv_unsigned sp - 40) in FK by lia.
  replace (bv_unsigned sp + -64 + 24 + 8) with (bv_unsigned sp + -32) in FR3 by lia.
  assert (TOK1 : obj_table_ok m1).
  { eapply obj_table_ok_transport; [exact TOK| exact MU|]. constructor; [cbn; unfold GLOBALS_TOP; lia| constructor]. }
  pose proof (munch_refl [(bv_unsigned sp - 192, bv_unsigned sp)]%Z m1) as MUm.
  eapply evt_cut.
  { eapply ossl_bsearch_spec with (lo := lo) (KP := bv_unsigned sp - 40) (KA := KA) (KD := KD) (knid := 0) (kb := kb);
      [ rewrite ESP; exact ST | exact MI | unfold GLOBALS_TOP; lia | rewrite ESP; unfold OSSL_BSEARCH_STACK; lia | exact TOK1
      | exact FK | rewrite ESP; lia | clear - SPA; Z.div_mod_to_equations; lia | exact HKA | rewrite ESP; lia | exact KAL | exact KA0 | lia | exact HKB | exact KDL
      | f_equal; lia | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity | reflexivity ]. }
  unfold bsearch_post, OSSL_BSEARCH_STACK. post_call_esp ESP m1. rewrite ?ESP in *.
  match goal with H : stk ctusegs _ lo _ |- _ => rename H into ST2 end.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m2 end.
  assert (TOK2 : obj_table_ok m2).
  { eapply obj_table_ok_transport; [exact TOK1| exact MUm|]. constructor; [cbn; unfold GLOBALS_TOP; lia| constructor]. }
  rewrite BI. unfold bsearch_res.
  destruct (TOK2 i IR) as (idx & ED & HE).
  pose proof HE as HE'. unfold obj_entry in HE'. destruct (tab_entry i) as [[enid content] elnlen] eqn:TE. cbn [fst snd] in NID, LNL. subst enid elnlen.
  destruct HE' as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ).
  unfold NUM_NID, NUM_OBJ, IMG_LO, P_OBJ_OBJS_VA, P_NID_OBJS_VA, MallocRep.wz in *.
  replace (262212 + 4 * i) with (4 * i + 262212) in RO1 by lia.
  zstep. if_cases K3; zify_cond K3; [exfalso; rewrite ?unsigned_lit, ?land_M64_small in K3 by lia; lia|]. clear K3.
  setreg 10%Z (Z_to_bv 64 (4 * i + 262212)) ltac:(f_equal; lia).
  zstep. uchk.
  zstep. rewrite (sx32_small idx) by lia.
  zstep. uchk.
  zstep. zstep. zstep. zstep. zstep. uchk.
  zstep. setreg 10%Z (Z_to_bv 64 (2898056 + 40 * idx)) ltac:(f_equal; lia).
  zstep. rewrite (sx32_small nid) by lia. zstep.
  zstep. do 5 zstep.
  (* [comment removed for export] *)
  lazymatch type of FR1 with rw_cells _ _ _ [CB 24 ?jk] =>
  assert (FR : rw_cells ctusegs m2 (bv_unsigned sp + -64) ([CB 24 jk] ++ [C8 (Z_to_bv 64 KA)] ++ [C8 s2; C8 s1; C8 s0; C8 ra])) end.
  { apply rw_cells_app. split; [exact FR1|]. cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ].
    apply rw_cells_app. split; [replace (bv_unsigned sp + -64 + 24) with (bv_unsigned sp - 40) by lia; eassumption|].
    cbn [cells_size csize Nat.add Z.of_nat Pos.of_succ_nat Pos.succ]. replace (bv_unsigned sp + -64 + 24 + 8) with (bv_unsigned sp + -32) by lia. eassumption. }
  cbn [app] in FR.
  release_frame FR ST2 (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma ossl_obj_obj2nid_nid_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo KA knid : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 64 ->
  ro_cells ctusegs m (KA + 16) [C4 (wz knid)] -> 0 < knid < 2^31 ->
  (bv_unsigned sp <= KA + 16 \/ KA + 20 <= lo) -> KA mod 8 = 0 -> 0 < KA ->
  a0 = wz KA ->
  evt ctusegs (obj2nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc knid
                 [(bv_unsigned sp - 64, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OSSL_OBJ_OBJ2NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until knid. intros ST MI GLO LO HKA KN KAS KAL KA0 ->.
  unfold OSSL_OBJ_OBJ2NID, GLOBALS_TOP, MallocRep.wz, obj2nid_post in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (ro_cells_bound _ _ _ _ HKA) as KAB. cbn in KAB.
  pose proof (munch_refl [(bv_unsigned sp - 64, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 64%nat ST. do 7 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?land_M64_small in K0 by lia; lia|]. clear K0.
  zstep. uchk.
  zstep. setreg 18%Z (Z_to_bv 64 knid) ltac:(symmetry; apply sx32_small; lia).
  zstep. if_cases K1; zify_cond K1; [| exfalso; rewrite ?unsigned_lit, ?land_M64_small in K1 by lia; lia]. clear K1.
  zstep. do 5 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma OBJ_obj2nid_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp) ->
              evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz OSSL_OBJ_OBJ2NID) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz OBJ_OBJ2NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO H.
  unfold OBJ_OBJ2NID, OSSL_OBJ_OBJ2NID, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OBJ_nid2obj_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo n : Z) (rest : list cell),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 80 -> 0 < n < NUM_NID ->
  ro_cells ctusegs m (P_NID_OBJS_VA + 40 * n + 16) (C4 (wz n) :: rest) ->
  a0 = wz n ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
      ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (P_NID_OBJS_VA + 40 * n)) a1' a2' a3' a4' a5' a6' a7'
                    s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
               F (ret_pc ra) fc None m' (seg_rom ctusegs)
      /\ munch [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
      /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OBJ_NID2OBJ) fc None m (seg_rom ctusegs)).
Proof.
  intros until rest. intros ST MI GLO LO Hn RO ->.
  unfold OBJ_NID2OBJ, NUM_NID, P_NID_OBJS_VA, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 80, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  assert (RO1 : ro_cells ctusegs m (2898056 + 40 * n + 16) [C4 (wz n)]).
  { destruct RO as [WF BA]. split; [cbn; tauto|]. cbn [cells_bytes] in BA |- *. rewrite app_nil_r. apply bytes_at_app in BA. exact (proj1 BA). }
  clear RO.
  carve_frame 80%nat ST. do 5 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?land_M64_small in K0 by lia; lia|]. clear K0.
  zstep. zstep. if_cases K1; zify_cond K1; [exfalso; rewrite ?unsigned_lit in K1 by lia; lia|]. clear K1.
  zstep. zstep. zstep. zstep. zstep. uchk.
  zstep. zstep. setreg 11%Z (Z_to_bv 64 (2898056 + 40 * n)) ltac:(f_equal; lia).
  zstep. setreg 11%Z (Z_to_bv 64 n) ltac:(symmetry; apply sx32_small; lia).
  zstep. if_cases K2; zify_cond K2; [exfalso; rewrite ?unsigned_lit, ?land_M64_small in K2 by lia; lia|]. clear K2.
  zstep. zstep. zstep. zstep. zstep. setreg 10%Z (Z_to_bv 64 (2898056 + 40 * n)) ltac:(f_equal; lia).
  zstep.
  do 4 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  finish.
Qed.

(* [comment removed for export] *)
Lemma static_obj_cells : forall m nid lnlen,
  mem_inv ctusegs m -> ap_img m -> static_obj_ok nid lnlen -> 0 < nid ->
  exists content ED,
    ro_cells ctusegs m (P_NID_OBJS_VA + 40 * nid + 16) [C4 (wz nid); C4 (wz (zlength content)); C8 (wz ED)]
    /\ ro_cells ctusegs m (P_NID_OBJS_VA + 40 * nid + 32) [C4 (wz 0)]
    /\ bytes_at ctusegs m ED (map (Z_to_bv 8) content) /\ Forall (fun c => 0 <= c < 256) content
    /\ 0 <= ED /\ ED + zlength content <= IMG_LO.
Proof.
  intros m nid lnlen MI IMG (i & content & Hi & TE & _) Hn.
  destruct (obj_table_ok_intro m MI IMG i Hi) as (idx & ED & HE). unfold obj_entry in HE. rewrite TE in HE.
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ). subst idx.
  exists content, ED. split; [exact RO2|]. split; [exact ROF|]. split; [exact HEB|]. split; [exact CR|]. split; [lia| exact EDL].
Qed.

(* [comment removed for export] *)
Lemma obj_bsearch_idx_hit : forall fuel key l h i, obj_bsearch_idx fuel key l h = Some i -> obj_cmp key (snd (fst (tab_entry i))) = 0.
Proof.
  induction fuel as [|fuel IH]; intros key l h i H; cbn [obj_bsearch_idx] in H; [discriminate|].
  destruct (l <? h); [|discriminate]. cbv zeta in H.
  destruct (Z.ltb_spec (obj_cmp key (snd (fst (tab_entry (l + (h - l) / 2))))) 0); [apply (IH _ _ _ _ H)|].
  destruct (Z.ltb_spec 0 (obj_cmp key (snd (fst (tab_entry (l + (h - l) / 2)))))); [apply (IH _ _ _ _ H)|].
  injection H as <-. lia.
Qed.
Lemma obj_cmp_zero_len : forall k c, obj_cmp k c = 0 -> zlength k = zlength c.
Proof. intros k c H. unfold obj_cmp in H. destruct (Z.eqb_spec (zlength k - zlength c) 0); lia. Qed.

Lemma obj_lookup_hit_facts : forall m kb nid lnlen,
  mem_inv ctusegs m -> ap_img m -> obj_lookup (zbytes kb) = Some (nid, lnlen) -> (0 < length kb)%nat ->
  0 < nid < NUM_NID /\ static_obj_ok nid lnlen.
Proof.
  intros m kb nid lnlen MI IMG LK KL. destruct (obj_lookup_idx _ _ _ LK) as (i & BI & NID & LNL & IR).
  pose proof (obj_bsearch_idx_hit _ _ _ _ _ BI) as HC. apply obj_cmp_zero_len in HC. rewrite zlength_zbytes in HC.
  destruct (obj_table_ok_intro m MI IMG i IR) as (idx & ED & HE). unfold obj_entry in HE.
  destruct (tab_entry i) as [[enid content] elnlen] eqn:TE. cbn [fst snd] in NID, LNL, HC. subst enid elnlen.
  destruct HE as (IDX & ED0 & EDL & NIDR & RO1 & RO2 & HEB & CR & INID & ROF & NZ). subst idx.
  split; [split; [apply NZ; lia| lia]|]. exists i, content. split; [exact IR|]. split; [exact TE|].
  intros E0. subst content. unfold zlength in HC. cbn in HC. lia.
Qed.

(* [comment removed for export] *)
Definition OBJ_OBJ2NID_STACK : Z := 16 + OSSL_OBJ_OBJ2NID_STACK.
Lemma OBJ_obj2nid_hit_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : word -> option byte) (lo KA KD : Z) (kb : list byte) (nid lnlen : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - OBJ_OBJ2NID_STACK -> bv_unsigned sp mod 16 = 0 ->
  obj_table_ok m ->
  rw_cells ctusegs m (KA + 16) [C4 (wz 0); C4 (wz (Z.of_nat (length kb))); C8 (wz KD)] ->
  (bv_unsigned sp <= KA + 16 \/ KA + 32 <= lo) -> KA mod 8 = 0 -> 0 < KA -> 0 < Z.of_nat (length kb) < 2^31 ->
  bytes_at ctusegs m KD kb -> KD + Z.of_nat (length kb) <= lo ->
  obj_lookup (zbytes kb) = Some (nid, lnlen) ->
  a0 = wz KA ->
  evt ctusegs (obj2nid_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc nid
                 [(bv_unsigned sp - OBJ_OBJ2NID_STACK, bv_unsigned sp)]%Z lo m)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (Z_to_bv 64 OBJ_OBJ2NID) fc None m (seg_rom ctusegs)).
Proof.
  intros until lnlen. intros ST MI GLO LO SPA TOK HKA KAS KAL KA0 KL HKB KDL LK HA0.
  unfold OBJ_OBJ2NID_STACK, OSSL_OBJ_OBJ2NID_STACK, OSSL_BSEARCH_STACK, GLOBALS_TOP in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (rw_cells_bound _ _ _ _ HKA) as KAB. cbn in KAB. pose proof (bytes_at_bound _ _ _ _ HKB) as KDB.
  apply (OBJ_obj2nid_fwd _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo ST MI ltac:(unfold GLOBALS_TOP; lia) ltac:(lia)).
  intros m1 MU1 WM1 MI1 ST1.
  eapply evt_mono.
  { eapply ossl_obj_obj2nid_hit_spec with (lo := lo) (KA := KA) (KD := KD) (kb := kb);
      [ exact ST1 | exact MI1 | unfold GLOBALS_TOP; lia | unfold OSSL_OBJ_OBJ2NID_STACK, OSSL_BSEARCH_STACK; lia | exact SPA
      | eapply obj_table_ok_transport; [exact TOK| exact MU1| constructor; [cbn; unfold GLOBALS_TOP; lia| constructor]]
      | eapply rw_cells_transport; [exact HKA| exact MU1| exact WM1| cbn; lia]
      | exact KAS | exact KAL | exact KA0 | exact KL
      | eapply bytes_at_transport; [exact HKB| exact MU1| cbn; lia]
      | exact KDL | exact LK | exact HA0 ]. }
  unfold obj2nid_post, OSSL_OBJ_OBJ2NID_STACK, OSSL_BSEARCH_STACK. intros ms' PO.
  destruct PO as (x0 & x1 & x2 & x3 & x4 & x5 & x6 & x7 & x8 & x9 & x10 & x11 & x12 & x13 & m' & -> & MU2 & WM2 & MI2 & ST2).
  do 15 eexists. split; [reflexivity|].
  split. { eapply munch_trans; (eapply munch_weaken; [| eassumption]); unfold sub_fp; cbn [outside]; intros; lia. }
  split; [eapply wmono_trans; [exact WM1| exact WM2]|]. split; [exact MI2| exact ST2].
Qed.
End WithCeiling0.
