(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool Permutation.
From Stdlib Require Import Uint63.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Mem Cells Step Arr.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prog ApState ApOwner.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common Require Import FastWord FastWordSem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Common.Ax Require Import ExTrie.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxRegs HxVal HxBytes HxMem HxMemSound HxQuery.
From OssFuzzTheorems.Proofs.openssl.ct.lib.HX Require Import HxImg.
From OssFuzzTheorems.Proofs.openssl.ct.lib.ApHX Require Import HxFacts HxImgRom.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts HxpImage HxpFinal.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
#[local] Arguments Uint63Axioms.to_Z : simpl never.
#[local] Arguments Uint63Axioms.of_Z : simpl never.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition RG3 : region := Eval cbv in (nth 0 FIN_LIT no_region).
Definition RG4 : region := Eval cbv in (nth 1 FIN_LIT no_region).
Definition RG5 : region := Eval cbv in (nth 2 FIN_LIT no_region).
Definition RG7 : region := Eval cbv in (nth 3 FIN_LIT no_region).
Definition RG8 : region := Eval cbv in (nth 4 FIN_LIT no_region).
Definition RG10 : region := Eval cbv in (nth 5 FIN_LIT no_region).
Definition RG11 : region := Eval cbv in (nth 6 FIN_LIT no_region).
Definition RG13 : region := Eval cbv in (nth 7 FIN_LIT no_region).
Lemma FIN_LIT_eq : FIN_LIT = [RG3; RG4; RG5; RG7; RG8; RG10; RG11; RG13]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
Definition BK_MK : region := Eval cbv in (nth 0 FIN_BLK no_region).
Definition BK_SA : region := Eval cbv in (nth 1 FIN_BLK no_region).
Definition BK_ND : region := Eval cbv in (nth 2 FIN_BLK no_region).
Definition BK_ES : region := Eval cbv in (nth 3 FIN_BLK no_region).
Definition BK_OL : region := Eval cbv in (nth 4 FIN_BLK no_region).
Definition BK_1 : region := Eval cbv in (nth 5 FIN_BLK no_region).
Definition BK_5 : region := Eval cbv in (nth 6 FIN_BLK no_region).
Definition BK_1543 : region := Eval cbv in (nth 7 FIN_BLK no_region).
Definition BK_XL : region := Eval cbv in (nth 8 FIN_BLK no_region).
Definition BK_1627 : region := Eval cbv in (nth 9 FIN_BLK no_region).
Lemma FIN_BLK_eq : FIN_BLK = [BK_MK; BK_SA; BK_ND; BK_ES; BK_OL; BK_1; BK_5; BK_1543; BK_XL; BK_1627]. Proof. reflexivity. Qed.
Lemma TAGS_BLKi_eq : TAGS_BLKi = [T K_MK; T K_SA; T K_ND; T K_ES; T K_OL; T 1; T 5; T 1543; T K_XL; T 1627]. Proof. reflexivity. Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Inductive citem : Type := IZ8 (z : Z) | IZ4 (z : Z) | IZ1 (z : Z) | IP (k : Z) | IB (zs : list Z).

Fixpoint kbs_items (l : list citem) : list kb :=
  match l with
  | [] => []
  | IZ8 z :: l' => kbs_Z 8 z ++ kbs_items l'
  | IZ4 z :: l' => kbs_Z 4 z ++ kbs_items l'
  | IZ1 z :: l' => kbs_Z 1 z ++ kbs_items l'
  | IP k :: l' => kbs_ptr (T k) ++ kbs_items l'
  | IB zs :: l' => kbs_bytes zs ++ kbs_items l'
  end.

Fixpoint cells_items (rho : valuation) (l : list citem) : list Cells.cell :=
  match l with
  | [] => []
  | IZ8 z :: l' => C8 (wz z) :: cells_items rho l'
  | IZ4 z :: l' => C4 (wz z) :: cells_items rho l'
  | IZ1 z :: l' => C1 (Z_to_bv 8 z) :: cells_items rho l'
  | IP k :: l' => C8 (wz (rho (T k))) :: cells_items rho l'
  | IB zs :: l' => CB (length zs) (map (Z_to_bv 8) zs) :: cells_items rho l'
  end.

Fixpoint items_ok (rho : valuation) (l : list citem) : Prop :=
  match l with
  | [] => True
  | IZ8 z :: l' => 0 <= z < 2 ^ 64 /\ items_ok rho l'
  | IZ4 z :: l' => 0 <= z < 2 ^ 64 /\ items_ok rho l'
  | IZ1 z :: l' => 0 <= z /\ items_ok rho l'
  | IP k :: l' => 0 < rho (T k) < 2 ^ 63 /\ items_ok rho l'
  | IB zs :: l' => items_ok rho l'
  end.

Lemma items_bytes (rho : valuation) : forall (l : list citem) (bs : list byte),
  items_ok rho l -> Forall2 (kb_ok rho) (kbs_items l) bs -> bs = cells_bytes (cells_items rho l).
Proof.
  induction l as [|[z|z|z|k|zs] l IH]; intros bs Hok H; cbn [kbs_items cells_items items_ok] in *.
  - exact (F2_nil rho bs H).
  - destruct Hok as [Hz Hok]. exact (F2_lit8 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_lit4 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_lit1 rho z _ _ bs Hz (fun bs' H' => IH bs' Hok H') H).
  - destruct Hok as [Hz Hok]. exact (F2_ptr rho (T k) _ _ bs ltac:(lia) ltac:(lia) (fun bs' H' => IH bs' Hok H') H).
  - exact (F2_bytes rho zs _ _ bs (fun bs' H' => IH bs' Hok H') H).
Qed.

Lemma items_wf (rho : valuation) : forall l, cells_wf (cells_items rho l).
Proof. induction l as [|[z|z|z|k|zs] l IH]; cbn; auto. split; [apply length_map | exact IH]. Qed.

Section WithSegs.
Let segs := ctusegs.

(* [comment removed for export] *)
Lemma cells_of_export (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (l : list citem) :
  region_export segs m rho B rg -> 0 <= B -> B + to_Z (rg_size rg) <= 2 ^ 64 -> 0 <= off -> off + Z.of_nat (cells_size (cells_items rho l)) <= to_Z (rg_size rg) ->
  kbs_of segs rg off (cells_size (cells_items rho l)) = kbs_items l -> items_ok rho l ->
  ro_cells segs m (B + off) (cells_items rho l).
Proof.
  intros HE HB Ht Ho Hf Ek Hok. unfold ro_cells.
  exact (export_cells segs m rho B rg off (cells_items rho l) (kbs_items l) HE HB Ho Hf Ht (items_wf rho l) Ek (fun bs H => items_bytes rho l bs Hok H)).
Qed.

Lemma rw_cells_of_export (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (l : list citem) :
  region_export segs m rho B rg -> rg_wr rg = true -> 0 <= B -> B + to_Z (rg_size rg) <= 2 ^ 64 -> 0 <= off -> off + Z.of_nat (cells_size (cells_items rho l)) <= to_Z (rg_size rg) ->
  kbs_of segs rg off (cells_size (cells_items rho l)) = kbs_items l -> items_ok rho l ->
  rw_cells segs m (B + off) (cells_items rho l).
Proof.
  intros HE Hw HB Ht Ho Hf Ek Hok. unfold rw_cells.
  exact (export_cells_rw segs m rho B rg off (cells_items rho l) (kbs_items l) HE Hw HB Ho Hf Ht (items_wf rho l) Ek (fun bs H => items_bytes rho l bs Hok H)).
Qed.

(* [comment removed for export] *)
Lemma bytes_of_Z (bs : list byte) (zs : list Z) : map bv_unsigned bs = zs -> bs = map (Z_to_bv 8) zs.
Proof.
  revert zs. induction bs as [|b bs IH]; intros [|z zs] H; cbn in H; try discriminate; [reflexivity|].
  injection H as H1 H2. cbn [map]. f_equal; [|exact (IH zs H2)]. apply bv_eq. rewrite Z_to_bv_unsigned, <- H1. symmetry. apply bv_wrap_small. apply bv_unsigned_in_range.
Qed.

(* [comment removed for export] *)
Lemma u32arr_of_export (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (ws : list word) (zs : list Z) :
  region_export segs m rho B rg -> rg_wr rg = true -> 0 <= B -> B + to_Z (rg_size rg) <= 2 ^ 64 -> 0 <= off -> off + Z.of_nat (length zs) <= to_Z (rg_size rg) ->
  kbs_of segs rg off (length zs) = kbs_bytes zs -> map bv_unsigned (u32s ws) = zs ->
  u32arr segs m (B + off) ws.
Proof.
  intros HE Hw HB Ht Ho Hf Ek Ews0. pose proof (bytes_of_Z _ _ Ews0) as Ews. pose proof (export_run segs m rho B rg off zs HE HB Ho Hf Ht Ek) as Hb. rewrite <- Ews in Hb.
  split; [exact Hb|]. pose proof (f_equal (@length byte) Ews) as L. rewrite u32s_length, length_map in L.
  replace (4 * Z.of_nat (length ws)) with (Z.of_nat (length zs)) by lia. exact (export_wr segs m rho B rg off _ HE Hw HB Ho (Nat2Z.is_nonneg _) Hf Ht).
Qed.

Lemma u64arr_of_export (m : word -> option byte) (rho : valuation) (B : Z) (rg : region) (off : Z) (ws : list word) (zs : list Z) :
  region_export segs m rho B rg -> rg_wr rg = true -> 0 <= B -> B + to_Z (rg_size rg) <= 2 ^ 64 -> 0 <= off -> off + Z.of_nat (length zs) <= to_Z (rg_size rg) ->
  kbs_of segs rg off (length zs) = kbs_bytes zs -> map bv_unsigned (u64s ws) = zs ->
  u64arr segs m (B + off) ws.
Proof.
  intros HE Hw HB Ht Ho Hf Ek Ews0. pose proof (bytes_of_Z _ _ Ews0) as Ews. pose proof (export_run segs m rho B rg off zs HE HB Ho Hf Ht Ek) as Hb. rewrite <- Ews in Hb.
  split; [exact Hb|]. pose proof (f_equal (@length byte) Ews) as L. rewrite u64s_length, length_map in L.
  replace (8 * Z.of_nat (length ws)) with (Z.of_nat (length zs)) by lia. exact (export_wr segs m rho B rg off _ HE Hw HB Ho (Nat2Z.is_nonneg _) Hf Ht).
Qed.

Lemma Forall2_cons_inv {A B : Type} (R : A -> B -> Prop) (a : A) (b : B) (l : list A) (l' : list B) :
  Forall2 R (a :: l) (b :: l') -> R a b /\ Forall2 R l l'.
Proof. intros H. inversion H. auto. Qed.

(* [comment removed for export] *)
Lemma RG5_facts : to_Z (rg_size RG5) = ltac:(let v := eval cbv in (to_Z (rg_size RG5)) in exact v) /\ rg_wr RG5 = false. Proof. split; reflexivity. Qed.
Lemma RG7_facts : to_Z (rg_size RG7) = ltac:(let v := eval cbv in (to_Z (rg_size RG7)) in exact v) /\ rg_wr RG7 = true. Proof. split; reflexivity. Qed.
Lemma RG8_facts : to_Z (rg_size RG8) = ltac:(let v := eval cbv in (to_Z (rg_size RG8)) in exact v) /\ rg_wr RG8 = true. Proof. split; reflexivity. Qed.
Lemma RG10_facts : to_Z (rg_size RG10) = ltac:(let v := eval cbv in (to_Z (rg_size RG10)) in exact v) /\ rg_wr RG10 = true. Proof. split; reflexivity. Qed.
Lemma RG11_facts : to_Z (rg_size RG11) = ltac:(let v := eval cbv in (to_Z (rg_size RG11)) in exact v) /\ rg_wr RG11 = true. Proof. split; reflexivity. Qed.
Lemma RG13_facts : to_Z (rg_size RG13) = ltac:(let v := eval cbv in (to_Z (rg_size RG13)) in exact v) /\ rg_wr RG13 = true. Proof. split; reflexivity. Qed.
Lemma BK_MK_facts : to_Z (rg_size BK_MK) = 72 /\ rg_wr BK_MK = true. Proof. split; reflexivity. Qed.
Lemma BK_SA_facts : to_Z (rg_size BK_SA) = 32 /\ rg_wr BK_SA = true. Proof. split; reflexivity. Qed.
Lemma BK_ND_facts : to_Z (rg_size BK_ND) = 128 /\ rg_wr BK_ND = true. Proof. split; reflexivity. Qed.
Lemma BK_ES_facts : to_Z (rg_size BK_ES) = 904 /\ rg_wr BK_ES = true. Proof. split; reflexivity. Qed.
Lemma BK_XL_facts : to_Z (rg_size BK_XL) = 40 /\ rg_wr BK_XL = true. Proof. split; reflexivity. Qed.

(* [comment removed for export] *)
Lemma ro_cells_addr (m : word -> option byte) (A B off : Z) (cs : list Cells.cell) : A = B + off -> ro_cells segs m (B + off) cs -> ro_cells segs m A cs.
Proof. intros -> H. exact H. Qed.
Lemma rw_cells_addr (m : word -> option byte) (A B off : Z) (cs : list Cells.cell) : A = B + off -> rw_cells segs m (B + off) cs -> rw_cells segs m A cs.
Proof. intros -> H. exact H. Qed.
Lemma rw_ro (m : word -> option byte) (A : Z) (cs : list Cells.cell) : rw_cells segs m A cs -> ro_cells segs m A cs.
Proof. intros [H _]. exact H. Qed.
Lemma u32arr_addr (m : word -> option byte) (A B off : Z) ws : A = B + off -> u32arr segs m (B + off) ws -> u32arr segs m A ws.
Proof. intros -> H. exact H. Qed.
Lemma u64arr_addr (m : word -> option byte) (A B off : Z) ws : A = B + off -> u64arr segs m (B + off) ws -> u64arr segs m A ws.
Proof. intros -> H. exact H. Qed.

(* [comment removed for export] *)
Ltac lit_B HE := lazymatch type of HE with region_export _ _ _ ?B _ => eval cbv in B end.
Ltac LITrw HE FACTS l :=
  let B := lit_B HE in
  let off := lazymatch goal with |- rw_cells _ _ ?A _ => eval cbv in (A - B) end in
  apply (rw_cells_addr _ _ B off); [cbv; reflexivity|];
  apply (rw_cells_of_export _ _ B _ off l HE (proj2 FACTS)); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | cbn [items_ok]; repeat split; try exact I; first [lia | cbv; easy] ].
Ltac LITro HE FACTS l :=
  let B := lit_B HE in
  let off := lazymatch goal with |- ro_cells _ _ ?A _ => eval cbv in (A - B) end in
  apply (ro_cells_addr _ _ B off); [cbv; reflexivity|];
  apply (cells_of_export _ _ B _ off l HE); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | cbn [items_ok]; repeat split; try exact I; first [lia | cbv; easy] ].
(* [comment removed for export] *)
Ltac BLKrw HE FACTS B off l :=
  apply (rw_cells_addr _ _ B off); [first [reflexivity | lia] |];
  apply (rw_cells_of_export _ _ B _ off l HE (proj2 FACTS)); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | cbn [items_ok]; repeat split; try exact I; first [lia | cbv; easy] ].
Ltac BLKro HE FACTS B off l :=
  apply (ro_cells_addr _ _ B off); [first [reflexivity | lia] |];
  apply (cells_of_export _ _ B _ off l HE); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | cbn [items_ok]; repeat split; try exact I; first [lia | cbv; easy] ].
Ltac ESu32 HE FACTS B off n :=
  apply (u32arr_addr _ _ B off); [first [reflexivity | lia] |];
  apply (u32arr_of_export _ _ B _ off _ (repeat n 64) HE (proj2 FACTS)); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].
Ltac ESu64 HE FACTS B off :=
  apply (u64arr_addr _ _ B off); [first [reflexivity | lia] |];
  apply (u64arr_of_export _ _ B _ off _ (repeat 0 128) HE (proj2 FACTS)); [lia | rewrite (proj1 FACTS); lia | lia | rewrite (proj1 FACTS); cbn; lia | vm_compute; reflexivity | vm_compute; reflexivity].

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)

Theorem linv_init : forall (m : word -> option byte) (OW : list block), ap_init_facts m OW -> ap_lib_inv ap_ls0 m OW.
Proof.
  intros m OW (rho & HL & HB & Hnd & HndOW & Hexit).
  rewrite FIN_LIT_eq in HL. rewrite FIN_BLK_eq, TAGS_BLKi_eq in HB.
  pose proof (Forall_inv HL) as E3. apply Forall_inv_tail in HL. pose proof (Forall_inv HL) as E4. apply Forall_inv_tail in HL.
  pose proof (Forall_inv HL) as E5. apply Forall_inv_tail in HL. pose proof (Forall_inv HL) as E7. apply Forall_inv_tail in HL.
  pose proof (Forall_inv HL) as E8. apply Forall_inv_tail in HL. pose proof (Forall_inv HL) as E10. apply Forall_inv_tail in HL.
  pose proof (Forall_inv HL) as E11. apply Forall_inv_tail in HL. pose proof (Forall_inv HL) as E13. clear HL.
  cbn [lit_base RG3 RG4 RG5 RG7 RG8 RG10 RG11 RG13 rg_abs] in E3, E4, E5, E7, E8, E10, E11, E13.
  apply Forall2_cons_inv in HB as [(XMK & (pMK & IMK) & AMK1 & AMK2 & AMK3) HB].
  apply Forall2_cons_inv in HB as [(XSA & (pSA & ISA) & ASA1 & ASA2 & ASA3) HB].
  apply Forall2_cons_inv in HB as [(XND & (pND & IND) & AND1 & AND2 & AND3) HB].
  apply Forall2_cons_inv in HB as [(XES & (pES & IES) & AES1 & AES2 & AES3) HB].
  apply Forall2_cons_inv in HB as [(XOL & (pOL & IOL) & AOL1 & AOL2 & AOL3) HB].
  apply Forall2_cons_inv in HB as [_ HB]. apply Forall2_cons_inv in HB as [_ HB]. apply Forall2_cons_inv in HB as [_ HB].
  apply Forall2_cons_inv in HB as [(XXL & (pXL & IXL) & AXL1 & AXL2 & AXL3) HB]. clear HB.
  cbn [rg_size BK_MK BK_SA BK_ND BK_ES BK_XL BK_OL] in IMK, ISA, IND, IES, IXL, IOL, AMK2, ASA2, AND2, AES2, AXL2, AOL2.
  exists (mkE 0 (rho (T K_ES)) (rho (T K_MK)) (rho (T K_SA)) (rho (T K_ND)) (rho (T K_XL)) pES pES pMK pSA pND pXL CnfInit).   (* [comment removed for export] *)
  split; [exact (proj1 ap_linv_init)|]. split; [reflexivity|].
  exists 0.
  change (to_Z 128%uint63) with 128 in *. change (to_Z 72%uint63) with 72 in *. change (to_Z 32%uint63) with 32 in *.
  change (to_Z 904%uint63) with 904 in *. change (to_Z 40%uint63) with 40 in *.
  assert (P_ES : 0 < rho (T K_ES) < 2 ^ 63) by lia.
  assert (P_MK : 0 < rho (T K_MK) < 2 ^ 63) by lia. assert (P_SA : 0 < rho (T K_SA) < 2 ^ 63) by lia.
  assert (P_ND : 0 < rho (T K_ND) < 2 ^ 63) by lia. assert (P_XL : 0 < rho (T K_XL) < 2 ^ 63) by lia. assert (P_OL : 0 < rho (T K_OL) < 2 ^ 63) by lia.
  unfold ap_state. split.
  { (* [comment removed for export] *)
    unfold ap_env_ok, env_blocks. cbn [e_bio e_es e_mk e_sa e_nd e_xl p_bio p_es p_mk p_sa p_nd p_xl blk_addr blk_size fst snd].
    split; [repeat constructor; assumption|]. split; [exact HndOW|].
    pose proof (proj1 BK_ES_facts) as S2. pose proof (proj1 BK_MK_facts) as S3.
    pose proof (proj1 BK_SA_facts) as S4. pose proof (proj1 BK_ND_facts) as S5. pose proof (proj1 BK_XL_facts) as S6.
    unfold BIO_SIZE, ES_SIZE, MUTEX_SIZE. repeat constructor; cbn [blk_addr blk_size fst snd]; lia. }
  split.
  { (* [comment removed for export] *)
    intros a Ha. unfold IMG_LO, IMG_HI in Ha. let B4 := lit_B E4 in destruct (Z_lt_le_dec a B4) as [L|L].
    - apply (dimage_export_rom segs rho m _ _ _ _ 2%nat _ _ seg2 (chunk_of seg2) E3 (eq_refl : nth_error ctusegs 2 = Some seg2) seg2_chunk seg2_rd);
        [vm_compute; reflexivity | intros a' Ha'; apply find_seg2_in; revert Ha'; vm_compute (to_Z _); lia | apply Z.leb_le; vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | revert Ha L; vm_compute (to_Z _); lia].
    - apply (dimage_export_rom segs rho m _ _ _ _ 2%nat _ _ seg2 (chunk_of seg2) E4 (eq_refl : nth_error ctusegs 2 = Some seg2) seg2_chunk seg2_rd);
        [vm_compute; reflexivity | intros a' Ha'; apply find_seg2_in; revert Ha'; vm_compute (to_Z _); lia | apply Z.leb_le; vm_compute; reflexivity
        | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | vm_compute; reflexivity | revert Ha L; vm_compute (to_Z _); lia]. }
  split.
  { (* [comment removed for export] *)
    unfold ap_statics_fixed, crypto_statics, realloc_statics. cbn [e_bio e_xl e_mk].
    split. { split. { LITro E5 RG5_facts constr:([IZ8 CRYPTO_MALLOC]). }
             split. { LITro E5 RG5_facts constr:([IZ8 CRYPTO_FREE]). }
             split. { apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 MEMSET]). }
             split. { apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 CRYPTO_MALLOC]). }
             split. { apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 CRYPTO_FREE]). }
             apply rw_ro. LITrw E8 RG8_facts constr:([IZ1 1]). }
    split. { split. { LITro E5 RG5_facts constr:([IZ8 CRYPTO_REALLOC]). }
             apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 CRYPTO_REALLOC]). }
    split. { exact I. }   (* [comment removed for export] *)
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 1; IZ4 2]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 K_MASTER_KEY]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ1 1]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 V_DC_KEY]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 2; IZ4 1]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 2; IZ4 1]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IP K_XL]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ8 0]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 0]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ1 0]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 2; IZ4 1]). }
    split. { apply rw_ro. LITrw E8 RG8_facts constr:([IZ4 V_IN_INIT_KEY]). }
    split. { exists (wz (rho (T K_OL))). apply rw_ro. LITrw E8 RG8_facts constr:([IP K_OL]). }
    split. { apply rw_ro. LITrw E11 RG11_facts constr:([IZ8 TSD_MAIN]). }
    split. { apply rw_ro. LITrw E13 RG13_facts constr:([IZ8 0]). }
    split. { apply rw_ro. LITrw E13 RG13_facts constr:([IP K_MK]). }
    split. { LITrw E10 RG10_facts constr:([IZ1 1]). }
    (* [comment removed for export] *)
    split. { apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 DEF_CREATE; IZ8 DEF_INIT_DEFAULT; IZ8 DEF_DESTROY]). }
    split. { apply rw_ro. LITrw E7 RG7_facts constr:([IZ8 DEF_LOAD]). }
    split. { exists (wz 0). LITrw E11 RG11_facts constr:([IZ8 0]). }
    split. { exists (Z_to_bv 8 V_OI_BASE_INITED). LITrw E8 RG8_facts constr:([IZ1 V_OI_BASE_INITED]). }
    split. { LITrw E8 RG8_facts constr:([IZ1 V_OI_DO_CLEANUP]). }
    (* [comment removed for export] *)
    unfold SCT_FREE_GOT. LITro E5 RG5_facts constr:([IZ8 SCT_FREE_VA]). }
  split.
  { (* [comment removed for export] *)
    cbn [as_cnf st_of_ls ap_ls0 ls_cnf e_stage stage_once stage_tsd]. unfold ap_statics_cnf. cbn [stage_once stage_tsd].
    split. { LITrw E8 RG8_facts constr:([IZ4 0; IZ4 0]). }
    split. { LITrw E8 RG8_facts constr:([IZ8 V_OI_OPTSDONE]). }
    split. { LITrw E8 RG8_facts constr:([IZ4 0; IZ4 0]). }
    split. { LITrw E8 RG8_facts constr:([IZ8 0; IZ8 0]). }
    split. { LITrw E8 RG8_facts constr:([IZ1 0]). }
    LITrw E13 RG13_facts constr:([IZ8 0]). }
  split.
  { (* [comment removed for export] *)
    unfold tl_chain. cbn [e_mk e_sa e_nd e_es]. unfold OFF_MK_SA.
    split. { apply rw_ro. BLKrw XMK BK_MK_facts (rho (T K_MK)) 24 constr:([IP K_SA]). }
    split. { exists (map (Z_to_bv 8) [0; 0; 0; 0]). apply rw_ro. unfold sa_cells. BLKrw XSA BK_SA_facts (rho (T K_SA)) 0 [IZ4 1; IB [0; 0; 0; 0]; IZ8 0; IZ8 1; IP K_ND]. }
    apply rw_ro. BLKrw XND BK_ND_facts (rho (T K_ND)) 0 constr:([IP K_ES]). }
  split.
  { (* [comment removed for export] *)
    unfold exlock_free, mutex_free_cells, zeros4. cbn [e_xl repeat].
    BLKrw XXL BK_XL_facts (rho (T K_XL)) 0 constr:([IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0; IZ4 0]). }
  split. { exact I. }   (* [comment removed for export] *)
  (* [comment removed for export] *)
  unfold err_rep. split; [repeat split; reflexivity|].
  split.
  { unfold es_at. cbn [e_es st_of_ls ap_ls0 ls_data ls_cnf as_marks as_buf as_data as_dflags as_file as_line as_func as_top as_bottom wl map repeat optr osize Z.of_nat].
    unfold ESO_FLAGS, ESO_MARKS, ESO_BUFFER, ESO_DATA, ESO_DSIZE, ESO_DFLAGS, ESO_FILE, ESO_LINE, ESO_FUNC, ESO_TOP, ERR_NUM. cbn [repeat].
    split. { ESu32 XES BK_ES_facts (rho (T K_ES)) 0 0. }
    split. { ESu32 XES BK_ES_facts (rho (T K_ES)) 64 0. }
    split. { ESu64 XES BK_ES_facts (rho (T K_ES)) 128. }
    split. { ESu64 XES BK_ES_facts (rho (T K_ES)) 256. }
    split. { ESu64 XES BK_ES_facts (rho (T K_ES)) 384. }
    split. { ESu32 XES BK_ES_facts (rho (T K_ES)) 512 0. }
    split. { ESu64 XES BK_ES_facts (rho (T K_ES)) 576. }
    split. { ESu32 XES BK_ES_facts (rho (T K_ES)) 704 255. }
    split. { ESu64 XES BK_ES_facts (rho (T K_ES)) 768. }
    BLKrw XES BK_ES_facts (rho (T K_ES)) 896 constr:([IZ4 0; IZ4 0]). }
  cbn [as_file as_func as_data st_of_ls ap_ls0 ls_data repeat ERR_NUM]. repeat split; repeat constructor.
Qed.

End WithSegs.
