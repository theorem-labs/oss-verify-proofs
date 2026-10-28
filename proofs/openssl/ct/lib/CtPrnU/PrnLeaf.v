(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem Bytes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim STree Malloc Monad Prog LibProg ProgG PrintfModel PrintfModelX ApFmt ApObjTab ApObj CtSizes CtTime.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_pieces Printf_piecesx Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf Printf_sn.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac ApObjRep W_obj_lookup W_asn1_string W_snprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Definition GENTIME_NEW : Z := 0x11528c.
Definition GENTIME_FREE : Z := 0x1152b0.
Definition GET0_DATA : Z := 0xfe4ec.
Definition OBJ_NID2LN : Z := 0xfb4c8.
Definition A_C18 : Z := 0x14afc.      (* [comment removed for export] *)
Definition LN_794 : Z := 0x182f2.     (* [comment removed for export] *)
Definition LN_668 : Z := 0x24ff5.     (* [comment removed for export] *)
Definition LNS_794 : list Z := [101; 99; 100; 115; 97; 45; 119; 105; 116; 104; 45; 83; 72; 65; 50; 53; 54].
Definition SLK_794 : list Z := [105; 100; 45; 71; 111; 115; 116].
Definition LNS_668 : list Z := [115; 104; 97; 50; 53; 54; 87; 105; 116; 104; 82; 83; 65; 69; 110; 99; 114; 121; 112; 116; 105; 111; 110].
Definition SLK_668 : list Z := [82; 83; 65; 45; 83; 72; 65].
(* [comment removed for export] *)
Definition ln_addr (nid : Z) : Z := if nid =? NID_ecdsa_with_SHA256 then LN_794 else LN_668.
Definition ln_str (nid : Z) : list Z := if nid =? NID_ecdsa_with_SHA256 then LNS_794 else LNS_668.
Definition ln_slk (nid : Z) : list Z := if nid =? NID_ecdsa_with_SHA256 then SLK_794 else SLK_668.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac rom_lit A :=
  intros m MI;
  lazymatch goal with |- bytes_at _ _ _ ?bs =>
    let bs' := eval cbv in bs in
    change bs with bs';
    apply (ro_cells_bytes m A (length bs') bs');
    apply (ro_cells_image ctusegs m A bs' MI); [vm_compute; reflexivity| unfold A; lia| unfold A; cbn; lia]
  end.

Lemma fmt_C18_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m A_C18 (zb FMT_C18). Proof. rom_lit A_C18. Qed.
Lemma ln_794_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m LN_794 (zb LNS_794 ++ Z_to_bv 8 0 :: zb SLK_794). Proof. rom_lit LN_794. Qed.
Lemma ln_668_at : forall m, mem_inv ctusegs m -> bytes_at ctusegs m LN_668 (zb LNS_668 ++ Z_to_bv 8 0 :: zb SLK_668). Proof. rom_lit LN_668. Qed.

Lemma ln_at : forall m nid, mem_inv ctusegs m -> nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  bytes_at ctusegs m (ln_addr nid) (zb (ln_str nid) ++ Z_to_bv 8 0 :: zb (ln_slk nid))
  /\ Forall (fun c => 0 < c < 256) (ln_str nid) /\ length (zb (ln_slk nid)) = 7%nat /\ zlength (ln_str nid) <= 23
  /\ 65536 <= ln_addr nid /\ ln_addr nid + zlength (ln_str nid) + 8 <= STATIC_SPLIT.
Proof.
  intros m nid MI Hn. unfold ln_addr, ln_str, ln_slk, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption, LN_794, LN_668, STATIC_SPLIT in *.
  destruct Hn as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - split; [apply ln_794_at; exact MI|]. split; [unfold LNS_794; repeat constructor|]. split; [reflexivity|]. change (zlength LNS_794) with 17. lia.
  - split; [apply ln_668_at; exact MI|]. split; [unfold LNS_668; repeat constructor|]. split; [reflexivity|]. change (zlength LNS_668) with 23. lia.
Qed.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
Lemma nidobj_cells : forall m nid, ap_img m -> nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  ro_cells ctusegs m (P_NID_OBJS_VA + 40 * nid + 16) [C4 (wz nid)]
  /\ ro_cells ctusegs m (P_NID_OBJS_VA + 40 * nid + 8) [C8 (wz (ln_addr nid))].
Proof.
  intros m nid IMG Hn. unfold ln_addr, P_NID_OBJS_VA, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption, LN_794, LN_668, MallocRep.wz in *.
  destruct Hn as [-> | ->]; cbn [Z.eqb Pos.eqb].
  - split.
    + eapply W_obj_lookup.ro_cells_recast; [apply (ap_img_ro_cells m (2898056 + 40 * 794 + 16) 4); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]| cbn; tauto| bytes_lit_eq].
    + eapply W_obj_lookup.ro_cells_recast; [apply (ap_img_ro_cells m (2898056 + 40 * 794 + 8) 8); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]| cbn; tauto| bytes_lit_eq].
  - split.
    + eapply W_obj_lookup.ro_cells_recast; [apply (ap_img_ro_cells m (2898056 + 40 * 668 + 16) 4); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]| cbn; tauto| bytes_lit_eq].
    + eapply W_obj_lookup.ro_cells_recast; [apply (ap_img_ro_cells m (2898056 + 40 * 668 + 8) 8); [exact IMG| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]| cbn; tauto| bytes_lit_eq].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma gentime_new_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp) ->
              evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz 24) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ASN1_STRING_TYPE_NEW) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz GENTIME_NEW) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO H.
  unfold GENTIME_NEW, ASN1_STRING_TYPE_NEW, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST. do 8 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
Qed.

Lemma gentime_free_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  (forall m1, munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp) ->
              evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ASN1_STRING_FREE) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz GENTIME_FREE) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST MI GLO LO H.
  unfold GENTIME_FREE, ASN1_STRING_FREE, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  carve_frame 16%nat ST. do 7 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (H mx MU WM ltac:(assumption) ST) end.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition leaf16_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

Lemma get0_data_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo G D : Z) (pre : list cell) (post : list cell),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  ro_cells ctusegs m G (pre ++ C8 (wz D) :: post) -> Z.of_nat (cells_size pre) = 8 -> 0 < G -> G mod 8 = 0 -> (G + 24 <= lo \/ bv_unsigned sp <= G) -> 0 <= D < 2^64 ->
  a0 = wz G ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m D)
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz GET0_DATA) fc None m (seg_rom ctusegs)).
Proof.
  intros until post. intros ST MI GLO LO HC SZ G0 GAL SEP DR ->.
  unfold GET0_DATA, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  destruct HC as [WF BY]. rewrite cells_bytes_app in BY. apply bytes_at_app in BY. destruct BY as [_ BY].
  rewrite (cells_bytes_length pre) in BY by (apply cells_wf_app' in WF; exact (proj1 WF)). rewrite SZ in BY.
  cbn [cells_bytes cbytes app] in BY. apply bytes_at_app in BY. destruct BY as [BY _].
  assert (HD : ro_cells ctusegs m (G + 8) [C8 (Z_to_bv 64 D)]).
  { split; [cbn; tauto|]. cbn [cells_bytes cbytes app]. rewrite app_nil_r. exact BY. }
  clear BY WF.
  assert (SEPD : G + 8 + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= G + 8) by lia.
  assert (GHI : G + 16 <= 2^64) by (destruct HD as [_ [_ [GH _]]]; cbn in GH; lia).
  carve_frame 16%nat ST. do 4 zstep.
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC GAL; Z.div_mod_to_equations; lia|]. clear KC.
  zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold leaf16_post. do 14 eexists. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.

Definition nid2ln_post (ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 : word) (F : bvmap 5 word) (fc : bv 32)
    (lo : Z) (m : mem) (r : Z) : machine_state -> Prop :=
  fun ms' => exists t0 t1 t2 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 m',
    ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (Z_to_bv 64 r) a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
             F (ret_pc ra) fc None m' (seg_rom ctusegs)
    /\ munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
    /\ stk ctusegs m' lo (bv_unsigned sp).

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma OBJ_nid2ln_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo nid : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 96 ->
  ap_img m -> nid = NID_ecdsa_with_SHA256 \/ nid = NID_sha256WithRSAEncryption ->
  a0 = wz nid ->
  evt ctusegs (nid2ln_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (ln_addr nid))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz OBJ_NID2LN) fc None m (seg_rom ctusegs)).
Proof.
  intros until nid. intros ST MI GLO LO IMG Hn ->.
  destruct (nidobj_cells m nid IMG Hn) as [HN HL].
  assert (NR : 0 < nid < NUM_NID /\ 0 <= ln_addr nid < 2^64).
  { unfold ln_addr, NUM_NID, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption, LN_794, LN_668 in *. destruct Hn as [-> | ->]; cbn; lia. }
  destruct NR as [NR LR].
  unfold OBJ_NID2LN, GLOBALS_TOP, P_NID_OBJS_VA, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR. unfold NUM_NID in NR.
  assert (SEPN : 2898056 + 40 * nid + 8 + 8 <= bv_unsigned sp - 16 \/ bv_unsigned sp <= 2898056 + 40 * nid + 8) by lia.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  zstep. name_mem m1.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -16)) = bv_unsigned sp + -16) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply (OBJ_nid2obj_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 lo nid []);
      [rewrite ?ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ?ESP; lia| unfold NUM_NID; lia
      | unfold P_NID_OBJS_VA, MallocRep.wz; exact HN| reflexivity]. }
  cbv beta. intros ms' (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & m2 & -> & MU2 & WM2 & MI2 & ST2).
  rewrite ?ESP in MU2, ST2.
  eapply rw_cells_transport in FR; [| exact MU2| exact WM2| cbn [disjoint_from cells_size csize Nat.add]; lia].
  eapply ro_cells_transport in HL; [| exact MU2| cbn [disjoint_from cells_size csize Nat.add]; lia].
  apply (munch_weaken _ [(bv_unsigned sp - 96, bv_unsigned sp)]%Z) in MU2; [| unfold sub_fp; cbn [outside]; intros y Hy; lia].
  assert (MU3 : munch [(bv_unsigned sp - 96, bv_unsigned sp)]%Z m m2) by (eapply munch_trans; [exact MU| exact MU2]).
  assert (WM3 : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU MU2 WM WM2 MI ST HN. rename MU3 into MU, WM3 into WM, MI2 into MI, ST2 into ST. clear dependent m1.
  replace (ret_pc (Z_to_bv 64 1029340)) with (Z_to_bv 64 1029340) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0; [exfalso; unfold P_NID_OBJS_VA in K0; rewrite ?land_M64_small, ?unsigned_lit in K0 by lia; lia|]. clear K0.
  zstep. zstep. if_cases KC; zify_cond KC; [exfalso; unfold P_NID_OBJS_VA in KC; rewrite ?land_M64_small, ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC; Z.div_mod_to_equations; lia|]. clear KC.
  unfold P_NID_OBJS_VA. zstep. do 3 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. unfold nid2ln_post. do 14 eexists. eexists. split; [reflexivity|]. repeat (split; [assumption|]). assumption.
Qed.


(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma sng_C18 : forall m lo q D (a3 a4 a5 a6 a7 : word) (GD : Z) (g : list Z) (ms : Z) (junk : list byte),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  bytes_at ctusegs m GD (zb g ++ Z_to_bv 8 0 :: junk) -> Forall (fun c => 0 < c < 256) g -> zlength g = 15 ->
  GD mod 8 = 0 -> 4096 <= GD -> GD + 16 + zlength junk <= lo -> lo <= D -> lo < 2^63 ->
  0 <= ms < 1000 -> a3 = Z_to_bv 64 GD -> bv_unsigned a4 mod 2^32 = ms ->
  sng_call_ok m lo q D 20 A_C18 FMT_C18 [a3; a4; a5; a6; a7] [PA_s g; PA_i ms] (ct_genstr g ms).
Proof.
  intros until junk. intros MI SL HS RNG LG AL8 GLO GHI LOD L63 MSR -> A4.
  destruct (printf_piecesx_C18 g ms ltac:(lia) MSR) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  pose proof (zlength_nonneg'' (zb g ++ Z_to_bv 8 0 :: junk)) as J0. pose proof (zlength_nonneg'' junk) as J1.
  split; [apply fmt_C18_at; exact MI|]. split; [exact fmt_bytes_C18|]. split; [exact pass1x_ok_C18|].
  split; [unfold A_C18, STATIC_SPLIT; change (zlength FMT_C18) with 12; lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok]. rewrite !unsigned_lit by lia. split; [| split; [split; [lia| rewrite A4; symmetry; apply Z.mod_small; lia]| exact I]].
    exists junk. split.
    { eapply bytes_at_transport; [exact HS| exact MU'|]. cbn [disjoint_from]. unfold zb. rewrite length_app, length_map. cbn [length].
      unfold zlength in *. split; [lia|]. split; [lia| exact I]. }
    split; [exact RNG|]. rewrite LG.
    replace (- (GD + 15 + 1) mod 8) with 0 by (symmetry; replace (- (GD + 15 + 1)) with ((- (GD / 8) - 2) * 8) by (pose proof (Z.div_mod GD 8 ltac:(lia)); lia); apply Z.mod_mul; lia).
    unfold zlength in *. lia. }
  assert (MD : printf_modelx OUT_sn OUTFP_sn FMT_C18 [PA_s g; PA_i ms] [] = ITree.Ret (ITree.Exc.Ok (zlength (ct_genstr g ms), ct_genstr g ms))).
  { rewrite <- CC. rewrite L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold SN_CAP. lia. }
  split; [exact MD|].
  split; [apply fp_callsx_nog; repeat constructor|].
  pose proof (zlength_ct_genstr g ms ltac:(lia) MSR) as LO. unfold zlength in LO. lia.
Qed.

(* [comment removed for export] *)
Lemma sng_C18_null : forall m lo q D (a3 a4 a5 a6 a7 : word) (ms : Z),
  mem_inv ctusegs m -> STATIC_SPLIT <= lo ->
  0 <= ms < 1000 -> a3 = Z_to_bv 64 0 -> bv_unsigned a4 mod 2^32 = ms ->
  sng_call_ok m lo q D 20 A_C18 FMT_C18 [a3; a4; a5; a6; a7] [PA_sn; PA_i ms] (ct_genstr_null ms).
Proof.
  intros until ms. intros MI SL MSR -> A4.
  destruct (printf_piecesx_C18_null ms MSR) as (ps & P & CC). pose proof (printf_piecesx_count _ _ _ _ P) as L.
  split; [apply fmt_C18_at; exact MI|]. split; [exact fmt_bytes_C18|]. split; [exact pass1x_ok_C18|].
  split; [unfold A_C18, STATIC_SPLIT; change (zlength FMT_C18) with 12; lia|].
  split.
  { intros m' MU'. cbn [args_ok arg_ok]. split; [rewrite unsigned_lit by lia; reflexivity|]. split; [| exact I]. split; [lia|]. rewrite A4. symmetry. apply Z.mod_small. lia. }
  assert (MD : printf_modelx OUT_sn OUTFP_sn FMT_C18 [PA_sn; PA_i ms] [] = ITree.Ret (ITree.Exc.Ok (zlength (ct_genstr_null ms), ct_genstr_null ms))).
  { rewrite <- CC. rewrite L. apply (printf_modelx_sn _ _ _ _ P). rewrite L. unfold SN_CAP. lia. }
  split; [exact MD|].
  split; [apply fp_callsx_nog; repeat constructor|].
  pose proof (zlength_ct_genstr_null ms MSR) as LO. unfold zlength in LO. lia.
Qed.

End WithCeiling0.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Fixpoint zlist_eqb (l1 l2 : list Z) : bool :=
  match l1, l2 with [], [] => true | x :: l1', y :: l2' => (x =? y) && zlist_eqb l1' l2' | _, _ => false end.
Lemma zlist_eqb_eq : forall l1 l2, zlist_eqb l1 l2 = true -> l1 = l2.
Proof.
  induction l1 as [|x l1 IH]; intros [|y l2] H; cbn in H; try discriminate; [reflexivity|].
  apply andb_prop in H. destruct H as [H1 H2]. apply Z.eqb_eq in H1. subst y. f_equal. apply IH. exact H2.
Qed.
Definition zpad3_check : bool := forallb (fun ms => zlist_eqb (zpad 3 ms) (dec3 ms)) (zrange 1000 0).
Lemma zpad3_check_ok : zpad3_check = true. Proof. vm_compute. reflexivity. Qed.

Lemma zpad3_dec3 : forall ms, 0 <= ms < 1000 -> zpad 3 ms = dec3 ms.
Proof.
  intros ms Hms. pose proof (proj1 (forallb_forall _ _) zpad3_check_ok ms ltac:(apply zrange_In; lia)) as C. cbv beta in C.
  apply zlist_eqb_eq. exact C.
Qed.

Lemma genstr_some : forall ts t, gentime_adj ts = Some t -> ct_genstr (gen15 t) (ts_ms ts) = genstr ts.
Proof.
  intros ts t E. unfold ct_genstr, genstr. rewrite E. pose proof (ts_ms_range ts). rewrite zpad3_dec3 by lia. reflexivity.
Qed.

Lemma genstr_none : forall ts, gentime_adj ts = None -> ct_genstr_null (ts_ms ts) = genstr ts.
Proof.
  intros ts E. unfold ct_genstr_null, genstr. rewrite E. pose proof (ts_ms_range ts). rewrite zpad3_dec3 by lia. reflexivity.
Qed.

(* [comment removed for export] *)
Lemma days_in_month_le31 : forall y m, days_in_month y m <= 31.
Proof. intros y m. unfold days_in_month. repeat (match goal with |- context [if ?c then _ else _] => destruct c; cbn end); lia. Qed.

Lemma dec2_bytes : forall n, 0 <= n <= 99 -> Forall (fun c => 0 < c < 256) (dec2 n).
Proof.
  intros n Hn. unfold dec2. pose proof (digit_range (n / 10)). pose proof (digit_range (n mod 10)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)). assert (0 <= n / 10 < 10) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  repeat constructor; lia.
Qed.
Lemma dec4_bytes : forall n, 0 <= n <= 9999 -> Forall (fun c => 0 < c < 256) (dec4 n).
Proof.
  intros n Hn. unfold dec4. pose proof (digit_range (n / 1000)). pose proof (digit_range ((n / 100) mod 10)). pose proof (digit_range ((n / 10) mod 10)). pose proof (digit_range (n mod 10)).
  pose proof (Z.mod_pos_bound n 10 ltac:(lia)). pose proof (Z.mod_pos_bound (n / 100) 10 ltac:(lia)). pose proof (Z.mod_pos_bound (n / 10) 10 ltac:(lia)).
  assert (0 <= n / 1000 < 10) by (split; [apply Z.div_pos; lia| apply Z.div_lt_upper_bound; lia]).
  repeat constructor; lia.
Qed.
Lemma gen15_bytes : forall ts t, gentime_adj ts = Some t -> Forall (fun c => 0 < c < 256) (gen15 t).
Proof.
  intros ts t E. pose proof (gentime_adj_valid ts t E) as (Y & MO & MD & HH & MI & SS).
  pose proof (days_in_month_le31 (t_year t) (t_mon t)) as DM.
  unfold gen15. repeat (apply Forall_app; split); first [apply dec4_bytes; lia| apply dec2_bytes; lia| repeat constructor; unfold CH_Z; lia].
Qed.
