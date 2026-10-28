(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_kit Printf_lib.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Ltac bytes_lit_eq := cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]].

(* [comment removed for export] *)
Ltac cell_of_bytes bs ::=
  lazymatch bs with
  | le8 ?v => constr:(C8 v)
  | le4 ?v => constr:(C4 v)
  | le2 ?v => constr:(C2 v)
  | [?b] => constr:(C1 b)
  | le1 (zxb ?b) => constr:(C1 b)
  | le1 ?v => constr:(C1 (Z_to_bv 8 (bv_unsigned v)))
  | Z_to_le_bytes 8 ?z => constr:(C8 (Z_to_bv 64 z))
  | Z_to_le_bytes 4 ?z => constr:(C4 (Z_to_bv 64 z))
  | Z_to_le_bytes 1 ?z => constr:(C1 (Z_to_bv 8 z))
  end.

Section WithCeiling. Context {CE__ : Ceiling}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma CRYPTO_clear_free_null_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo : Z),
  stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> mem_inv ctusegs m ->
  a0 = wz 0 ->
  evt ctusegs (fun ms' => exists m',
               ms' = MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m'
               /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz CRYPTO_CLEAR_FREE) fc None m (seg_rom ctusegs)).
Proof.
  intros until lo. intros ST GLO LO MI ->.
  unfold CRYPTO_CLEAR_FREE, GLOBALS_TOP, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST. do 7 zstep. zstep. if_true.
  do 6 zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. eexists. split; [reflexivity|]. auto.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition ASN1_STRING_SET0_STACK : Z := 48 + 48.

Lemma ASN1_STRING_set0_walk : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) (fc : bv 32) (m : mem) (lo A D ty len : Z),
  stk ctusegs m lo (bv_unsigned sp) -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - ASN1_STRING_SET0_STACK -> mem_inv ctusegs m ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 <= D < 2^64 -> 0 <= len < 2^31 -> 0 <= ty < 2^31 ->
  rw_cells ctusegs m A (asn1_string_cells 0 ty 0 0) ->
  A mod 8 = 0 -> a0 = wz A -> a1 = wz D -> a2 = wz len ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0' a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - ASN1_STRING_SET0_STACK, bv_unsigned sp); (A, A + ASN1_STRING_SIZE)]%Z m m' /\ wmono ctusegs m m'
               /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' A (asn1_string_cells len ty D 0))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_STRING_SET0) fc None m (seg_rom ctusegs)).
Proof.
  intros until len. intros ST GLO LO MI A0 ALO DR LR TR HS AL8 -> -> ->.
  unfold ASN1_STRING_SET0, ASN1_STRING_SET0_STACK, ASN1_STRING_SIZE, GLOBALS_TOP, MallocRep.wz in *. unfold asn1_string_cells, MallocRep.wz in HS.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 48%nat ST. do 7 zstep.
  (* [comment removed for export] *)
  zstep. if_cases K0; zify_cond K0; [exfalso; rewrite ?unsigned_lit in K0 by lia; lia|]. clear K0.
  zstep. zstep. zstep. if_cases KC; zify_cond KC; [exfalso; rewrite ?unsigned_lit in KC by lia; change 7 with (Z.ones 3) in KC; rewrite Z.land_ones in KC by lia; clear - KC AL8; Z.div_mod_to_equations; lia|]. clear KC.
  do 4 zstep. zstep. if_false.
  (* [comment removed for export] *)
  do 5 zstep. zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -48)) = bv_unsigned sp + -48) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply CRYPTO_clear_free_null_spec with (lo := lo); [rewrite ESP; exact ST| unfold GLOBALS_TOP; lia| rewrite ESP; lia| assumption| reflexivity]. }
  cbv beta. intros ms2 (m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 1040836)) with (Z_to_bv 64 1040836) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  assert (MU' : munch [(bv_unsigned sp - 96, bv_unsigned sp); (A, A + 24)]%Z m m2).
  { eapply munch_trans; [exact MU|]. eapply munch_weaken; [| exact MU2]. unfold sub_fp. cbn [outside]. intros y Hy. lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HS; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  clear MU WM MU2 WM2 MI ST. rename MU' into MU. rename WM' into WM. rename MI2 into MI. rename ST2 into ST. clear m1.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep.
  setreg 11%Z (Z_to_bv 64 len) ltac:(f_equal; symmetry; apply set0_len_norm; lia).
  zstep. change (Z.land 0 (-257)) with 0.
  zstep. zstep. zstep.
  do 5 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  apply evt_done. do 15 eexists. eexists. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [assumption|]. split; [exact ST|].
  unfold asn1_string_cells, MallocRep.wz.
  lazymatch goal with H : rw_cells _ _ A ?cs |- rw_cells _ _ A ?cs' => eapply (rw_cells_recast _ _ _ _ H); [cbn; tauto| cbn; bytes_lit_eq| reflexivity] end.
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

Lemma ASN1_object_size_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo len : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  0 <= len < 65536 ->
  a0 = wz 0 -> a1 = wz len -> a2 = wz V_ASN1_OCTET_STRING ->
  evt ctusegs (leaf16_post ra sp gp tp s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 F fc lo m (der_hl len + len))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_OBJECT_SIZE) fc None m (seg_rom ctusegs)).
Proof.
  intros until len. intros ST MI GLO LO LEN -> -> ->. unfold GLOBALS_TOP in GLO. unfold ASN1_OBJECT_SIZE, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                   replace c with false by (symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?signed_of_Z, ?unsigned_lit by lia; first [apply Z.ltb_ge| apply Z.eqb_neq| apply Z.leb_gt]; lia); cbv iota end.
  Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                   replace c with true by (symmetry; unfold bv_eqb, bv_ltu, bv_lts, bv_leu; rewrite ?signed_of_Z, ?unsigned_lit by lia; first [apply Z.ltb_lt| apply Z.eqb_eq| apply Z.leb_le]; lia); cbv iota end.
  zstep. zstep. sfalse. zstep. zstep. strue. zstep. zstep. zstep. if_cases K0; [| exfalso; revert K0; vm_compute; congruence]. clear K0.
  ub. zstep. zstep. if_cases K; zify_cond K; rewrite ?signed_of_Z, ?unsigned_lit in K by lia.
  Ltac os_tail r len FR ST sp :=
    let KT := fresh "KT" in
    zstep; zstep; zstep; rewrite ?(lxor_ones31 len) by lia;
    zstep; (if_cases KT; zify_cond KT; rewrite ?signed_of_Z, ?unsigned_lit in KT by lia; [exfalso; lia|]; clear KT);
    zstep; setreg 13%Z (Z_to_bv 64 (r + len)) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; bv_solve);
    zstep; ub; zstep; setreg 10%Z (Z_to_bv 64 (r + len)) ltac:(rewrite ?(unsigned_lit (r + len)), ?swrap32_small by lia; rewrite ?Z.add_0_r; try reflexivity; rewrite ?swrap32_small by lia; reflexivity);
    do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep; finish.
  - (* [comment removed for export] *)
    rewrite der_hl_small by lia. os_tail 2 len FR ST sp.
  - (* [comment removed for export] *)
    zstep. zstep. rewrite (srliw8_small len) by lia. zstep. rewrite ?(swrap32_small 3) by lia. zstep. if_cases K1; zify_cond K1.
    + (* [comment removed for export] *)
      assert (L256 : 256 <= len) by (rewrite ?land64_small in K1 by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]);
                                    destruct (Z.lt_ge_cases len 256) as [Hl|Hl]; [exfalso; apply K1; rewrite Z.div_small by lia; reflexivity| exact Hl]).
      rewrite der_hl_big by lia.
      zstep. rewrite (srliw8_small (len / 256)) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
      rewrite (Z.div_small (len / 256) 256) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
      zstep. rewrite ?(swrap32_small 4) by lia. zstep. if_cases K2; [exfalso; revert K2; vm_compute; congruence|]. clear K2.
      os_tail 4 len FR ST sp.
    + assert (L256 : len < 256).
      { destruct (Z.lt_ge_cases len 256) as [Hl|Hl]; [exact Hl|]. exfalso. revert K1. rewrite ?land64_small by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
        intros K1. assert (1 <= len / 256) by (apply Z.div_le_lower_bound; lia). lia. }
      rewrite der_hl_mid by lia. os_tail 3 len FR ST sp.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_put_object_spec : forall ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6
    (F : bvmap 5 word) fc (m : mem) (lo len PP P : Z) (junk : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 16 ->
  0 <= len < 65536 -> bv_unsigned sp <= PP -> PP + 8 <= 2^64 -> 0 < P -> P + der_hl len <= lo ->
  rw_cells ctusegs m PP [C8 (wz P)] -> rw_cells ctusegs m P [CB (Z.to_nat (der_hl len)) junk] -> PP mod 8 = 0 ->
  a0 = wz PP -> a1 = wz 0 -> a2 = wz len -> a3 = wz V_ASN1_OCTET_STRING -> a4 = wz 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 a0 a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + der_hl len); (PP, PP + 8)]%Z m m' /\ wmono ctusegs m m'
               /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' PP [C8 (wz (P + der_hl len))] /\ (exists hb, rw_cells ctusegs m' P [CB (Z.to_nat (der_hl len)) hb]))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_PUT_OBJECT) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO LEN PPlo PPhi P0 Plo HPP HP PAL8 -> -> -> -> ->.
  unfold GLOBALS_TOP in GLO. unfold ASN1_PUT_OBJECT, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (der_hl_range len LEN) as HLR.
  pose proof (munch_refl [(bv_unsigned sp - 16, bv_unsigned sp); (P, P + der_hl len); (PP, PP + 8)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 16%nat ST. do 4 zstep.
  (* [comment removed for export] *)
  Ltac po_head := ub; do 7 zstep; zstep; sfalse; ub; zstep; zstep;
                  setreg 13%Z (Z_to_bv 64 4) ltac:(reflexivity);
                  zstep; zstep; zstep; zstep; let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0; zstep; zstep.
  Ltac po_fin FR ST sp P := do 3 zstep; release_frame FR ST (bv_unsigned sp); zstep;
                         apply evt_done; do 14 eexists; eexists; split; [reflexivity|]; repeat (split; [assumption|]);
                         lazymatch goal with H : rw_cells _ _ P ?cs |- _ =>
                          exists (cells_bytes cs); eapply (rw_cells_recast _ _ _ _ H); [cbn; repeat split; reflexivity| cbn; rewrite ?app_nil_r; reflexivity| reflexivity] end.
  Ltac setp r v := setreg r (Z_to_bv 64 v) ltac:(symmetry; apply bv_eq; rewrite ?unsigned_lit by lia; first [lia | bv_solve]).
  destruct (Z_lt_le_dec len 128) as [C1|C1].
  { rewrite der_hl_small in * by lia. change (Z.to_nat 2) with 2%nat in *.
    po_head. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [exfalso; lia|]. clear K.
    (* [comment removed for export] *)
    zstep. zstep. ub. zstep. zstep. zstep. po_fin FR ST sp P. }
  destruct (Z_lt_le_dec len 256) as [C2|C2].
  { rewrite der_hl_mid in * by lia. change (Z.to_nat 3) with 3%nat in *.
    po_head. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [| exfalso; lia]. clear K.
    (* [comment removed for export] *)
    do 4 zstep. zstep. rewrite (srliw8_small len), (Z.div_small len 256) by lia. zstep. try rewrite (swrap32_small 0) by lia. zstep. zstep.
    zstep. if_cases K1; [exfalso; revert K1; vm_compute; congruence|]. clear K1.
    (* [comment removed for export] *)
    ub. do 3 zstep. zstep. if_cases K2; [exfalso; revert K2; vm_compute; congruence|]. clear K2.
    do 2 zstep. ub. rewrite ?Z.add_0_l. setp 14%Z (P + 2). do 3 zstep. zstep. if_cases K3; [| exfalso; revert K3; vm_compute; congruence]. clear K3.
    zstep. if_cases K4; [| exfalso; revert K4; vm_compute; congruence]. clear K4.
    (* [comment removed for export] *)
    ub. setp 11%Z (P + 3). zstep. po_fin FR ST sp P. }
  { rewrite der_hl_big in * by lia. change (Z.to_nat 4) with 4%nat in *.
    po_head. if_cases K; zify_cond K; rewrite ?signed_of_Z in K by lia; [| exfalso; lia]. clear K.
    (* [comment removed for export] *)
    do 4 zstep. zstep. rewrite (srliw8_small len) by lia. zstep. zstep. zstep.
    zstep. if_cases K1; zify_cond K1; [| exfalso; revert K1; rewrite ?land64_small by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]);
                                         intros K1; assert (1 <= len / 256) by (apply Z.div_le_lower_bound; lia); lia].
    (* [comment removed for export] *)
    zstep. rewrite (srliw8_small (len / 256)) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
    rewrite (Z.div_small (len / 256) 256) by (pose proof (Z.div_pos len 256); split; [lia| apply Z.div_lt_upper_bound; lia]).
    zstep. zstep. try rewrite (swrap32_small 1) by lia. zstep. zstep. if_cases K2; [exfalso; revert K2; vm_compute; congruence|]. clear K2 K1.
    (* [comment removed for export] *)
    ub. do 3 zstep. zstep. if_cases K3; [exfalso; revert K3; vm_compute; congruence|]. clear K3.
    do 2 zstep. ub. rewrite ?Z.add_0_l. setp 14%Z (P + 3). do 2 zstep. zstep. rewrite (srliw8_small len) by lia. zstep. if_cases K4; [| exfalso; revert K4; vm_compute; congruence]. clear K4.
    zstep. if_cases K5; [exfalso; revert K5; vm_compute; congruence|]. clear K5.
    do 2 zstep. ub. rewrite ?Z.add_0_l. setp 14%Z (P + 2). do 3 zstep. zstep. if_cases K6; [| exfalso; revert K6; vm_compute; congruence]. clear K6.
    zstep. if_cases K7; [| exfalso; revert K7; vm_compute; congruence]. clear K7.
    ub. setp 11%Z (P + 4). zstep. po_fin FR ST sp P. }
Qed.
End WithCeiling.
