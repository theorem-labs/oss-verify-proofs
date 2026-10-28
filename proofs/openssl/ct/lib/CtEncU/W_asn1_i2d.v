(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
(* [comment removed for export] *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Malloc Prog LibProg CtSizes CtWire ApPrim.
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem SFModel.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep MallocBlocks Malloc_iface Malloc_ifaceP.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtMallocU Require Import RMallocRep RMallocTree RMalloc_iface.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_memcpy.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtBnU Require Import BnKit BnHeap BnRep W_crypto.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApRep ApWalkTac W_item_d2i_stmt W_item_d2i_img.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtEncU Require Import EncPure EncStmt EncKit W_asn1_enc_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.
Local Ltac step := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.step.
Local Ltac zstep := ual; ub; OssFuzzTheorems.Proofs.openssl.ct.lib.Lib.Step.zstep.

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

Definition ASN1_EX_I2C_OCT : Z := 0x116438.        (* [comment removed for export] *)
Definition ASN1_EX_I2C_JT : Z := 0x4170c.          (* [comment removed for export] *)
Definition ASN1_I2D_EX_PRIMITIVE : Z := 0x1160c0.
Definition ASN1_ITEM_FLAGS_I2D : Z := 0x115438.
Definition ASN1_ITEM_I2D : Z := 0x115538.
Definition A_TASN_ENC_C : Z := 0x293e3.            (* [comment removed for export] *)

(* [comment removed for export] *)
Ltac lit_addr H := lazymatch type of H with
  | ro_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H
  | rw_cells _ _ ?a _ => let v := eval vm_compute in a in change a with v in H end.

(* [comment removed for export] *)
Ltac btaken := let K0 := fresh "K0" in if_cases K0; [| exfalso; revert K0; vm_compute; congruence]; clear K0.
Ltac bnot := let K0 := fresh "K0" in if_cases K0; [exfalso; revert K0; vm_compute; congruence|]; clear K0.
Ltac sfalse := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with false by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.
Ltac strue := lazymatch goal with |- evt _ _ (MS _ _ (if ?c then _ else _) _ _ _ _) =>
                 replace c with true by (symmetry; unfold_cond; fold_lit_ux; rewrite ?signed_of_Z, ?unsigned_lit by lia; solve_cond_rec); cbv iota end.

Section WithCeiling0. Context {CE__ : Ceiling} {RN__ : RunRnd}.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Local Ltac img_cell A n c :=
  let bs := eval vm_compute in (match image_bytes ctusegs A n with Some bs => bs | None => [] end) in
  lazymatch goal with |- ro_cells _ ?mm _ _ =>
  apply (ro_cells_recast mm A [CB n bs] [c]);
  [ apply (ap_img_ro_cells mm A n bs); [assumption| unfold IMG_LO; lia| unfold IMG_HI; cbn; lia| vm_compute; reflexivity]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ] end.

Lemma item_size_octet : forall m, ap_img m -> ro_cells ctusegs m (ITEM_OCTET + 40) [C8 (Z_to_bv 64 0)].
Proof. intros m HI. unfold ITEM_OCTET. img_cell 2960368 8%nat (C8 (Z_to_bv 64 0)). Qed.

Local Ltac rom_cell4 A v :=
  intros m MI;
  let bs := eval vm_compute in (match image_bytes ctusegs A 4 with Some bs => bs | None => [] end) in
  apply (ro_cells_recast m A [CB 4 bs] [C4 (Z_to_bv 64 v)]);
  [ apply (ro_cells_image ctusegs m A bs MI); [vm_compute; reflexivity| lia| cbn; lia]
  | cbn; repeat split; reflexivity
  | cbv -[Z_to_bv]; repeat first [reflexivity | apply (f_equal2 (@cons _)); [apply bv_eq; vm_compute; reflexivity|]] ].

(* [comment removed for export] *)
Lemma jt_ex_i2c_oct : forall m, mem_inv ctusegs m -> ro_cells ctusegs m 268064 [C4 (Z_to_bv 64 871712)]. Proof. rom_cell4 268064 871712. Qed.

(* [comment removed for export] *)
Definition item_oct (m : mem) : Prop := item_cells m ITEM_OCTET V_ASN1_OCTET_STRING /\ ro_cells ctusegs m (ITEM_OCTET + 40) [C8 (Z_to_bv 64 0)].
Lemma item_oct_of_img : forall m, ap_img m -> item_oct m.
Proof. intros m HI. split; [apply item_cells_octet; exact HI| apply item_size_octet; exact HI]. Qed.

Lemma item_oct_agree : forall m m' W, item_oct m -> munch W m m' ->
  Forall (fun iv => snd iv <= ITEM_OCTET \/ ITEM_OCTET + 48 <= fst iv) W -> item_oct m'.
Proof.
  intros m m' W ((I1 & I2 & I3 & I4 & I5) & I6) MU HW. unfold item_cells, item_oct in *.
  assert (DJ : forall a k, ITEM_OCTET <= a -> a + Z.of_nat k <= ITEM_OCTET + 48 -> disjoint_from W a (Z.of_nat k)).
  { intros a k Ha Hk. clear - HW Ha Hk. induction W as [|[x y] W IH]; [exact I|]. apply Forall_cons_iff in HW. destruct HW as [H1 H2].
    cbn [fst snd] in H1. cbn. split; [lia| apply IH; exact H2]. }
  unfold ITEM_OCTET in *.
  repeat split; (eapply ro_cells_transport; [eassumption| exact MU| apply DJ; cbn; lia]).
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma asn1_ex_i2c_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL PUT A len D fl cout : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 -> bv_unsigned sp <= PUT -> PUT + 4 <= 2^64 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 <= len < 2^31 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 -> 0 <= cout < 2^64 ->
  PVAL mod 8 = 0 -> PUT mod 4 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] -> ro_cells ctusegs m PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  a0 = wz PVAL -> a1 = wz cout -> a2 = wz PUT -> a3 = wz ITEM_OCTET ->
  (forall m1 (x10 x12 x14 x15 x16 x17 : word) junk,
     munch [(bv_unsigned sp + -48, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
     stk ctusegs m1 lo (bv_unsigned sp + -48) ->
     rw_cells ctusegs m1 (bv_unsigned sp + -48) [CB 16%nat junk; C8 (wz cout); C8 s1; C8 s0; C8 ra] ->
     evt ctusegs P (MS (mkR ra (Z_to_bv 64 (bv_unsigned sp + -48)) gp tp t0 t1 t2 sp (Z_to_bv 64 len)
                           x10 (wz cout) x12 (wz D) x14 x15 x16 x17 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                     F (Z_to_bv 64 0x116520) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ASN1_EX_I2C) fc None m (seg_rom ctusegs)).
Proof.
  intros until cout. intros ST MI GLO LO IT PVlo PVhi PUlo PUhi A0 ALO LEN DR FLR CR PV8 PU4 A8 HPV HPU HS -> -> -> -> K.
  unfold GLOBALS_TOP in GLO. unfold ASN1_EX_I2C, ASN1_STRING_SIZE, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  destruct IT as ((I1 & I2 & I3 & I4 & I5) & I6). unfold ITEM_OCTET in *. lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I6.
  unfold asn1_string_cells, MallocRep.wz in HS.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  pose proof (jt_ex_i2c_oct m MI) as JT.
  carve_frame 48%nat ST. do 5 zstep.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. bnot. zstep. zstep. zstep. bnot. zstep. zstep. sfalse. zstep. zstep. btaken. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. zstep. btaken.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. rewrite (sx32_lit len) by lia.
  eapply K; [exact MU| exact WM| assumption| exact ST| exact FR].
Qed.

(* [comment removed for export] *)
Lemma asn1_ex_i2c_len_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL PUT A len D fl : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 -> bv_unsigned sp <= PUT -> PUT + 4 <= 2^64 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 <= len < 2^31 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 ->
  PVAL mod 8 = 0 -> PUT mod 4 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] -> ro_cells ctusegs m PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  a0 = wz PVAL -> a1 = wz 0 -> a2 = wz PUT -> a3 = wz ITEM_OCTET ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_EX_I2C) fc None m (seg_rom ctusegs)).
Proof.
  intros until fl. intros ST MI GLO LO IT PVlo PVhi PUlo PUhi A0 ALO LEN DR FLR PV8 PU4 A8 HPV HPU HS -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  eapply asn1_ex_i2c_fwd with (cout := 0) (PVAL := PVAL) (PUT := PUT) (A := A) (len := len) (D := D) (fl := fl) (lo := lo); try eassumption; try reflexivity; try lia.
  intros m1 x10 x12 x14 x15 x16 x17 junk MU WM MI1 ST1 FR. unfold GLOBALS_TOP, MallocRep.wz in *.
  (* [comment removed for export] *)
  zstep. btaken. zstep. zstep. do 3 zstep. zstep. release_frame FR ST1 (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. auto.
Qed.

(* [comment removed for export] *)
Lemma asn1_ex_i2c_write_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL PUT A len D fl C : Z) (src junk : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 48 -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 -> bv_unsigned sp <= PUT -> PUT + 4 <= 2^64 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 < len < 2^31 -> 0 < D -> D + len <= lo -> 0 <= fl < 2^64 -> 0 < C -> C + len <= lo ->
  (D + len <= C \/ C + len <= D) ->
  PVAL mod 8 = 0 -> PUT mod 4 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] -> ro_cells ctusegs m PUT [C4 (wz V_ASN1_OCTET_STRING)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  bytes_at ctusegs m D src -> length src = Z.to_nat len -> rw_cells ctusegs m C [CB (Z.to_nat len) junk] ->
  a0 = wz PVAL -> a1 = wz C -> a2 = wz PUT -> a3 = wz ITEM_OCTET ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 len) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - 48, bv_unsigned sp); (C, C + len)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' C [CB (Z.to_nat len) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_EX_I2C) fc None m (seg_rom ctusegs)).
Proof.
  intros until junk. intros ST MI GLO LO IT PVlo PVhi PUlo PUhi A0 ALO LEN D0 DLO FLR C0 CLO SEP PV8 PU4 A8 HPV HPU HS SRC SLEN DST -> -> -> ->.
  change (frozen (D + len <= C \/ C + len <= D)) in SEP.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  eapply asn1_ex_i2c_fwd with (cout := C) (PVAL := PVAL) (PUT := PUT) (A := A) (len := len) (D := D) (fl := fl) (lo := lo); try eassumption; try reflexivity; try lia.
  intros m1 x10 x12 x14 x15 x16 x17 junkf MU WM MI1 ST1 FR. unfold GLOBALS_TOP, MallocRep.wz in *.
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in DST; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  (* [comment removed for export] *)
  zstep. sfalse. zstep. sfalse. zstep. zstep. zstep. zstep. zstep.
  eapply evt_cut.
  { eapply memcpy_spec with (src := src) (junk := junk); rewrite ?unsigned_lit by lia; [exact SRC| exact SLEN| exact DST| exact SEP| exact MI1]. }
  cbv beta. intros ms2 PO. unfold memcpy_post in PO. rewrite ?unsigned_lit in PO by lia.
  destruct PO as (q0 & q1 & q2 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & DST2 & SRC2).
  replace (ret_pc (Z_to_bv 64 1140028)) with (Z_to_bv 64 1140028) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  assert (ST2 : stk ctusegs m2 lo (bv_unsigned sp + -48)) by (eapply stk_transport; [exact ST1| exact MU2| exact WM2| cbn; lia]).
  assert (MU' : munch [(bv_unsigned sp - 48, bv_unsigned sp); (C, C + len)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 MI1 ST1. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. do 3 zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|]. repeat (split; [assumption|]). exact DST2.
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Definition EX_PRIM_STACK : Z := 96 + 48.

Lemma ex_prim_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL A len D fl out : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - EX_PRIM_STACK -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 <= len < 2^31 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 -> 0 <= out < 2^64 ->
  bv_unsigned sp mod 16 = 0 -> PVAL mod 8 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  a0 = wz PVAL -> a1 = wz out -> a2 = wz ITEM_OCTET -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  (forall m1 (x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 : word) junk,
     munch [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
     stk ctusegs m1 lo (bv_unsigned sp + -96) ->
     rw_cells ctusegs m1 (bv_unsigned sp + -96) [CB 4%nat junk; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp (wz out)
                            x10 x11 x12 x13 x14 x15 x16 x17
                            (Z_to_bv 64 len) (Z_to_bv 64 V_ASN1_OCTET_STRING) (Z_to_bv 64 0) (wz ITEM_OCTET) (Z_to_bv 64 len) (wz PVAL) (Z_to_bv 64 0) (Z_to_bv 64 V_ASN1_OCTET_STRING)
                            s10 s11 x28 x29 x30 x31)
                       F (Z_to_bv 64 0x116158) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ASN1_I2D_EX_PRIMITIVE) fc None m (seg_rom ctusegs)).
Proof.
  intros until out. intros ST MI GLO LO IT PVlo PVhi A0 ALO LEN DR FLR OUTR SP16 PV8 A8 HPV HS -> -> -> -> -> K.
  unfold GLOBALS_TOP in GLO. unfold ASN1_I2D_EX_PRIMITIVE, EX_PRIM_STACK, ASN1_STRING_SIZE, MallocRep.wz in *.
  pose proof IT as ((I1 & I2 & I3 & I4 & I5) & I6). unfold ITEM_OCTET in *. lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I6.
  unfold asn1_string_cells, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 96%nat ST. do 13 zstep.
  (* [comment removed for export] *)
  do 5 zstep. zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => rename mx into m1 end.
  assert (IT1 : item_oct m1) by (eapply item_oct_agree; [exact IT| exact MU| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  pose proof (cells_pick m1 (bv_unsigned sp + -96) 4 [CB 4%nat _] (C4 (Z_to_bv 64 4)) _ FR eq_refl) as HPU.
  eapply evt_cut.
  { eapply asn1_ex_i2c_len_spec with (lo := lo) (PVAL := PVAL) (PUT := bv_unsigned sp + -96 + 4) (A := A) (len := len) (D := D) (fl := fl);
      rewrite ?ESP; try eassumption; try reflexivity; try (unfold ITEM_OCTET, V_ASN1_OCTET_STRING, GLOBALS_TOP, ASN1_STRING_SIZE, MallocRep.wz; first [lia | reflexivity | f_equal; lia]).
    clear - SP16; ulia_open; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 1138984)) with (Z_to_bv 64 1138984) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU2) in HPV; [| cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU2) in HS; [| cbn; lia].
  assert (IT2 : item_oct m2) by (eapply item_oct_agree; [exact IT1| exact MU2| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
  assert (MU' : munch [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 ST IT1 HPU I1 I2 I3 I4 I5 I6. rename MU' into MU. rename WM' into WM. clear MI. rename MI2 into MI. clear m1.
  (* [comment removed for export] *)
  zstep. zstep. sfalse. zstep. zstep. zstep. zstep. zstep. zstep. zstep. btaken. zstep. zstep.
  replace (len + 2 <? 1) with false by (symmetry; apply Z.ltb_ge; lia). cbn [Z.b2z]. change (Z.shiftl 0 1) with 0.
  change (Z.land (bv_swrap 32 (0 + -1)) 18446744073709551615) with 18446744073709551615.
  rewrite (Z.land_comm 18446744073709551615 len), (land64_small len) by lia.
  change (sx32 (Z_to_bv 64 4)) with (Z_to_bv 64 4).
  eapply K; [exact MU| exact WM| exact MI| exact ST2| exact FR].
Qed.

(* [comment removed for export] *)
Lemma ex_prim_tail : forall
    (x1 sp gp tp x5 x6 x7 x9 x10 x11 x12 x13 x14 x15 x16 x17 x21 x22 x23 x24 s10 s11 x28 x29 x30 x31 : word)
    (ra s0 s1 s2 s3 s4 s5 s6 s7 s8 s9 : word)
    (F : bvmap 5 word) fc (m0 m : mem) (lo len : Z) junk W,
  mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - EX_PRIM_STACK -> 0 <= len < 65536 ->
  munch W m0 m -> wmono ctusegs m0 m -> (forall y, outside W y -> outside [(bv_unsigned sp + -144, bv_unsigned sp)]%Z y) ->
  stk ctusegs m lo (bv_unsigned sp + -96) ->
  rw_cells ctusegs m (bv_unsigned sp + -96) [CB 4%nat junk; C4 (Z_to_bv 64 V_ASN1_OCTET_STRING); C8 s9; C8 s8; C8 s7; C8 s6; C8 s5; C8 s4; C8 s3; C8 s2; C8 s1; C8 s0; C8 ra] ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch W m0 m' /\ wmono ctusegs m0 m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ munch [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m')
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp x5 x6 x7 sp x9 x10 x11 x12 x13 x14 x15 x16 x17
             (Z_to_bv 64 len) (Z_to_bv 64 V_ASN1_OCTET_STRING) (Z_to_bv 64 0) x21 x22 x23 x24 (Z_to_bv 64 V_ASN1_OCTET_STRING) s10 s11 x28 x29 x30 x31)
        F (Z_to_bv 64 0x1161fc) fc None m (seg_rom ctusegs)).
Proof.
  intros until W. intros MI GLO LO LEN MU0 WM0 HWW ST FR.
  unfold GLOBALS_TOP in GLO. unfold EX_PRIM_STACK, V_ASN1_OCTET_STRING, MallocRep.wz in *.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply ASN1_object_size_spec with (lo := lo) (len := len); rewrite ?ESP; try eassumption; try reflexivity; unfold GLOBALS_TOP; lia. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x11622c)) with (Z_to_bv 64 0x11622c) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  assert (MU' : munch [(bv_unsigned sp + -144, bv_unsigned sp)]%Z m m2).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 ST MI. rename MU' into MU. rename WM' into WM. rename MI2 into MI.
  (* [comment removed for export] *)
  zstep. zstep. do 11 zstep. zstep. release_frame FR ST2 (bv_unsigned sp). zstep.
  apply evt_done. do 14 eexists. eexists. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU0| eapply munch_weaken; [exact HWW| exact MU]]|].
  split; [eapply wmono_trans; [exact WM0| exact WM]|]. split; [exact MI|]. split; [exact ST2|]. split; [exact MU| exact WM].
Qed.

(* [comment removed for export] *)
Lemma asn1_i2d_ex_prim_len_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL A len D fl : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - EX_PRIM_STACK -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 <= len < 65536 -> 0 <= D < 2^64 -> 0 <= fl < 2^64 ->
  bv_unsigned sp mod 16 = 0 -> PVAL mod 8 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  a0 = wz PVAL -> a1 = wz 0 -> a2 = wz ITEM_OCTET -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - EX_PRIM_STACK, bv_unsigned sp)]%Z m m' /\ wmono ctusegs m m' /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp))
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_I2D_EX_PRIMITIVE) fc None m (seg_rom ctusegs)).
Proof.
  intros until fl. intros ST MI GLO LO IT PVlo PVhi A0 ALO LEN DR FLR SP16 PV8 A8 HPV HS -> -> -> -> ->.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  eapply ex_prim_fwd with (out := 0) (PVAL := PVAL) (A := A) (len := len) (D := D) (fl := fl) (lo := lo); try eassumption; try reflexivity; try lia.
  intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk MU WM MI1 ST1 FR. unfold EX_PRIM_STACK, MallocRep.wz in *.
  (* [comment removed for export] *)
  zstep. btaken.
  eapply evt_mono; [eapply ex_prim_tail; try eassumption; try lia; intros y Hy; cbn in Hy |- *; lia|].
  cbv beta. intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & MU' & WM' & MI' & ST' & _ & _).
  do 14 eexists. eexists. split; [reflexivity|]. auto.
Qed.

(* [comment removed for export] *)
Lemma asn1_i2d_ex_prim_write_spec : forall
    (ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL A len D fl PP P : Z) (src j1 j2 : list byte),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - EX_PRIM_STACK -> item_oct m ->
  bv_unsigned sp <= PVAL -> PVAL + 8 <= 2^64 -> bv_unsigned sp <= PP -> PP + 8 <= PVAL ->
  0 < A -> A + ASN1_STRING_SIZE <= lo -> 0 < len < 65536 -> 0 < D -> D + len <= lo -> 0 <= fl < 2^64 ->
  0 < P -> P + der_hl len + len <= lo -> (D + len <= P \/ P + der_hl len + len <= D) -> (A + ASN1_STRING_SIZE <= P \/ P + der_hl len + len <= A) ->
  (P + der_hl len + len <= 0x10000 \/ 0x355000 <= P) ->
  bv_unsigned sp mod 16 = 0 -> PVAL mod 8 = 0 -> A mod 8 = 0 ->
  ro_cells ctusegs m PVAL [C8 (wz A)] ->
  ro_cells ctusegs m A (asn1_string_cells len V_ASN1_OCTET_STRING D fl) ->
  bytes_at ctusegs m D src -> length src = Z.to_nat len ->
  PP mod 8 = 0 ->
  rw_cells ctusegs m PP [C8 (wz P)] -> rw_cells ctusegs m P [CB (Z.to_nat (der_hl len)) j1] -> rw_cells ctusegs m (P + der_hl len) [CB (Z.to_nat len) j2] ->
  a0 = wz PVAL -> a1 = wz PP -> a2 = wz ITEM_OCTET -> a3 = Z_to_bv 64 (-1) -> a4 = wz 0 ->
  evt ctusegs (fun ms' => exists t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' m',
               ms' = MS (mkR ra sp gp tp t0' t1' t2' s0 s1 (Z_to_bv 64 (der_hl len + len)) a1' a2' a3' a4' a5' a6' a7' s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3' t4' t5' t6')
                        F (ret_pc ra) fc None m' (seg_rom ctusegs)
               /\ munch [(bv_unsigned sp - EX_PRIM_STACK, bv_unsigned sp); (P, P + der_hl len + len); (PP, PP + 8)]%Z m m' /\ wmono ctusegs m m'
               /\ mem_inv ctusegs m' /\ stk ctusegs m' lo (bv_unsigned sp)
               /\ rw_cells ctusegs m' PP [C8 (wz (P + der_hl len + len))]
               /\ (exists hb, rw_cells ctusegs m' P [CB (Z.to_nat (der_hl len)) hb]) /\ rw_cells ctusegs m' (P + der_hl len) [CB (Z.to_nat len) src])
    (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 a0 a1 a2 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
        F (wz ASN1_I2D_EX_PRIMITIVE) fc None m (seg_rom ctusegs)).
Proof.
  intros until j2. intros ST MI GLO LO IT PVlo PVhi PPlo PPhi A0 ALO LEN D0 DLO FLR P0 PLO SEP SEPA PBND SP16 PV8 A8 HPV HS SRC SLEN PP8 HPP HP1 HP2 -> -> -> -> ->.
  change (frozen (D + len <= P \/ P + der_hl len + len <= D)) in SEP. change (frozen (A + ASN1_STRING_SIZE <= P \/ P + der_hl len + len <= A)) in SEPA.
  change (frozen (P + der_hl len + len <= 0x10000 \/ 0x355000 <= P)) in PBND.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (der_hl_range len ltac:(lia)) as HLR. unfold EX_PRIM_STACK in LO.
  eapply ex_prim_fwd with (out := PP) (PVAL := PVAL) (A := A) (len := len) (D := D) (fl := fl) (lo := lo); try eassumption; try reflexivity; try lia.
  intros m1 x1 x5 x6 x7 x10 x11 x12 x13 x14 x15 x16 x17 x28 x29 x30 x31 junk MU WM MI1 ST1 FR. unfold EX_PRIM_STACK, GLOBALS_TOP, MallocRep.wz in *.
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HPP; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HP1; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU WM) in HP2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU) in HPV; [| cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU) in HS; [| unfold asn1_string_cells; cbn; unfold ASN1_STRING_SIZE in ALO; lia].
  assert (IT1 : item_oct m1) by (eapply item_oct_agree; [exact IT| exact MU| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]).
  (* [comment removed for export] *)
  zstep. sfalse. zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep. zstep. bnot. zstep. zstep. zstep. zstep. zstep. zstep.
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia).
  eapply evt_cut.
  { eapply ASN1_put_object_spec with (lo := lo) (len := len) (PP := PP) (P := P) (junk := j1); rewrite ?ESP; try eassumption; try reflexivity; lia. }
  cbv beta. intros ms2 PO.
  destruct PO as (q5 & q6 & q7 & q11 & q12 & q13 & q14 & q15 & q16 & q17 & q28 & q29 & q30 & q31 & m2 & -> & MU2 & WM2 & MI2 & ST2 & HPP2 & HP12). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x116194)) with (Z_to_bv 64 0x116194) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU2 WM2) in HP2; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU2) in HPV; [| cbn; lia].
  apply (fun H => ro_cells_transport _ _ _ _ _ _ H MU2) in HS; [| unfold asn1_string_cells; cbn; pose proof SEPA as SEPA'; unfold frozen, ASN1_STRING_SIZE in SEPA', ALO; lia].
  apply (fun H => bytes_at_transport _ _ _ _ _ _ H MU2) in SRC; [| rewrite SLEN, Z2Nat.id by lia; cbn; pose proof SEP as SEP'; unfold frozen in SEP'; lia].
  assert (ST2' : stk ctusegs m2 lo (bv_unsigned sp + -96)) by exact ST2.
  assert (IT2 : item_oct m2).
  { pose proof PBND as PBND'. unfold frozen in PBND'.
    eapply item_oct_agree; [exact IT1| exact MU2| constructor; [cbn; unfold ITEM_OCTET; lia| constructor; [cbn; unfold ITEM_OCTET; lia| constructor; [cbn; unfold ITEM_OCTET; lia| constructor]]]]. }
  assert (MU' : munch [(bv_unsigned sp + -144, bv_unsigned sp); (P, P + der_hl len + len); (PP, PP + 8)]%Z m m2).
  { eapply munch_trans; [eapply munch_weaken; [| exact MU]| eapply munch_weaken; [| exact MU2]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m2) by (eapply wmono_trans; [exact WM| exact WM2]).
  clear MU WM MU2 WM2 ST1 MI1 IT1 HPP HP1. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. zstep. zstep. zstep.
  pose proof (cells_pick m2 (bv_unsigned sp + -96) 4 [CB 4%nat _] (C4 (Z_to_bv 64 4)) _ FR eq_refl) as HPU.
  eapply evt_cut.
  { eapply asn1_ex_i2c_write_spec with (lo := lo) (PVAL := PVAL) (PUT := bv_unsigned sp + -96 + 4) (A := A) (len := len) (D := D) (fl := fl) (C := P + der_hl len) (src := src) (junk := j2);
      rewrite ?ESP; try eassumption; try reflexivity; try (unfold ITEM_OCTET, V_ASN1_OCTET_STRING, GLOBALS_TOP, ASN1_STRING_SIZE, MallocRep.wz; first [lia | reflexivity | f_equal; lia]).
    pose proof SEP as SEP'. unfold frozen in SEP'. lia.
    clear - SP16; ulia_open; Z.div_mod_to_equations; lia. }
  cbv beta. intros ms3 PO.
  destruct PO as (p5 & p6 & p7 & p11 & p12 & p13 & p14 & p15 & p16 & p17 & p28 & p29 & p30 & p31 & m3 & -> & MU3 & WM3 & MI3 & ST3 & HP23). rewrite ESP in *.
  replace (ret_pc (Z_to_bv 64 0x1161b0)) with (Z_to_bv 64 0x1161b0) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in FR; [| cbn; lia].
  apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in HPP2; [| cbn; lia].
  destruct HP12 as [hb HP12]. apply (fun H => rw_cells_transport _ _ _ _ _ _ H MU3 WM3) in HP12; [| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
  assert (MU' : munch [(bv_unsigned sp + -144, bv_unsigned sp); (P, P + der_hl len + len); (PP, PP + 8)]%Z m m3).
  { eapply munch_trans; [exact MU| eapply munch_weaken; [| exact MU3]]; unfold sub_fp; cbn [outside]; intros y Hy; lia. }
  assert (WM' : wmono ctusegs m m3) by (eapply wmono_trans; [exact WM| exact WM3]).
  clear MU WM MU3 WM3 ST2 ST2' MI2 IT2 HPU HS HPV SRC. rename MU' into MU. rename WM' into WM.
  (* [comment removed for export] *)
  zstep. zstep. strue. zstep. zstep. zstep. zstep.
  eapply evt_mono; [eapply ex_prim_tail with (m0 := m); try eassumption; try lia; unfold sub_fp; cbn [outside]; intros y Hy; lia|].
  cbv beta. intros ms' (u0 & u1 & u2 & u3 & u4 & u5 & u6 & u7 & u8 & u9 & u10 & u11 & u12 & u13 & m' & -> & MU' & WM' & MI' & ST' & MU4 & WM4).
  do 14 eexists. eexists. split; [reflexivity|]. split; [exact MU'|]. split; [exact WM'|]. split; [exact MI'|]. split; [exact ST'|].
  split; [eapply rw_cells_transport; [eassumption| exact MU4| exact WM4| cbn; lia]|].
  split; [exists hb; eapply rw_cells_transport; [exact HP12| exact MU4| exact WM4| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia]|].
  eapply rw_cells_transport; [exact HP23| exact MU4| exact WM4| cbn [cells_size csize]; rewrite Nat.add_0_r, Z2Nat.id by lia; cbn; lia].
Qed.

(* [comment removed for export] *)
(* [comment removed for export] *)
(* [comment removed for export] *)
Lemma ASN1_item_ex_i2d_fwd : forall (P : machine_state -> Prop)
    (ra sp gp tp t0 t1 t2 s0 s1 a1 a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6 : word)
    (F : bvmap 5 word) fc (m : mem) (lo PVAL : Z),
  stk ctusegs m lo (bv_unsigned sp) -> mem_inv ctusegs m -> GLOBALS_TOP <= lo -> lo <= bv_unsigned sp - 128 -> item_oct m ->
  0 <= PVAL < 2^64 ->
  (forall m1, munch [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m m1 -> wmono ctusegs m m1 -> mem_inv ctusegs m1 ->
              stk ctusegs m1 lo (bv_unsigned sp) ->
              evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PVAL) a1 (wz ITEM_OCTET) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                                F (wz ASN1_I2D_EX_PRIMITIVE) fc None m1 (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR ra sp gp tp t0 t1 t2 s0 s1 (wz PVAL) a1 (wz ITEM_OCTET) a3 a4 a5 a6 a7 s2 s3 s4 s5 s6 s7 s8 s9 s10 s11 t3 t4 t5 t6)
                    F (wz ASN1_ITEM_EX_I2D) fc None m (seg_rom ctusegs)).
Proof.
  intros until PVAL. intros ST MI GLO LO IT PVR K.
  unfold GLOBALS_TOP in GLO. unfold ASN1_ITEM_EX_I2D, ASN1_I2D_EX_PRIMITIVE, MallocRep.wz in *.
  pose proof IT as ((I1 & I2 & I3 & I4 & I5) & I6). unfold ITEM_OCTET in *. lit_addr I2. lit_addr I3. lit_addr I4. lit_addr I5. lit_addr I6.
  pose proof (bv_unsigned_in_range 64 sp) as SPR. unfold bv_modulus in SPR. cbn in SPR.
  assert (LO0 : 0 <= lo) by (destruct ST as [? _]; assumption).
  pose proof (munch_refl [(bv_unsigned sp - 128, bv_unsigned sp)]%Z m) as MU. pose proof (wmono_refl ctusegs m) as WM.
  carve_frame 128%nat ST. do 15 zstep.
  (* [comment removed for export] *)
  do 4 zstep. zstep. zstep. zstep. btaken. zstep. zstep. btaken.
  do 5 zstep. do 13 zstep. zstep. release_frame FR ST (bv_unsigned sp). zstep.
  lazymatch goal with |- evt _ _ (MS _ _ _ _ _ ?mx _) => apply (K mx MU WM ltac:(assumption) ST) end.
Qed.
End WithCeiling0.
