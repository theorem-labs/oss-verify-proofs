(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 *)
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtLib Require Import ImageCt.
(* [comment removed for export] *)
From Stdlib Require Import ZArith List Lia Bool.
From stdpp Require Import gmap.
From LinuxProcessSemantics.LinuxProcessSem Require Import BvBase RiscvSemantics MemImageType State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Fpu Sem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Tac Image ZBridge SysStep ITree Nodes Decode Arr FP Frame Cells Step Mem.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Malloc Require Import MallocRep.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SCT_PRINT : Z := 0x19d8bc.
(* [comment removed for export] *)
Definition SCT_PRINT_NV1_STACK : Z := 96 + HX_STACK.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section SPN. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp tp : word) (F : bvmap 5 word) (m0 : mem) (lo out pv : Z) (canary : word).
(* [comment removed for export] *)
Variables (A ver SB sbn : Z) (sbs : list byte).
Variables (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word).

Hypothesis GLO : 3493888 <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 6752.
Hypothesis SP63 : bv_unsigned sp < 2^63.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis OB : 0 < out /\ out + 128 <= lo /\ (out + 128 <= 65536 \/ 3493888 <= out).
Hypothesis OAL : out mod 8 = 0.
Hypothesis HA : 0 < A /\ A + 104 <= lo /\ (A + 104 <= out \/ out + 128 <= A).   (* [comment removed for export] *)
Hypothesis AAL : A mod 8 = 0.
Hypothesis HVER : -2^31 <= ver < 2^31 /\ ver <> 0.
Hypothesis SBN : Z.of_nat (length sbs) = sbn /\ 0 <= sbn < 2^31.
Hypothesis SBR : 0 < sbn -> 0 < SB /\ SB + sbn <= lo /\ (SB + sbn <= out \/ out + 128 <= SB).
Hypothesis SBW : 0 <= SB < 2^64.

Definition W0 : list (Z * Z) := [(lo, bv_unsigned sp); (out, out + 128)].
Definition sp_hi : list cell := [C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra].
(* [comment removed for export] *)
Definition sct_nv1_cells (m : mem) : Prop :=
  ro_cells ctusegs m A [C4 (Z_to_bv 64 ver)] /\ ro_cells ctusegs m (A + 8) [C8 (Z_to_bv 64 SB); C4 (Z_to_bv 64 sbn)].
Definition sp_inv (clo : list cell) (m : mem) : Prop :=
  mem_inv ctusegs m /\ stk ctusegs m lo (bv_unsigned sp + -96) /\ ssp_cells m canary /\ null_meth_cells m /\ (0 < sbn -> bytes_at ctusegs m SB sbs)
  /\ munch W0 m0 m /\ wmono ctusegs m0 m /\ rw_cells ctusegs m (bv_unsigned sp + -64) sp_hi
  /\ rw_cells ctusegs m (bv_unsigned sp + -96) clo /\ cells_size clo = 32%nat /\ sct_nv1_cells m.
Definition sp_bio (m : mem) (nw : Z) : Prop := 0 <= nw < 2^64 /\ rw_cells ctusegs m out (bio_null_cells NULL_METHOD pv nw).
Definition sp_F (Fc : bvmap 5 word) : Prop := forall k : reg, bv_unsigned k <> 10 -> reg_get Fc k = reg_get F k.

Local Ltac open_inv H :=
  destruct H as (MI & ST & [SSP1 SSP2] & [NMa NMb] & HS & MU & WM & FRH & FRL & SZ & [SC0 SC1]); unfold got_ssp, ssp_guard in SSP1, SSP2; unfold NULL_METHOD in NMa, NMb.
Local Ltac facts :=
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia);
  assert (SEPB : out + 128 <= lo \/ bv_unsigned sp <= out) by lia;
  assert (SEPA : A + 104 <= lo \/ bv_unsigned sp <= A) by lia;
  assert (SEPM : 2978032 + 72 <= lo \/ bv_unsigned sp <= 2978032) by lia;
  assert (SEPG : 3271976 + 8 <= lo \/ bv_unsigned sp <= 3271976) by lia;
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.

(* [comment removed for export] *)
Lemma wrap64_zero : forall v, -2^63 < v < 2^63 -> bv_unsigned (Z_to_bv 64 v) = 0 -> v = 0.
Proof.
  intros v Hv E. rewrite Z_to_bv_unsigned in E. unfold bv_wrap, bv_modulus in E. change (2 ^ Z.of_N 64) with (2^64) in E.
  destruct (Z.lt_ge_cases v 0).
  - replace v with ((v + 2^64) + (-1) * 2^64) in E by lia. rewrite Z.mod_add in E by lia. rewrite Z.mod_small in E by lia. lia.
  - rewrite Z.mod_small in E by lia. lia.
Qed.

(* [comment removed for export] *)
Lemma sp_call : forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell) (AF : Z) (fmt : list Z) (args : list parg) (o : list Z) (retpc : Z)
    (P : machine_state -> Prop),
  sp_inv clo m -> sp_bio m nw -> frm0 fc -> sp_F Fc ->
  printf_call_ok m lo (bv_unsigned sp + -96) AF fmt [a2; a3; a4; a5; a6; a7] args o ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 AF -> x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     sp_inv clo m' -> sp_bio m' ((nw + zlength o) mod 2^64) -> frm0 fc' -> sp_F Fc' ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                        Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                   Fc (Z_to_bv 64 BIO_PRINTF) fc None m (seg_rom ctusegs)).
Proof using GLO HA LO OAL OB SBN SBR SBW SP16 SP63.
  intros until P. intros INV [NW HB] FRM HFC PC -> -> -> Hret EVEN K. pose proof INV as INV'. open_inv INV. facts.
  eapply evt_cut.
  { eapply (BIO_printf_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc _ out pv nw AF lo canary);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold BIO_PRINTF_STACK, VSN_DEPTH; lia| rewrite ESP; lia
      | rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia
      | split; [exact SSP1| exact SSP2]| exact FRM
      | exact HB| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| exact OAL| exact NW| split; [exact NMa| exact NMb]
      | rewrite ESP; exact PC| reflexivity| reflexivity]. }
  cbv beta. unfold bio_printf_post. intros ms' (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & -> & MU2 & WM2 & MI2 & FRM2 & FREG2 & ST2 & SSP2' & HB2).
  rewrite ?ESP in *.
  replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| exact EVEN]).
  clear ST HB. unfold W0 in MU. unfold sp_hi in FRH. transport_after_call ctusegs m m2 MU2 WM2.
  apply K.
  - split; [exact MI2|]. split; [exact ST2|]. split; [exact SSP2'|]. split; [split; [exact NMa| exact NMb]|].
    split. { intros Hn. eapply bytes_at_transport; [exact (HS Hn)| exact MU2|]. cbn [disjoint_from]. pose proof (SBR Hn). lia. } split; [exact MU|]. split; [exact WM|]. split; [exact FRH|]. split; [exact FRL|]. split; [exact SZ|]. split; [exact SC0| exact SC1].
  - split; [| rewrite bio_null_cells_mod; exact HB2]. apply Z.mod_pos_bound. lia.
  - exact FRM2.
  - intros k Hk. rewrite (FREG2 k Hk). apply HFC. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma sct_print_nv1 : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (nw : Z),
  stk ctusegs m0 lo (bv_unsigned sp) -> mem_inv ctusegs m0 -> ssp_cells m0 canary -> frm0 fc ->
  rw_cells ctusegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 -> null_meth_cells m0 ->
  (0 < sbn -> bytes_at ctusegs m0 SB sbs) -> sct_nv1_cells m0 ->
  evt ctusegs (hexstring_post vra sp gp tp v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 F lo out pv canary m0)
    (MS (mkR vra sp gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 A) (Z_to_bv 64 out) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_PRINT) fc None m0 (seg_rom ctusegs)).
Proof using CE__ RN__ AAL GLO HA HVER LO OAL OB SBN SBR SBW SP16 SP63.
  intros until nw. intros ST MI [SSP1 SSP2] FRM HB NW [NMa NMb] HS [SC0 SC1].
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold NULL_METHOD in NMa, NMb. unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  facts. unfold SCT_PRINT.
  pose proof (munch_refl W0 m0) as MU. unfold W0 in MU. pose proof (wmono_refl ctusegs m0) as WM.
  assert (HFC : sp_F F) by (intros k Hk; reflexivity).
  (* [comment removed for export] *)
  carve_frame 96%nat ST. zstep. do 8 zstep. zstep. zstep. zstep. zstep. zstep.
  (* [comment removed for export] *)
  zstep. try (if_cases K0; zify_cond K0; [| exfalso; rewrite ?unsigned_lit in K0 by lia; lia]). zstep.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  name_mem m1.
  lazymatch goal with FR : rw_cells _ m1 (bv_unsigned sp + -96) (?c0 :: ?rest) |- _ =>
    pose proof (proj1 (rw_cells_app m1 _ [c0] rest) FR) as [FRL FRH]; clear FR end.
  cbn [cells_size csize Nat.add] in FRH. replace (bv_unsigned sp + -96 + Z.of_nat 32) with (bv_unsigned sp + -64) in FRH by lia.
  lazymatch type of FRL with rw_cells _ _ _ ?clo =>
  eapply (sp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 nw clo A_C1 FMT_C1 [PA_i 4; PA_s []] O_C1 0x19d938);
    [ | split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| exact FRM| exact HFC
    | apply pcok_C1; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ] end.
  { split; [exact MI|]. split; [exact ST|]. split; [split; [exact SSP1| exact SSP2]|]. split; [split; [exact NMa| exact NMb]|].
    split. { intros Hn. eapply bytes_at_transport; [exact (HS Hn)| exact MU|]. cbn [disjoint_from]. pose proof (SBR Hn). lia. }
    split; [exact MU|]. split; [exact WM|]. split; [exact FRH|]. split; [exact FRL|]. split; [reflexivity|]. split; [exact SC0| exact SC1]. }
  clear MI ST SSP1 SSP2 NMa NMb HS MU WM FRH FRL SC0 SC1 HB ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m1.
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fc2 fc2 m2 INV2 BIO2 FRM2 HFC2.
  pose proof INV2 as INV2'. open_inv INV2. facts.
  (* [comment removed for export] *)
  ub. zstep.
  do 5 zstep. zstep.
  eapply (sp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc2 fc2 m2 _ _ A_C2 FMT_C2 [PA_i 8; PA_s []] O_C2 0x19d95c);
    [exact INV2'| exact BIO2| exact FRM2| exact HFC2
    | apply pcok_C2; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST SSP1 SSP2 NMa NMb HS MU WM FRH FRL SZ SC0 SC1 INV2' BIO2 FRM2 HFC2 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m2.
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m3 INV3 BIO3 FRM3 HFC3.
  pose proof INV3 as INV3'. open_inv INV3. facts.
  (* [comment removed for export] *)
  zstep. if_cases C0; [exfalso; zify_cond C0; lia| clear C0].
  zstep. if_cases CA; [exfalso; zify_cond CA; revert CA; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - AAL; intros CA; Z.div_mod_to_equations; lia| clear CA].
  zstep. zstep. if_cases K1; zify_cond K1. { exfalso. rewrite sx32_lit in K1 by lia. apply wrap64_zero in K1; lia. } try clear K1.
  (* [comment removed for export] *)
  ub. zstep.
  do 5 zstep. zstep.
  eapply (sp_call _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m3 _ _ A_C3 FMT_C3 [PA_i 20; PA_s []] O_C3 0x19d990);
    [exact INV3'| exact BIO3| exact FRM3| exact HFC3
    | apply pcok_C3; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST SSP1 SSP2 NMa NMb HS MU WM FRH FRL SZ SC0 SC1 INV3' BIO3 FRM3 HFC3 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m3.
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fc4 fc4 m4 INV4 [NW4 HB4] FRM4 HFC4.
  open_inv INV4. facts. unfold sp_hi in FRH.
  (* [comment removed for export] *)
  zstep. zstep. try rewrite (swrap32_small sbn) by lia. zstep. zstep. zstep.
  (* [comment removed for export] *)
  do 8 zstep.
  lazymatch type of FRL with rw_cells _ _ _ ?clo =>
  assert (FR : rw_cells ctusegs m4 (bv_unsigned sp + -96) (clo ++ [C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra]))
    by (apply rw_cells_app; split; [exact FRL|]; rewrite SZ; replace (bv_unsigned sp + -96 + Z.of_nat 32) with (bv_unsigned sp + -64) by lia; exact FRH) end.
  clear FRL FRH.
  zstep.
  eapply stk_release in FR; [| exact ST| lia]. clear ST. rename FR into ST.
  rewrite cells_size_app, SZ in ST. cbn [cells_size csize Nat.add] in ST.
  replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in ST by lia.
  (* [comment removed for export] *)
  zstep.
  eapply evt_cut.
  { eapply (BIO_hex_string_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc4 fc4 m4 out pv _ SB sbn lo canary sbs);
      [exact ST| exact MI| unfold GLOBALS_TOP; lia| unfold HX_STACK; lia| lia| first [exact SP16| clear - SP16; Z.div_mod_to_equations; lia]| split; [exact SSP1| exact SSP2]| exact FRM4
      | rewrite bio_null_cells_mod; exact HB4| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| exact OAL| apply Z.mod_pos_bound; lia| split; [exact NMa| exact NMb]
      | destruct (Z.lt_ge_cases 0 sbn) as [Hn|Hn]; [exact (HS Hn)| assert (sbs = []) as -> by (destruct sbs; [reflexivity| cbn [length] in SBN; lia]); split; [lia| split; [cbn [length]; lia| intros i Hi; cbn [length] in Hi; lia]]]
      | lia| lia| exact SBR
      | reflexivity| f_equal; lia| reflexivity| reflexivity| first [reflexivity| apply sx32_lit; lia] ]. }
  cbv beta. unfold hexstring_post. intros ms' (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & F5 & fc5 & m5 & nw5 & -> & MU5 & WM5 & MI5 & FRM5 & FREG5 & ST5 & SSP5 & HB5 & NW5).
  apply evt_done.
  do 14 eexists. exists F5, fc5, m5, nw5. split; [reflexivity|].
  split; [eapply munch_trans; [exact MU| exact MU5]|]. split; [eapply wmono_trans; [exact WM| exact WM5]|]. split; [exact MI5|].
  split; [exact FRM5|]. split; [intros k Hk; rewrite (FREG5 k Hk); apply HFC4; exact Hk|].
  split; [exact ST5|]. split; [exact SSP5|]. split; [exact HB5| exact NW5].
Qed.
End SPN.
