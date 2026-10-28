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
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string W_sct_print_nv1.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApUTac.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

(* [comment removed for export] *)
Definition SCT_PRINT_TS : Z := 0x19da64.
Definition SCT_PRINT_TAIL : Z := 0x19db1c.
(* [comment removed for export] *)
Definition SCT_PRINT_SEG_STACK : Z := 96 + HX_STACK.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section SPV. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp tp : word) (F : bvmap 5 word) (m0 : mem) (lo out pv : Z) (canary : word).
(* [comment removed for export] *)
Variables (A LI lin ts EX exn hsh sga SG sgn : Z) (lib exb sgb : list byte).
(* [comment removed for export] *)
Variables (vra v8 v9 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 : word).

Hypothesis GLO : 3493888 <= lo.
Hypothesis LO : lo <= bv_unsigned sp - 6752.
Hypothesis SP63 : bv_unsigned sp < 2^63.
Hypothesis SP16 : bv_unsigned sp mod 16 = 0.
Hypothesis OB : 0 < out /\ out + 128 <= lo /\ (out + 128 <= 65536 \/ 3493888 <= out).
Hypothesis OAL : out mod 8 = 0.
Hypothesis HA : 0 < A /\ A + 104 <= lo /\ (A + 104 <= out \/ out + 128 <= A).
Hypothesis AAL : A mod 8 = 0.
Hypothesis LIN : Z.of_nat (length lib) = lin /\ 0 <= lin < 2^31.
(* [comment removed for export] *)
Hypothesis LIR : frozen (0 < lin -> 0 < LI /\ LI + lin <= lo /\ (LI + lin <= out \/ out + 128 <= LI)).
Hypothesis LIW : 0 <= LI < 2^64.
Hypothesis EXN : Z.of_nat (length exb) = exn /\ 0 <= exn < 2^31.
Hypothesis EXR : frozen (0 < exn -> 0 < EX /\ EX + exn <= lo /\ (EX + exn <= out \/ out + 128 <= EX)).
Hypothesis EXW : 0 <= EX < 2^64.
Hypothesis SGN : Z.of_nat (length sgb) = sgn /\ 0 <= sgn < 2^31.
Hypothesis SGR : frozen (0 < sgn -> 0 < SG /\ SG + sgn <= lo /\ (SG + sgn <= out \/ out + 128 <= SG)).
Hypothesis SGW : 0 <= SG < 2^64.
Hypothesis TSW : 0 <= ts < 2^64.
Hypothesis HSH : 0 <= hsh < 256.
Hypothesis SGA : 0 <= sga < 256.

Definition pv_hi : list cell := [C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra].
(* [comment removed for export] *)
Definition sct_v1_cells (m : mem) : Prop :=
  ro_cells ctusegs m A [C4 (Z_to_bv 64 0)]
  /\ ro_cells ctusegs m (A + 24) [C8 (Z_to_bv 64 LI); C4 (Z_to_bv 64 lin)]
  /\ ro_cells ctusegs m (A + 40) [C8 (Z_to_bv 64 ts); C8 (Z_to_bv 64 EX); C8 (Z_to_bv 64 exn)]
  /\ ro_cells ctusegs m (A + 64) [C1 (Z_to_bv 8 hsh); C1 (Z_to_bv 8 sga)]
  /\ ro_cells ctusegs m (A + 72) [C8 (Z_to_bv 64 SG); C4 (Z_to_bv 64 sgn)].
Definition pv_arrays (m : mem) : Prop :=
  (0 < lin -> bytes_at ctusegs m LI lib) /\ (0 < exn -> bytes_at ctusegs m EX exb) /\ (0 < sgn -> bytes_at ctusegs m SG sgb).
(* [comment removed for export] *)
Definition pv_static (m : mem) : Prop := ssp_cells m canary /\ null_meth_cells m /\ pv_arrays m /\ sct_v1_cells m /\ ap_img m.
(* [comment removed for export] *)
Definition pv_inv (clo : list cell) (m : mem) : Prop :=
  mem_inv ctusegs m /\ stk ctusegs m lo (bv_unsigned sp + -96) /\ pv_static m
  /\ munch (W0 sp lo out) m0 m /\ wmono ctusegs m0 m /\ rw_cells ctusegs m (bv_unsigned sp + -64) pv_hi
  /\ rw_cells ctusegs m (bv_unsigned sp + -96) clo /\ cells_size clo = 32%nat.

Local Ltac open_inv H := destruct H as (MI & ST & PS & MU & WM & FRH & FRL & SZ).
Local Ltac open_static PS :=
  destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG);
  unfold got_ssp, ssp_guard in SSP1, SSP2; unfold NULL_METHOD in NMa, NMb.
Local Ltac facts :=
  pose proof (bv_unsigned_in_range 64 sp) as SPR; unfold bv_modulus in SPR; cbn in SPR;
  assert (ESP : bv_unsigned (Z_to_bv 64 (bv_unsigned sp + -96)) = bv_unsigned sp + -96) by (apply unsigned_lit; lia);
  assert (SEPB : out + 128 <= lo \/ bv_unsigned sp <= out) by lia;
  assert (SEPA : A + 104 <= lo \/ bv_unsigned sp <= A) by lia;
  assert (SEPM : 2978032 + 72 <= lo \/ bv_unsigned sp <= 2978032) by lia;
  assert (SEPG : 3271976 + 8 <= lo \/ bv_unsigned sp <= 3271976) by lia;
  assert (SEPC : 3486312 + 8 <= lo \/ bv_unsigned sp <= 3486312) by lia.
Local Ltac close_inv MI ST PS MU WM FRH FRL SZ :=
  split; [exact MI|]; split; [exact ST|]; split; [exact PS|];
  split; [exact MU|]; split; [exact WM|]; split; [exact FRH|]; split; [exact FRL|]; first [exact SZ| reflexivity].

(* [comment removed for export] *)
Lemma pv_static_transport : forall m m' q, pv_static m -> munch [(lo, q); (out, out + 128)] m m' -> wmono ctusegs m m' -> lo <= q -> pv_static m'.
Proof using GLO OB HA LIN LIR LIW EXN EXR EXW SGN SGR SGW TSW HSH SGA. try clear SP16 OAL LO SP63 AAL.
  intros m m' q ([S1 S2] & [N1 N2] & (H1 & H2 & H3) & (C0 & C1 & C2 & C4 & C3) & IMG) MU WM LQ.
  unfold got_ssp, ssp_guard in S1, S2. unfold NULL_METHOD in N1, N2.
  split; [| split; [| split; [| split]]].
  - unfold ssp_cells, got_ssp, ssp_guard. split; (eapply rw_cells_transport; [eassumption| exact MU| exact WM|]); cbn [disjoint_from cells_size csize Nat.add]; lia.
  - unfold null_meth_cells, NULL_METHOD. split; (eapply ro_cells_transport; [eassumption| exact MU|]); cbn [disjoint_from cells_size csize Nat.add]; lia.
  - split; [| split]; intros Hn.
    + eapply bytes_at_transport; [exact (H1 Hn)| exact MU|]. cbn [disjoint_from]. pose proof (LIR Hn). lia.
    + eapply bytes_at_transport; [exact (H2 Hn)| exact MU|]. cbn [disjoint_from]. pose proof (EXR Hn). lia.
    + eapply bytes_at_transport; [exact (H3 Hn)| exact MU|]. cbn [disjoint_from]. pose proof (SGR Hn). lia.
  - split; [| split; [| split; [| split]]]; (eapply ro_cells_transport; [eassumption| exact MU|]); cbn [disjoint_from cells_size csize Nat.add]; lia.
  - intros a Ha. rewrite <- (IMG a Ha). unfold mrd. rewrite (MU (wa a)); [reflexivity|]. unfold wa. unfold IMG_LO, IMG_HI in Ha. rewrite unsigned_lit by lia. cbn. lia.
Qed.

(* [comment removed for export] *)
Lemma sp_callv : forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell) (AF : Z) (fmt : list Z) (args : list parg) (o : list Z) (retpc : Z)
    (P : machine_state -> Prop),
  pv_inv clo m -> sp_bio out pv m nw -> frm0 fc -> sp_F F Fc ->
  printf_call_ok m lo (bv_unsigned sp + -96) AF fmt [a2; a3; a4; a5; a6; a7] args o ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 AF -> x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem),
     pv_inv clo m' -> sp_bio out pv m' ((nw + zlength o) mod 2^64) -> frm0 fc' -> sp_F F Fc' ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 (zlength o)) a1' a2' a3' a4' a5' a6' a7'
                             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                        Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                   Fc (Z_to_bv 64 BIO_PRINTF) fc None m (seg_rom ctusegs)).
Proof using EXN EXR EXW GLO HA HSH LIN LIR LIW LO OAL OB SGA SGN SGR SGW SP16 SP63 TSW.
  intros until P. intros INV [NW HB] FRM HFC PC -> -> -> Hret EVEN K. pose proof INV as INV'. open_inv INV. pose proof PS as PS0. open_static PS. facts.
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
  pose proof (pv_static_transport m m2 _ PS0 MU2 WM2 ltac:(lia)) as PS2.
  clear ST HB HS1 HS2 HS3 SSP1 SSP2 NMa NMb SC0 SC1 SC2 SC4 SC3 IMG PS0. unfold W0 in MU. unfold pv_hi in FRH. transport_after_call ctusegs m m2 MU2 WM2.
  apply K.
  - close_inv MI2 ST2 PS2 MU WM FRH FRL SZ.
  - split; [| rewrite bio_null_cells_mod; exact HB2]. apply Z.mod_pos_bound. lia.
  - exact FRM2.
  - intros k Hk. rewrite (FREG2 k Hk). apply HFC. exact Hk.
Qed.

(* [comment removed for export] *)
Lemma hx_callv : forall (x1 t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6 : word)
    (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell) (S len : Z) (bs : list byte) (retpc : Z)
    (P : machine_state -> Prop),
  pv_inv clo m -> sp_bio out pv m nw -> frm0 fc -> sp_F F Fc ->
  (0 < len -> bytes_at ctusegs m S bs) -> Z.of_nat (length bs) = len -> 0 <= len < 2^31 -> 0 <= S < 2^64 ->
  (0 < len -> 0 < S /\ S + len <= lo /\ (S + len <= out \/ out + 128 <= S)) ->
  a0 = Z_to_bv 64 out -> a1 = Z_to_bv 64 20 -> a2 = Z_to_bv 64 16 -> a3 = Z_to_bv 64 S -> a4 = Z_to_bv 64 len ->
  x1 = Z_to_bv 64 retpc -> 0 <= retpc < 2^64 -> retpc mod 2 = 0 ->
  (forall (t0' t1' t2' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc' : bvmap 5 word) (fc' : bv 32) (m' : mem) (nw' : Z),
     pv_inv clo m' -> sp_bio out pv m' nw' -> frm0 fc' -> sp_F F Fc' ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' x8 x9 (Z_to_bv 64 1) a1' a2' a3' a4' a5' a6' a7'
                             x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3' t4' t5' t6')
                        Fc' (Z_to_bv 64 retpc) fc' None m' (seg_rom ctusegs))) ->
  evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 x8 x9 a0 a1 a2 a3 a4 a5 a6 a7 x18 x19 x20 x21 x22 x23 x24 x25 x26 x27 t3 t4 t5 t6)
                   Fc (Z_to_bv 64 BIO_HEX_STRING) fc None m (seg_rom ctusegs)).
Proof using CE__ EXN EXR EXW GLO HA HSH LIN LIR LIW LO OAL OB RN__ SGA SGN SGR SGW SP16 SP63 TSW.
  intros until P. intros INV [NW HB] FRM HFC HS LEN LENR SW SR -> -> -> -> -> -> Hret EVEN K. pose proof INV as INV'. open_inv INV. pose proof PS as PS0. open_static PS. facts.
  eapply evt_cut.
  { eapply (BIO_hex_string_null_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m out pv nw S len lo canary bs);
      [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; unfold HX_STACK; lia| rewrite ESP; lia| rewrite ESP; clear - SP16; Z.div_mod_to_equations; lia| split; [exact SSP1| exact SSP2]| exact FRM
      | exact HB| unfold obj_range, BIO_SIZE, GLOBALS_TOP; lia| exact OAL| exact NW| split; [exact NMa| exact NMb]
      | destruct (Z.lt_ge_cases 0 len) as [Hn|Hn]; [exact (HS Hn)| assert (bs = []) as -> by (destruct bs; [reflexivity| cbn [length] in LEN; lia]); split; [lia| split; [cbn [length]; lia| intros i Hi; cbn [length] in Hi; lia]]]
      | exact LEN| exact LENR| exact SR
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity]. }
  cbv beta. unfold hexstring_post. intros ms' (u0 & u1 & u2 & w1 & w2 & w3 & w4 & w5 & w6 & w7 & u3 & u4 & u5 & u6 & F2 & fc2 & m2 & nw2 & -> & MU2 & WM2 & MI2 & FRM2 & FREG2 & ST2 & SSP2' & HB2 & NW2).
  rewrite ?ESP in *.
  replace (ret_pc (Z_to_bv 64 retpc)) with (Z_to_bv 64 retpc) by (symmetry; apply ret_pc_even; [lia| exact EVEN]).
  pose proof (pv_static_transport m m2 _ PS0 MU2 WM2 ltac:(lia)) as PS2.
  clear ST HB HS1 HS2 HS3 HS SSP1 SSP2 NMa NMb SC0 SC1 SC2 SC4 SC3 IMG PS0. unfold W0 in MU. unfold pv_hi in FRH. transport_after_call ctusegs m m2 MU2 WM2.
  apply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ F2 fc2 m2 nw2).
  - close_inv MI2 ST2 PS2 MU WM FRH FRL SZ.
  - split; [exact NW2| exact HB2].
  - exact FRM2.
  - intros k Hk. rewrite (FREG2 k Hk). apply HFC. exact Hk.
Qed.




(* [comment removed for export] *)
Local Ltac static_now PS0 MU WM :=
  let PS := fresh "PS" in
  pose proof (pv_static_transport _ _ _ PS0 MU WM ltac:(lia)) as PS;
  destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG);
  unfold got_ssp, ssp_guard in SSP1, SSP2; unfold NULL_METHOD in NMa, NMb.

(* [comment removed for export] *)
Lemma seg_A : forall (t0 t1 t2 a4 a5 a6 a7 t3 t4 t5 t6 : word) (fc : bv 32) (nw : Z) (P : machine_state -> Prop),
  stk ctusegs m0 lo (bv_unsigned sp) -> mem_inv ctusegs m0 -> frm0 fc ->
  rw_cells ctusegs m0 out (bio_null_cells NULL_METHOD pv nw) -> 0 <= nw < 2^64 -> pv_static m0 ->
  (forall (x1 t0' t1' t2' a0' a1' a2' a3' a4' a5' a6' a7' t3' t4' t5' t6' : word) (Fc : bvmap 5 word) (fc' : bv 32) (m1 : mem) (nw1 : Z) (clo : list cell),
     pv_inv clo m1 -> sp_bio out pv m1 nw1 -> frm0 fc' -> sp_F F Fc ->
     evt ctusegs P (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0' t1' t2' sp (Z_to_bv 64 out) a0' a1' a2' a3' a4' a5' a6' a7'
                             (Z_to_bv 64 A) (Z_to_bv 64 8) (Z_to_bv 64 20) (Z_to_bv 64 4) (Z_to_bv 64 ts) v23 v24 v25 v26 v27 t3' t4' t5' t6')
                        Fc (Z_to_bv 64 SCT_PRINT_TS) fc' None m1 (seg_rom ctusegs))) ->
  evt ctusegs P
    (MS (mkR vra sp gp tp t0 t1 t2 v8 v9 (Z_to_bv 64 A) (Z_to_bv 64 out) (Z_to_bv 64 4) (Z_to_bv 64 0) a4 a5 a6 a7
             v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        F (Z_to_bv 64 SCT_PRINT) fc None m0 (seg_rom ctusegs)).
Proof using All.
  intros until P. intros ST MI FRM HB NW PS0 K.
  unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz in HB.
  facts. unfold SCT_PRINT.
  pose proof (munch_refl (W0 sp lo out) m0) as MU. unfold W0 in MU. pose proof (wmono_refl ctusegs m0) as WM.
  assert (HFC : sp_F F F) by (intros k Hk; reflexivity).
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
  pose proof (pv_static_transport _ _ _ PS0 MU WM ltac:(lia)) as PS1.
  lazymatch type of FRL with rw_cells _ _ _ ?clo =>
  eapply (sp_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F fc m1 nw clo A_C1 FMT_C1 [PA_i 4; PA_s []] O_C1 0x19d938);
    [ | split; [exact NW| unfold bio_null_cells, bio_cells, NULL_METHOD, MallocRep.wz; exact HB]| exact FRM| exact HFC
    | apply pcok_C1; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ] end.
  { close_inv MI ST PS1 MU WM FRH FRL FRL. }
  clear MI ST MU WM FRH FRL HB PS1 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m1.
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fc2 fc2 m2 INV2 BIO2 FRM2 HFC2.
  pose proof INV2 as INV2'. open_inv INV2. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  ub. zstep.
  do 5 zstep. zstep.
  eapply (sp_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc2 fc2 m2 _ _ A_C2 FMT_C2 [PA_i 8; PA_s []] O_C2 0x19d95c);
    [exact INV2'| exact BIO2| exact FRM2| exact HFC2
    | apply pcok_C2; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV2' BIO2 FRM2 HFC2 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m2.
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m3 INV3 BIO3 FRM3 HFC3.
  pose proof INV3 as INV3'. open_inv INV3. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  static_now PS0 MU WM.
  zstep. if_cases C0; [exfalso; zify_cond C0; lia| clear C0].
  zstep. if_cases CA; [exfalso; zify_cond CA; revert CA; change 7 with (Z.ones 3); rewrite Z.land_ones by lia; change (2 ^ 3) with 8; clear - AAL; intros CA; Z.div_mod_to_equations; lia| clear CA].
  zstep. zstep. if_cases K1; zify_cond K1; [| exfalso; apply K1; reflexivity]. try clear K1.
  clear SSP1 SSP2 NMa NMb HS1 HS2 HS3 SC0 SC1 SC2 SC4 SC3 IMG.
  (* [comment removed for export] *)
  do 3 zstep. zstep.
  eapply (sp_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m3 _ _ A_C4 FMT_C4 [] O_C4 0x19d9dc);
    [exact INV3'| exact BIO3| exact FRM3| exact HFC3
    | apply pcok_C4; exact MI
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV3' BIO3 FRM3 HFC3 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m3.
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fc4 fc4 m4 INV4 BIO4 FRM4 HFC4.
  pose proof INV4 as INV4'. open_inv INV4. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  zstep. if_cases K2; zify_cond K2; [| exfalso; apply K2; reflexivity]. try clear K2.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  eapply (sp_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc4 fc4 m4 _ _ A_C5 FMT_C5 [PA_i 8; PA_s []] O_C5 0x19da24);
    [exact INV4'| exact BIO4| exact FRM4| exact HFC4
    | apply pcok_C5; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV4' BIO4 FRM4 HFC4 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m4.
  intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m5 INV5 BIO5 FRM5 HFC5.
  pose proof INV5 as INV5'. open_inv INV5. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  static_now PS0 MU WM.
  ub. zstep. zstep. try rewrite (sx32_lit lin) by lia. clear SSP1 SSP2 NMa NMb HS2 HS3 SC0 SC1 SC2 SC4 SC3 IMG.
  zstep. zstep. zstep. zstep.
  eapply (hx_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc5 fc5 m5 _ _ LI lin lib 0x19da44);
    [exact INV5'| exact BIO5| exact FRM5| exact HFC5| exact HS1| exact (proj1 LIN)| exact (proj2 LIN)| exact LIW| exact LIR
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV5' BIO5 FRM5 HFC5 HS1 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m5.
  intros t0f t1f t2f a1f a2f a3f a4f a5f a6f a7f t3f t4f t5f t6f Fc6 fc6 m6 nw6 INV6 BIO6 FRM6 HFC6.
  pose proof INV6 as INV6'. open_inv INV6. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  eapply (sp_callv _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc6 fc6 m6 _ _ A_C6 FMT_C6 [PA_i 8; PA_s []] O_C6 0x19da60);
    [exact INV6'| exact BIO6| exact FRM6| exact HFC6
    | apply pcok_C6; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV6' BIO6 FRM6 HFC6 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m6.
  intros t0g t1g t2g a1g a2g a3g a4g a5g a6g a7g t3g t4g t5g t6g Fc7 fc7 m7 INV7 BIO7 FRM7 HFC7.
  pose proof INV7 as INV7'. open_inv INV7. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  static_now PS0 MU WM.
  zstep.
  unfold SCT_PRINT_TS in K. eapply (K _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc7 fc7 m7 _ _ INV7' BIO7 FRM7 HFC7).
Qed.

End SPV.
