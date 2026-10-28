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
From OssFuzzTheorems.Proofs.openssl.ct.lib.Spec Require Import Prelim Monad PrintfModel PrintfModelX CtSizes.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Printf_apfmt Printf_ctfmt.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtU Require Import Layout Lib_iface Lib_kit Printf_lib F_pop_arg F_printf_iface F_vsnprintf.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtHXU Require Import HxpFacts.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtRepU Require Import ApCells ApRepDefs ApWalkTac W_bio_push W_bio_write W_bio_printf W_obj_lookup.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtSctU Require Import SctDefs W_sct_leaves.
From OssFuzzTheorems.Proofs.openssl.ct.lib.CtPrnU Require Import PrnFmt W_bio_hex_string W_sct_print_nv1 PrnLeaf W_sct_print_A.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import Ceiling.
From OssFuzzTheorems.Proofs.openssl.ct.lib.P Require Import Rnd.
From OssFuzzTheorems.Proofs.openssl.ct.lib.Lib Require Import StoreFast.
Unset Lia Cache. Unset Nia Cache. Unset Nra Cache.
Import ListNotations.
Open Scope Z_scope.

Definition SCT_PRINT_C9 : Z := 0x19db6c.

Local Ltac std_lia__ := lia.
Local Ltac lia := first [std_lia__ | try (pose proof alloc_ceiling_range as CEIL_RANGE__); std_lia__].

Section SPV. Context {CE__ : Ceiling} {RN__ : RunRnd}.
Variables (sp gp tp : word) (F : bvmap 5 word) (m0 : mem) (lo out pv : Z) (canary : word).
Variables (A LI lin ts EX exn hsh sga SG sgn : Z) (lib exb sgb : list byte).
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
(* [comment removed for export] *)
Hypothesis NID : frozen (sig_nid 0 hsh sga <> NID_undef).

Local Notation pv_invN := (pv_inv sp m0 lo out canary A LI lin ts EX exn hsh sga SG sgn lib exb sgb vra v8 v9 v18 v19 v20 v21 v22).
Local Notation pv_staticN := (pv_static canary A LI lin ts EX exn hsh sga SG sgn lib exb sgb).
Local Notation sp_callvN := (sp_callv sp gp tp F m0 lo out pv canary A LI lin ts EX exn hsh sga SG sgn lib exb sgb vra v8 v9 v18 v19 v20 v21 v22
                                      GLO LO SP63 SP16 OB OAL HA LIN LIR LIW EXN EXR EXW SGN SGR SGW TSW HSH SGA).
Local Notation hx_callvN := (hx_callv sp gp tp F m0 lo out pv canary A LI lin ts EX exn hsh sga SG sgn lib exb sgb vra v8 v9 v18 v19 v20 v21 v22
                                      GLO LO SP63 SP16 OB OAL HA LIN LIR LIW EXN EXR EXW SGN SGR SGW TSW HSH SGA).
Local Notation pv_static_transportN := (pv_static_transport lo out canary A LI lin ts EX exn hsh sga SG sgn lib exb sgb
                                          GLO OB HA LIN LIR LIW EXN EXR EXW SGN SGR SGW TSW HSH SGA).

Local Ltac open_inv H := destruct H as (MI & ST & PS & MU & WM & FRH & FRL & SZ).
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
Local Ltac static_now PS0 MU WM :=
  let PS := fresh "PS" in
  pose proof (pv_static_transportN _ _ _ PS0 MU WM ltac:(lia)) as PS;
  destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG);
  unfold got_ssp, ssp_guard in SSP1, SSP2; unfold NULL_METHOD in NMa, NMb.

(* [comment removed for export] *)
Lemma nid_cases : sig_nid 0 hsh sga = NID_ecdsa_with_SHA256 \/ sig_nid 0 hsh sga = NID_sha256WithRSAEncryption.
Proof using NID.
  generalize NID. unfold frozen, sig_nid, NID_undef, NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption. cbn [Z.eqb andb].
  destruct (hsh =? 4); cbn [andb]; [| intros H; exfalso; apply H; reflexivity].
  destruct (sga =? 3); [left; reflexivity|]. destruct (sga =? 1); [right; reflexivity|]. intros H; exfalso; apply H; reflexivity.
Qed.

(* [comment removed for export] *)
Definition segC_post (nwF : Z -> Prop) : machine_state -> Prop :=
  fun ms' => exists (t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 t3 t4 t5 t6 : word) (F' : bvmap 5 word) (fc' : bv 32) (m' : mem) (nw' : Z),
    ms' = MS (mkR vra sp gp tp t0 t1 t2 v8 v9 a0 a1 a2 a3 a4 a5 a6 a7 v18 v19 v20 v21 v22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
             F' (ret_pc vra) fc' None m' (seg_rom ctusegs)
    /\ munch (W0 sp lo out) m0 m' /\ wmono ctusegs m0 m' /\ mem_inv ctusegs m'
    /\ frm0 fc' /\ sp_F F F' /\ stk ctusegs m' lo (bv_unsigned sp) /\ pv_staticN m' /\ sp_bio out pv m' nw' /\ nwF nw'.

(* [comment removed for export] *)
Local Ltac after_leaf16 ESP mold HB :=
  let ms' := fresh "ms'" in let PO := fresh "PO" in
  intros ms' PO; rewrite ?ESP in PO;
  destruct PO as (? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & ? & mnew & -> & MUc & WMc & MIc & STc);
  let W := lazymatch type of MUc with munch ?W _ _ => W end in
  lazymatch goal with
  | FRH : rw_cells _ mold (bv_unsigned sp + -64) _, FRL : rw_cells _ mold (bv_unsigned sp + -96) _,
    MU : munch _ m0 mold, WM : wmono _ m0 mold, PSm : pv_staticN mold |- _ =>
      apply (pv_static_transportN mold mnew (bv_unsigned sp + -96)) in PSm; [| intros xq Hxq; apply MUc; clear - Hxq LO; cbn in *; lia| exact WMc| clear - LO; lia];
      apply (rw_cells_transport ctusegs W mold mnew) in HB; [| exact MUc| exact WMc| clear - OB LO; cbn [disjoint_from cells_size csize Nat.add bio_null_cells bio_cells length]; lia];
      apply (rw_cells_transport ctusegs W mold mnew) in FRH; [| exact MUc| exact WMc| clear - LO; cbn [disjoint_from cells_size csize Nat.add length]; lia];
      apply (rw_cells_transport ctusegs W mold mnew) in FRL; [| exact MUc| exact WMc| clear - LO; cbn [disjoint_from]; lia];
      (let MU' := fresh "MU" in
       assert (MU' : munch [(lo, bv_unsigned sp); (out, out + 128)] m0 mnew)
         by (intros xq Hxq; rewrite (MUc xq); [apply MU; exact Hxq| clear - Hxq LO; cbn in *; lia]); clear MU; rename MU' into MU);
      apply (wmono_trans ctusegs m0 mold mnew WM) in WMc; clear WM MUc; rename WMc into WM; clear mold
  end.

(* [comment removed for export] *)
Lemma seg_C2 : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell),
  pv_invN clo m -> sp_bio out pv m nw -> frm0 fc -> sp_F F Fc ->
  evt ctusegs (segC_post (fun _ => True))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A) (Z_to_bv 64 8) (Z_to_bv 64 20) x21 x22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_PRINT_C9) fc None m (seg_rom ctusegs)).
Proof using All.
  intros until clo. intros INV BIO FRM HFC. pose proof INV as INV'. open_inv INV. pose proof PS as PS0'. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  unfold SCT_PRINT_C9.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  eapply (sp_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m _ _ A_C9 FMT_C9 [PA_i 8; PA_s []] O_C9 0x19db88);
    [exact INV'| exact BIO| exact FRM| exact HFC
    | apply pcok_C9; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV' BIO FRM HFC ESP SEPB SEPA SEPM SEPG SEPC SPR PS0'. clear m.
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fc2 fc2 m2 INV2 BIO2 FRM2 HFC2.
  pose proof INV2 as INV2'. open_inv INV2. facts. unfold W0 in MU. unfold pv_hi in FRH.
  pose proof PS as PSm. destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG).
  unfold got_ssp, ssp_guard in SSP1, SSP2. unfold NULL_METHOD in NMa, NMb.
  (* [comment removed for export] *)
  zstep. zstep.
  assert (RV : ro_cells ctusegs m2 (A + SCTO_VERSION) [C4 (Z_to_bv 64 0)]) by (unfold SCTO_VERSION; rewrite Z.add_0_r; exact SC0).
  clear SSP1 SSP2 NMa NMb HS1 HS2 HS3 SC0 SC1 SC2 SC3 INV2'.
  eapply evt_cut; [eapply (SCT_get_signature_nid_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo A 0 hsh sga);
    [rewrite ESP; exact ST| exact MI| unfold GLOBALS_TOP; lia| rewrite ESP; lia| unfold SCT_SIZE; lia| exact AAL| exact RV| exact SC4| lia| lia| lia| reflexivity]|].
  clear RV SC4.
  unfold nid_post. clear ST MI IMG. destruct BIO2 as [NW2 HB2]. after_leaf16 ESP m2 HB2. rename MIc into MI3, STc into ST3, mnew into m3.
  replace (ret_pc (Z_to_bv 64 1694608)) with (Z_to_bv 64 1694608) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  cbn [Z.eqb].
  (* [comment removed for export] *)
  pose proof nid_cases as NC.
  assert (NR : 0 < sig_nid 0 hsh sga < 2^11) by (unfold NID_ecdsa_with_SHA256, NID_sha256WithRSAEncryption in NC; lia).
  zstep. if_cases KN; zify_cond KN; [exfalso; revert KN; rewrite ?unsigned_lit by lia; lia|]. clear KN.
  (* [comment removed for export] *)
  pose proof PSm as (_ & _ & _ & _ & IMG3).
  zstep.
  eapply evt_cut; [eapply (OBJ_nid2ln_spec _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ lo (sig_nid 0 hsh sga));
    [rewrite ESP; exact ST3| exact MI3| unfold GLOBALS_TOP; lia| rewrite ESP; lia| exact IMG3| exact NC| reflexivity]|].
  unfold nid2ln_post. clear ST3 MI3 IMG3. after_leaf16 ESP m3 HB2. rename MIc into MI4, STc into ST4, mnew into m4.
  replace (ret_pc (Z_to_bv 64 1694616)) with (Z_to_bv 64 1694616) by (symmetry; apply ret_pc_even; [lia| reflexivity]).
  (* [comment removed for export] *)
  destruct (ln_at m4 (sig_nid 0 hsh sga) MI4 NC) as (LNB & LNF & LNK & LNL & LN0 & LN1).
  pose proof (zlength_nonneg'' (ln_str (sig_nid 0 hsh sga))) as LS0.
  do 4 zstep. zstep.
  assert (INV4 : pv_invN clo m4) by (close_inv MI4 ST4 PSm MU WM FRH FRL SZ).
  eapply (sp_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc2 fc2 m4 _ _ A_C10 FMT_C10 [PA_s (ln_str (sig_nid 0 hsh sga))] (ln_str (sig_nid 0 hsh sga)) 0x19dbac);
    [exact INV4| split; [exact NW2| exact HB2]| exact FRM2| exact HFC2
    | eapply (pcok_C10 m4 lo _ A_C10 (ln_addr (sig_nid 0 hsh sga)) (ln_str (sig_nid 0 hsh sga)) (zb (ln_slk (sig_nid 0 hsh sga))));
        [exact MI4| unfold STATIC_SPLIT; lia| apply fmt_C10_at; exact MI4| unfold A_C10; lia| unfold A_C10, STATIC_SPLIT; lia
        | exact LNB| exact LNF| exact LNK| exact LN0| exact LN1| lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI4 ST4 MU WM FRH FRL SZ INV4 NW2 HB2 FRM2 HFC2 ESP SEPB SEPA SEPM SEPG SEPC SPR PSm LNB LNF LNK LNL LN0 LN1 LS0. clear m4.
  intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m5 INV5 BIO5 FRM5 HFC5.
  pose proof INV5 as INV5'. open_inv INV5. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  zstep. do 6 zstep. zstep.
  eapply (sp_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc3 fc3 m5 _ _ A_C11 FMT_C11 [PA_i 8; PA_s []] O_C11 0x19dbe4);
    [exact INV5'| exact BIO5| exact FRM5| exact HFC5
    | apply pcok_C11; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV5' BIO5 FRM5 HFC5 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m5.
  intros t0d t1d t2d a1d a2d a3d a4d a5d a6d a7d t3d t4d t5d t6d Fc4 fc4 m6 INV6 BIO6 FRM6 HFC6.
  pose proof INV6 as INV6'. open_inv INV6. facts. unfold W0 in MU. unfold pv_hi in FRH.
  pose proof PS as PSm. destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG).
  (* [comment removed for export] *)
  zstep. zstep. rewrite (sx32_lit sgn) by lia. clear SSP1 SSP2 NMa NMb HS1 HS2 SC0 SC1 SC2 SC4 SC3 IMG.
  zstep. zstep. zstep. zstep.
  eapply (hx_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc4 fc4 m6 _ _ SG sgn sgb 0x19dbfc);
    [exact INV6'| exact BIO6| exact FRM6| exact HFC6| exact HS3| exact (proj1 SGN)| exact (proj2 SGN)| exact SGW| exact SGR
    | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV6' BIO6 FRM6 HFC6 HS3 ESP SEPB SEPA SEPM SEPG SEPC SPR PSm. clear m6.
  intros t0e t1e t2e a1e a2e a3e a4e a5e a6e a7e t3e t4e t5e t6e Fc5 fc5 m7 nw7 INV7 BIO7 FRM7 HFC7.
  open_inv INV7. facts. unfold W0 in MU. unfold pv_hi in FRH.
  (* [comment removed for export] *)
  do 8 zstep.
  assert (FR : rw_cells ctusegs m7 (bv_unsigned sp + -96) (clo ++ [C8 v22; C8 v21; C8 v20; C8 v19; C8 v18; C8 v9; C8 v8; C8 vra]))
    by (apply rw_cells_app; split; [exact FRL|]; rewrite SZ; replace (bv_unsigned sp + -96 + Z.of_nat 32) with (bv_unsigned sp + -64) by lia; exact FRH).
  clear FRL FRH.
  zstep.
  eapply stk_release in FR; [| exact ST| lia]. clear ST. rename FR into ST.
  rewrite cells_size_app, SZ in ST. cbn [cells_size csize Nat.add] in ST.
  replace (bv_unsigned sp + -96 + Z.of_nat 96) with (bv_unsigned sp) in ST by lia.
  zstep.
  apply evt_done. unfold segC_post.
  do 15 eexists. exists Fc5, fc5, m7, nw7. split; [reflexivity|].
  split; [exact MU|]. split; [exact WM|]. split; [exact MI|]. split; [exact FRM7|]. split; [exact HFC7|]. split; [exact ST|]. split; [exact PS|]. split; [exact BIO7| exact I].
Qed.


(* [comment removed for export] *)
Lemma seg_C : forall (x1 t0 t1 t2 a0 a1 a2 a3 a4 a5 a6 a7 x21 x22 t3 t4 t5 t6 : word) (Fc : bvmap 5 word) (fc : bv 32) (m : mem) (nw : Z) (clo : list cell),
  pv_invN clo m -> sp_bio out pv m nw -> frm0 fc -> sp_F F Fc ->
  evt ctusegs (segC_post (fun _ => True))
    (MS (mkR x1 (Z_to_bv 64 (bv_unsigned sp + -96)) gp tp t0 t1 t2 sp (Z_to_bv 64 out) a0 a1 a2 a3 a4 a5 a6 a7
             (Z_to_bv 64 A) (Z_to_bv 64 8) (Z_to_bv 64 20) x21 x22 v23 v24 v25 v26 v27 t3 t4 t5 t6)
        Fc (Z_to_bv 64 SCT_PRINT_TAIL) fc None m (seg_rom ctusegs)).
Proof using All.
  intros until clo. intros INV BIO FRM HFC. pose proof INV as INV'. open_inv INV. clear PS. facts. unfold W0 in MU. unfold pv_hi in FRH.
  unfold SCT_PRINT_TAIL.
  (* [comment removed for export] *)
  do 6 zstep. zstep.
  eapply (sp_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc fc m _ _ A_C7 FMT_C7 [PA_i 8; PA_s []] O_C7 0x19db38);
    [exact INV'| exact BIO| exact FRM| exact HFC
    | apply pcok_C7; [exact MI| unfold STATIC_SPLIT; lia]
    | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
  clear MI ST MU WM FRH FRL SZ INV' BIO FRM HFC ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m.
  intros t0b t1b t2b a1b a2b a3b a4b a5b a6b a7b t3b t4b t5b t6b Fc2 fc2 m2 INV2 BIO2 FRM2 HFC2.
  pose proof INV2 as INV2'. open_inv INV2. facts. unfold W0 in MU. unfold pv_hi in FRH.
  pose proof PS as PSm. destruct PS as ([SSP1 SSP2] & [NMa NMb] & (HS1 & HS2 & HS3) & (SC0 & SC1 & SC2 & SC4 & SC3) & IMG).
  (* [comment removed for export] *)
  zstep. zstep. if_cases KE; zify_cond KE.
  - (* [comment removed for export] *)
    assert (E0 : exn = 0) by (revert KE; rewrite ?unsigned_lit by lia; lia). clear KE.
    clear SSP1 SSP2 NMa NMb HS1 HS2 HS3 SC0 SC1 SC2 SC4 SC3 IMG PSm.
    do 3 zstep. zstep.
    eapply (sp_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc2 fc2 m2 _ _ A_C8 FMT_C8 [] O_C8 0x19db6c);
      [exact INV2'| exact BIO2| exact FRM2| exact HFC2
      | apply pcok_C8; exact MI
      | reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
    clear MI ST MU WM FRH FRL SZ INV2' BIO2 FRM2 HFC2 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m2.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m3 INV3 BIO3 FRM3 HFC3.
    unfold SCT_PRINT_C9 in *.
    eapply seg_C2; [exact INV3| exact BIO3| exact FRM3| exact HFC3].
  - (* [comment removed for export] *)
    assert (E1 : 0 < exn) by (revert KE; rewrite ?unsigned_lit by lia; lia). clear KE.
    zstep. zstep. rewrite Z.add_0_r, (swrap32_small exn) by lia. clear SSP1 SSP2 NMa NMb HS1 HS3 SC0 SC1 SC2 SC4 SC3 IMG PSm.
    zstep. zstep. zstep. zstep.
    eapply (hx_callvN _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Fc2 fc2 m2 _ _ EX exn exb 0x19db58);
      [exact INV2'| exact BIO2| exact FRM2| exact HFC2| exact HS2| exact (proj1 EXN)| exact (proj2 EXN)| exact EXW| exact EXR
      | reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| reflexivity| lia| reflexivity| ].
    clear MI ST MU WM FRH FRL SZ INV2' BIO2 FRM2 HFC2 HS2 ESP SEPB SEPA SEPM SEPG SEPC SPR. clear m2.
    intros t0c t1c t2c a1c a2c a3c a4c a5c a6c a7c t3c t4c t5c t6c Fc3 fc3 m3 nw3 INV3 BIO3 FRM3 HFC3.
    pose proof INV3 as INV3'. open_inv INV3. clear PS. facts.
    zstep.
    unfold SCT_PRINT_C9 in *.
    eapply seg_C2; [exact INV3'| exact BIO3| exact FRM3| exact HFC3].
Qed.

End SPV.
