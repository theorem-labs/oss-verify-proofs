(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFPSpec LibRodata LibFrame LibFPLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PerfKc.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require Import SymDriveLB.
From Stdlib Require Import Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.ev_simpl E ::= ev_simpl_lz E.
#[local] Ltac SymDriveFP.ev_simpl_in E H ::= ev_simpl_in_lz E H.
(* [comment removed for export] *)
#[local] Ltac SymDriveFP.run_fp_with_h HR HF HK fuel stops scr chints keep extra ::= run_fp_with_h_lz HR HF HK fuel stops scr chints keep extra.
#[local] Ltac SymDriveFP.branch_case_with HR HF HK Hc ::= branch_case_with_lz HR HF HK Hc.
(* [comment removed for export] *)
Local Ltac Zify.zify ::= intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook.
(* [comment removed for export] *)
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.
Import SXF. Import SXFS.

Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Ltac in_lit := cbn; repeat (first [left; reflexivity | right]).

Section Proof.
  Hypothesis Hev : eval_curve_contract SEGS wp3_src1.

  Variables (FPI : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp C data t8 t16 : word) (n len : Z) (bs : list byte).

  Hypothesis Hra : getr regs 1 = ret.
  Hypothesis Hret : ret_ok ret.
  Hypothesis Hsp : getr regs 2 = sp.
  Hypothesis Hc : getr regs 10 = C.
  Hypothesis H11 : getr regs 11 = Z_to_bv 64 n.
  Hypothesis H12 : getr regs 12 = Z_to_bv 64 (bv_unsigned sp + 12).
  Hypothesis H13 : getr regs 13 = Z_to_bv 64 (bv_unsigned sp + 8).
  Hypothesis H14 : getr regs 14 = Z_to_bv 64 (bv_unsigned sp + 4).
  Hypothesis Hal16 : (bv_unsigned sp mod 16 = 0)%Z.
  Hypothesis Hwst : writable SEGS mem (bv_unsigned sp - 112) 128.
  Hypothesis Hcw : exists w, cell SEGS mem (bv_unsigned sp + 12) 4 w.
  Hypothesis Hcal : (bv_unsigned C mod 8 = 0)%Z.
  Hypothesis Hc32 : (bv_unsigned C + 32 <= 2 ^ 64)%Z.
  Hypothesis Hn32 : (0 <= n < 2 ^ 32)%Z.
  Hypothesis Hn   : cell SEGS mem (bv_unsigned C) 4 (Z_to_bv 64 n).
  Hypothesis Ht8  : cell64 SEGS mem (bv_unsigned C + 8) t8.
  Hypothesis Ht16 : cell64 SEGS mem (bv_unsigned C + 16) t16.
  Hypothesis Hnr : (2 <= n <= 2 ^ 24)%Z.
  Hypothesis H8 : (bv_unsigned t8 <> 0%Z -> inDATA data len (bv_unsigned t8) n).
  Hypothesis H16 : (bv_unsigned t16 <> 0%Z -> inDATA data len (bv_unsigned t16) (2 * n)).
  Hypothesis Hsome : (bv_unsigned t8 <> 0%Z \/ bv_unsigned t16 <> 0%Z).
  Hypothesis Hdok : data_ok mem data len bs.
  Hypothesis Hro : rodata_clear mem 0x103ec 0x1048c.
  Hypothesis Hdisj_sc : (bv_unsigned sp + 16 <= bv_unsigned C \/ bv_unsigned C + 32 <= bv_unsigned sp - 112)%Z.
  Hypothesis Hdisj_ds : (bv_unsigned data + len <= bv_unsigned sp - 112 \/ bv_unsigned sp + 16 <= bv_unsigned data)%Z.

  #[local] Abbreviation fp0 := (fp_regs (FPState:=FPI)).

  (* [comment removed for export] *)
  Definition QP (FPI' : FPState) (regs' : bvmap 5 word) (mem' : word -> option byte) : Prop :=
    regs_kept abi_kept regs regs' /\ fregs_kept abi_fkept fp0 (fp_regs (FPState:=FPI')) /\
    (frame_mod mem mem' [(Z_to_bv 64 (bv_unsigned sp - 112), 128%Z)] /\
     (exists w, cell SEGS mem' (bv_unsigned sp + 12) 4 w) /\ (exists w, cell SEGS mem' (bv_unsigned sp + 4) 4 w) /\
     exists r, getr regs' 10 = Z_to_bv 64 r /\ (1 <= r <= n)%Z).
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem', st' = mkst (FP:=FPI') regs' ret mem' rom /\ QP FPI' regs' mem'.

  (* [comment removed for export] *)
  Definition MEMFIX (M : word -> option byte) : Prop :=
    cell64 SEGS M (bv_unsigned sp - 8) ret /\ cell64 SEGS M (bv_unsigned sp - 16) (getr regs 8) /\
    cell64 SEGS M (bv_unsigned sp - 24) (getr regs 9) /\ cell64 SEGS M (bv_unsigned sp - 32) (getr regs 18) /\
    cell64 SEGS M (bv_unsigned sp - 40) (getr regs 19) /\ cell64 SEGS M (bv_unsigned sp - 48) (getr regs 20) /\
    cell64 SEGS M (bv_unsigned sp - 56) (getr regs 21) /\ cell64 SEGS M (bv_unsigned sp - 64) (getr regs 22) /\
    cell64 SEGS M (bv_unsigned sp - 72) (reg_get fp0 8) /\ cell64 SEGS M (bv_unsigned sp - 80) (reg_get fp0 9) /\
    cell64 SEGS M (bv_unsigned sp - 88) (reg_get fp0 18) /\ cell64 SEGS M (bv_unsigned sp - 96) (reg_get fp0 19) /\
    cell64 SEGS M (bv_unsigned sp - 104) (reg_get fp0 20) /\
    cell SEGS M (bv_unsigned C) 4 (Z_to_bv 64 n) /\ cell64 SEGS M (bv_unsigned C + 8) t8 /\ cell64 SEGS M (bv_unsigned C + 16) t16 /\
    data_ok M data len bs /\ rodata_clear M 0x103ec 0x1048c /\ writable SEGS M (bv_unsigned sp - 112) 128 /\
    frame_mod mem M [(Z_to_bv 64 (bv_unsigned sp - 112), 128%Z)].

  (* [comment removed for export] *)
  Definition REGFIX (FPI' : FPState) (R : bvmap 5 word) : Prop :=
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 112) /\ getr R 8 = Z_to_bv 64 (bv_unsigned sp + 8) /\
    getr R 9 = Z_to_bv 64 (bv_unsigned sp + 4) /\ getr R 18 = Z_to_bv 64 (bv_unsigned sp + 12) /\
    getr R 19 = Z_to_bv 64 n /\ getr R 20 = C /\
    (forall r, In r [3; 4; 23; 24; 25; 26; 27]%bv -> getr R r = getr regs r) /\
    (forall r, In r [21; 22; 23; 24; 25; 26; 27]%bv -> reg_get (fp_regs (FPState:=FPI')) r = reg_get fp0 r).

  (* [comment removed for export] *)
  Definition TINV (lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    REGFIX FPI' R /\ getr R 21 = Z_to_bv 64 lp /\ (1 <= lp <= n)%Z /\ MEMFIX M /\
    (exists wf, cell SEGS M (bv_unsigned sp + 4) 4 wf) /\ (exists wc, cell SEGS M (bv_unsigned sp + 12) 4 wc).
  Definition INV (i lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) : Prop :=
    TINV lp FPI' R M /\ getr R 22 = Z_to_bv 64 i /\ (1 <= i <= n - 1)%Z.

  (* [comment removed for export] *)
  #[local] Abbreviation VALS R FR i lp wf wc :=
    (junk_vals R ++ fjunk_vals FR ++ junk_vals regs ++ fjunk_vals fp0 ++
     [t8; t16; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc]).
  (* [comment removed for export] *)

  Definition SRT : list expr :=
    [ELit 0; EVar 1; EAlu ALU_ADD (EVar 66) (ELit (-112)); EVar 67; EVar 68; EVar 5; EVar 6; EVar 7;
     EAlu ALU_ADD (EVar 66) (ELit 8); EAlu ALU_ADD (EVar 66) (ELit 4); EVar 10; EVar 11; EVar 12; EVar 13;
     EVar 14; EVar 15; EVar 16; EVar 17; EAlu ALU_ADD (EVar 66) (ELit 12); EVar 75; EVar 74; EVar 131;
     EVar 22; EVar 87; EVar 88; EVar 89; EVar 90; EVar 91; EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SRI : list expr :=
    [ELit 0; EVar 1; EAlu ALU_ADD (EVar 66) (ELit (-112)); EVar 67; EVar 68; EVar 5; EVar 6; EVar 7;
     EAlu ALU_ADD (EVar 66) (ELit 8); EAlu ALU_ADD (EVar 66) (ELit 4); EVar 10; EVar 11; EVar 12; EVar 13;
     EVar 14; EVar 15; EVar 16; EVar 17; EAlu ALU_ADD (EVar 66) (ELit 12); EVar 75; EVar 74; EVar 131;
     EVar 130; EVar 87; EVar 88; EVar 89; EVar 90; EVar 91; EVar 28; EVar 29; EVar 30; EVar 31].
  Definition SFR : list expr :=
    [EVar 32; EVar 33; EVar 34; EVar 35; EVar 36; EVar 37; EVar 38; EVar 39; EVar 40; EVar 41;
     EVar 42; EVar 43; EVar 44; EVar 45; EVar 46; EVar 47; EVar 48; EVar 49; EVar 50; EVar 51; EVar 52;
     EVar 117; EVar 118; EVar 119; EVar 120; EVar 121; EVar 122; EVar 123; EVar 60; EVar 61; EVar 62; EVar 63].

  Definition KN : list kentry :=
    [KAlign (EVar 66) 16; KRange (EVar 75) 2 16777216; KRange (EVar 130) 1 16777216; KRange (EVar 131) 1 16777216;
     KWord (SA (EVar 66) 4) 4 (EVar 132); KWord (SA (EVar 66) 12) 4 (EVar 133);
     KWord (SA (EVar 66) (-8)) 8 (EVar 65); KWord (SA (EVar 66) (-16)) 8 (EVar 72);
     KWord (SA (EVar 66) (-24)) 8 (EVar 73); KWord (SA (EVar 66) (-32)) 8 (EVar 82);
     KWord (SA (EVar 66) (-40)) 8 (EVar 83); KWord (SA (EVar 66) (-48)) 8 (EVar 84);
     KWord (SA (EVar 66) (-56)) 8 (EVar 85); KWord (SA (EVar 66) (-64)) 8 (EVar 86);
     KWord (SA (EVar 66) (-72)) 8 (EVar 104); KWord (SA (EVar 66) (-80)) 8 (EVar 105);
     KWord (SA (EVar 66) (-88)) 8 (EVar 114); KWord (SA (EVar 66) (-96)) 8 (EVar 115);
     KWord (SA (EVar 66) (-104)) 8 (EVar 116);
     KWr (SA (EVar 66) (-112)) 128].

  Lemma pack : forall (lp i : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte) (wf wc : word),
    REGFIX FPI' R -> getr R 21 = Z_to_bv 64 lp -> (1 <= lp <= n)%Z -> (1 <= i <= n)%Z ->
    MEMFIX M -> cell SEGS M (bv_unsigned sp + 4) 4 wf -> cell SEGS M (bv_unsigned sp + 12) 4 wc ->
    let E := Env (vals_ev (VALS R (fp_regs (FPState:=FPI')) i lp wf wc)) (blobs_ev [bs]) in
    regs_ok E SRT R /\ fregs_ok E SFR (fp_regs (FPState:=FPI')) /\ know_ok SEGS E M KN /\
    regs_ok E (sr_vars 64) regs /\ fregs_ok E (sfr_vars 96) fp0.
  Proof.
    intros lp i FPI' R M wf wc (R2 & R8 & R9 & R18 & R19 & R20 & RK & FK) R21 Hlp Hi
           (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & Mn & M8c & M16c & Md & Mro & Mw & Mfr) Hwf Hwc E.
    pose proof (u64_range sp) as Hspr. pose proof Mw as (W1 & W2 & W3 & W4).
    clear Hsome Hdisj_sc Hdisj_ds H8 H16 Hcw Md Mro Mfr.
    unfold cell64, cell in *.
    split; [|split; [|split; [|split]]].
    - replace SRT with (sr_upds (sr_vars 0)
        [(2, EAlu ALU_ADD (EVar 66) (ELit (-112))); (8, EAlu ALU_ADD (EVar 66) (ELit 8));
         (9, EAlu ALU_ADD (EVar 66) (ELit 4)); (18, EAlu ALU_ADD (EVar 66) (ELit 12));
         (19, EVar 75); (20, EVar 74); (21, EVar 131); (3, EVar 67); (4, EVar 68);
         (23, EVar 87); (24, EVar 88); (25, EVar 89); (26, EVar 90); (27, EVar 91)]%bv) by (vm_compute; reflexivity).
      apply regs_ok_pins; [exact (regs_ok_vars [] R _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; rewrite_getr; rewrite ?alu_add_lit;
                                  first [ reflexivity | apply RK; in_lit | f_equal; lia ] |]).
      apply Forall_nil.
    - replace SFR with (sr_upds (sfr_vars 32)
        [(21, EVar 117); (22, EVar 118); (23, EVar 119); (24, EVar 120); (25, EVar 121); (26, EVar 122); (27, EVar 123)]%bv)
        by (vm_compute; reflexivity).
      apply fregs_ok_pins; [exact (fregs_ok_vars (junk_vals R) (fp_regs (FPState:=FPI')) _ (blobs_ev [bs]))|].
      repeat (apply Forall_cons; [cbn [fst snd edenot]; ev_simpl E; apply FK; in_lit |]).
      apply Forall_nil.
    - unfold KN.
      constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal16]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H11, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite u_small by lia; lia|].
      Ltac kw E0 H := eapply (kword_intro SEGS _ _ (EVar 66) sp _ _ _ _);
                      [cbn [edenot]; ev_simpl E0; assumption | cbn [edenot]; ev_simpl E0; reflexivity | lia | lia | lia | lia |
                       lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ =>
                         lazymatch type of H with rdn _ _ (Z_to_bv 64 ?b) _ = _ => replace a with b by lia; rewrite_getr; exact H end end].
      constructor; [kw E Hwf|]. constructor; [kw E Hwc|].
      constructor; [kw E M1|]. constructor; [kw E M2|]. constructor; [kw E M3|]. constructor; [kw E M4|].
      constructor; [kw E M5|]. constructor; [kw E M6|]. constructor; [kw E M7|]. constructor; [kw E M8|].
      constructor; [kw E M9|]. constructor; [kw E M10|]. constructor; [kw E M11|]. constructor; [kw E M12|].
      constructor; [kw E M13|].
      constructor; [apply (kwr_intro SEGS E M (EVar 66) sp (-112) 128);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z by lia; exact W4]|].
      constructor.
    - exact (regs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI'))) regs
               (fjunk_vals fp0 ++ [t8; t16; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc]) (blobs_ev [bs])).
    - exact (fregs_ok_vars (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI')) ++ junk_vals regs) fp0
               [t8; t16; Z_to_bv 64 i; Z_to_bv 64 lp; wf; wc] (blobs_ev [bs])).
  Qed.

  Lemma pack_I : forall (i lp : Z) (FPI' : FPState) (R : bvmap 5 word) (M : word -> option byte),
    INV i lp FPI' R M -> exists wf wc,
    let E := Env (vals_ev (VALS R (fp_regs (FPState:=FPI')) i lp wf wc)) (blobs_ev [bs]) in
    regs_ok E SRI R /\ fregs_ok E SFR (fp_regs (FPState:=FPI')) /\ know_ok SEGS E M KN /\
    regs_ok E (sr_vars 64) regs /\ fregs_ok E (sfr_vars 96) fp0.
  Proof.
    intros i lp FPI' R M ((HRF & R21 & Hlp & HMF & (wf & Hwf) & (wc & Hwc)) & R22 & Hi).
    exists wf, wc.
    destruct (pack lp i FPI' R M wf wc HRF R21 Hlp ltac:(lia) HMF Hwf Hwc) as (HR & HF & HK & H64 & H96).
    split; [|split; [exact HF| split; [exact HK | split; [exact H64 | exact H96]]]].
    apply (regs_ok_pin _ _ R 22 (EVar 130)) in HR; [| cbn [edenot ev eb vals_ev blobs_ev nth app junk_vals fjunk_vals]; exact R22].
    exact HR.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac rewrite_getr_in H :=
    repeat match goal with G : getr ?R ?r = _ |- _ => rewrite G in H end.

  (* [comment removed for export] *)
  Ltac kcell HK b k n v H :=
    lazymatch type of HK with know_ok _ ?E0 ?M0 ?kn =>
      let KR := fresh "KR" in let Hfl := fresh "Hfl" in
      kread_rdn_fast SEGS E0 M0 kn b k n v HK H;
      lazymatch type of H with ?FL -> _ =>
        assert (Hfl : FL) by (unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; rewrite_getr; lia);
        specialize (H Hfl); clear Hfl end;
      unfold adenot, v_addi in H; cbn [a_base a_off edenot] in H; ev_simpl_in E0 H; rewrite_getr_in H
    end.

  Ltac frame_of_log RS fixup :=
    lazymatch goal with
    | |- frame_mod ?M0 (mem_denot ?E0 ?M0 ?log) ?regions =>
        replace regions with (regions_denot E0 RS)
          by (cbn [regions_denot map fst snd]; unfold adenot; cbn [a_base a_off edenot]; ev_simpl E0; fixup; reflexivity);
        apply (frame_mod_mem_denot E0 M0 log RS);
          [ lazymatch goal with H : log_flat _ log |- _ => exact H end
          | repeat (apply Forall_cons); [..|apply Forall_nil]; cbn [fst snd]; unfold flat, estart; cbn [a_base a_off edenot]; ev_simpl E0; fixup; lia
          | vm_compute; reflexivity ]
    end.

  Ltac subst_triv := repeat match goal with H : ?a = ?b |- _ => is_var a; is_var b; subst a end.

  Ltac solve_reg := rewrite_getr; rewrite ?alu_add_lit; rewrite ?addw1_lit by lia; rewrite ?u_small by lia;
                    rewrite ?Z.add_0_r, ?Z_to_bv_bv_unsigned; first [reflexivity | f_equal; lia | idtac].

  (* [comment removed for export] *)
  Ltac creg r := lazymatch goal with HR : regs_ok _ _ ?R' |- getr ?R' _ = _ => regv HR r; solve_reg end.

  (* [comment removed for export] *)
  Ltac prove_regfix H64 H96 :=
    lazymatch goal with |- REGFIX ?I ?R' =>
    lazymatch goal with HR : regs_ok ?E ?sr R', HF : fregs_ok _ ?sfr (@fp_regs I) |- _ =>
      lift_id H64 HR; lift_id H96 HF; unfold REGFIX;
      split; [creg (2%bv:reg)|]; split; [creg (8%bv:reg)|]; split; [creg (9%bv:reg)|];
      split; [creg (18%bv:reg)|]; split; [creg (19%bv:reg)|]; split; [creg (20%bv:reg)|];
      split;
      [ lazymatch type of H64 with id (regs_ok _ ?sr0 _) =>
          exact (regs_same_on E sr0 sr regs R' [3; 4; 23; 24; 25; 26; 27]%bv H64 HR ltac:(vm_compute; reflexivity)) end
      | lazymatch type of H96 with id (fregs_ok _ ?sfr0 _) =>
          exact (fregs_same_on E sfr0 sfr fp0 _ [21; 22; 23; 24; 25; 26; 27]%bv H96 HF ltac:(vm_compute; reflexivity)) end ]
    end end.

  (* [comment removed for export] *)
  Ltac kcell_auto HK b k n H :=
    lazymatch type of HK with know_ok _ _ _ ?kn =>
      let r := eval vm_compute in (kread SEGS kn b k n) in
      lazymatch r with Some ?v => kcell HK b k n v H end end.

  (* [comment removed for export] *)
  Ltac call_ec RET HM :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
    lazymatch goal with HR : regs_ok _ _ R' |- _ =>
      eapply rt_call;
      [ eapply (Hev data len bs I R' M' rom (Z_to_bv 64 RET));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | unfold eval_curve_pre; cbn [w3_ro_lo w3_ro_hi wp3_src1];
          exists C, t8, t16, n; split; [regv HR (10%bv:reg); rewrite_getr; reflexivity|];
          split; [exact Hcal|]; split; [lia|]; exact HM ]
      | cbv beta;
        let FPI' := fresh "FPI" in let regs' := fresh "R" in let mem' := fresh "MC" in
        let Hkeep := fresh "Hkeep" in let Hfkeep := fresh "Hfkeep" in let Hmem := fresh "Hmem" in
        intros FPI' regs' mem' (Hkeep & Hfkeep & Hmem); unfold eval_curve_post in Hmem; subst mem';
        unfold regs_kept in Hkeep; unfold fregs_kept in Hfkeep;
        after_call Hkeep Hfkeep FPI'; clear Hkeep Hfkeep ]
    end end.

  Lemma memfix_tc : forall M, MEMFIX M ->
    table_curve SEGS M data len (bv_unsigned C) n t8 t16 /\ data_ok M data len bs /\ rodata_clear M 0x103ec 0x1048c.
  Proof.
    intros M HM. destruct HM as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mn & M8 & M16 & Md & Mro & _ & _).
    split; [|split; [exact Md | exact Mro]].
    unfold table_curve. repeat (split; [first [split; [exact Hn32| exact Mn] | assumption] |]). exact Hsome.
  Qed.

  Lemma memfix_frame12 : forall M M', MEMFIX M -> frame_mod M M' [(Z_to_bv 64 (bv_unsigned sp + 12), 4%Z)] -> MEMFIX M'.
  Proof.
    intros M M' HM Hf. pose proof (u64_range sp). pose proof (u64_range C). pose proof Hwst as (W1 & _ & W3 & _).
    pose proof Hdok as (Hlen & _).
    pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) Hwst Hro) as Hsro.
    destruct HM as (M1 & M2 & M3 & M4 & M5 & M6 & M7 & M8 & M9 & M10 & M11 & M12 & M13 & Mn & M8c & M16c & Md & Mro & Mw & Mfr).
    unfold MEMFIX.
    repeat match goal with
    | |- cell64 _ _ _ _ /\ _ => split; [eapply cell64_frame; [exact Hf | eassumption | lia | lia | solve_apart]|]
    | |- cell _ _ _ _ _ /\ _ => split; [eapply cell_frame; [exact Hf | eassumption | lia | cbn; lia | solve_apart]|]
    end.
    split; [eapply data_ok_frame; [exact Hf | exact Md | solve_apart]|].
    split; [eapply rodata_clear_frame; [exact Hf | exact Mro | lia | lia | solve_apart]|].
    split; [eapply writable_frame; [exact Hf | exact Mw]|].
    eapply frame_mod_trans_same; [exact Mfr|]. eapply frame_mod_grow1; [| |exact Hf]; rewrite ?u_small by lia; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma tail_ok : forall lp (FPI' : FPState) R M, TINV lp FPI' R M ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x15c38) M rom) Q.
  Proof.
    intros lp FPI' R M HT.
    pose proof HT as (HRF & R21 & Hlp & HMF & (wf & Hwf) & (wc & Hwc)).
    pose proof (u64_range sp) as Hspr. pose proof Hwst as (W1 & W2 & W3 & W4).
    destruct (pack lp 1 FPI' R M wf wc HRF R21 Hlp ltac:(lia) HMF Hwf Hwc) as (HR & HF & HK & H64 & H96).
    pose proof (H64 : id _) as H64i. pose proof (H96 : id _) as H96i. clear H64 H96.
    pose proof HMF as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Mfr).
    run_fp 100%nat (@nil Z) noscr true.
    fin_ret.
    unfold Q, QP.
    lazymatch goal with |- exists _ _ _, @mkst ?I ?R' _ ?M' _ = _ /\ _ => exists I, R', M' end.
    split; [regv HR (1%bv:reg); rewrite_getr; reflexivity|].
    lift_id H64i HR. lift_id H96i HF.
    split; [exact (regs_same_on _ _ _ regs _ abi_kept H64i HR ltac:(vm_compute; reflexivity))|].
    split; [exact (fregs_same_on _ _ _ fp0 _ abi_fkept H96i HF ltac:(vm_compute; reflexivity))|].
    split.
    { eapply frame_mod_trans_same; [exact Mfr|].
      lazymatch goal with EQM : ?M' = mem_denot _ _ _ |- frame_mod _ ?M' _ => rewrite EQM end.
      frame_of_log [(SA (EVar 66) (-112), 128%Z)] ltac:(rewrite_getr). }
    kcell HK (EVar 66) 12%Z 4%nat (EExt false 0 4 (EVar 133)) HC12.
    kcell HK (EVar 66) 4%Z 4%nat (EExt false 0 4 (EVar 132)) HC4.
    split; [eexists; exact HC12|]. split; [eexists; exact HC4|].
    exists lp. split; [regv HR (10%bv:reg); reflexivity | exact Hlp].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac prove_memfix :=
    first
      [ assumption
      | lazymatch goal with |- MEMFIX ?Mx =>
          lazymatch goal with EQM : Mx = mem_denot _ ?M0 _, HM0 : MEMFIX ?M0 |- _ =>
            eapply (memfix_frame12 M0 Mx HM0); rewrite EQM;
            frame_of_log [(SA (EVar 66) 12, 4%Z)] ltac:(rewrite_getr)
          end end ].

  Ltac prove_cell b k :=
    first
      [ assumption
      | lazymatch goal with |- exists _, cell _ ?Mx _ _ _ =>
          lazymatch goal with HK : know_ok _ _ Mx _ |- _ =>
            let H := fresh "HC" in kcell_auto HK b k 4%nat H; eexists; exact H end end ].

  Ltac prove_TINV H64 H96 :=
    unfold TINV;
    split; [prove_regfix H64 H96|];
    split; [creg (21%bv:reg)|];
    split; [lia|];
    split; [prove_memfix|];
    split; [prove_cell (EVar 66) 4%Z | prove_cell (EVar 66) 12%Z].

  Ltac prove_INV H64 H96 :=
    unfold INV; split; [prove_TINV H64 H96 | split; [creg (22%bv:reg) | lia]].

  (* [comment removed for export] *)
  Ltac norm_latch Hl :=
    lazymatch type of Hl with branch_taken _ (edenot ?E0 _) _ = _ =>
      rewrite branch_taken_Z in Hl; cbv beta iota in Hl; cbn [edenot] in Hl; ev_simpl_in E0 Hl;
      rewrite_getr_in Hl; rewrite ?alu_add_lit in Hl; rewrite ?addw1_lit in Hl by lia; rewrite ?u_small in Hl by lia
    end.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma loop_ok : forall k i lp (FPI' : FPState) R M,
    INV i lp FPI' R M -> (n - i <= Z.of_nat k)%Z ->
    runs_to SEGS (mkst (FP:=FPI') R (Z_to_bv 64 0x15bb8) M rom) Q.
  Proof.
    induction k as [|k IH]; intros i lp FPI' R M HINV Hk.
    { exfalso. destruct HINV as (_ & _ & Hi). lia. }
    pose proof (u64_range sp) as Hspr. pose proof Hwst as (W1 & W2 & W3 & W4).
    (* [comment removed for export] *)
    assert (JOIN : forall (FPJ : FPState) RJ MJ, INV i lp FPJ RJ MJ ->
              runs_to SEGS (mkst (FP:=FPJ) RJ (Z_to_bv 64 0x15c10) MJ rom) Q).
    { intros FPJ RJ MJ HJ.
      pose proof HJ as ((HRF & R21 & Hlp & HMF & HWF & HWC) & R22 & Hi).
      destruct (pack_I _ _ _ _ _ HJ) as (wf & wc & HR & HF & HK & H64 & H96).
      pose proof (H64 : id _) as H64i. pose proof (H96 : id _) as H96i. clear H64 H96.
      (* [comment removed for export] *)
      run_fp 100%nat (@nil Z) noscr true; subst_triv.
      Ltac latch IH i lp' H64i H96i :=
        let Hl := fresh "Hl" in
        branch_case as Hl; norm_latch Hl;
        [ (* [comment removed for export] *)
          eapply (IH (i + 1)%Z lp'); [prove_INV H64i H96i | lia]
        | (* [comment removed for export] *)
          apply (tail_ok lp'); prove_TINV H64i H96i ].
      branch_case as Hj1.
      - latch IH i lp H64i H96i.
      - run_fp 100%nat (@nil Z) noscr true; subst_triv.
        branch_case as Hj2.
        + latch IH i lp H64i H96i.
        + run_fp 100%nat [0x15c34%Z] noscr true; subst_triv.
          latch IH i (i + 1)%Z H64i H96i. }
    (* [comment removed for export] *)
    pose proof HINV as ((HRF & R21 & Hlp & HMF & HWF & HWC) & R22 & Hi).
    destruct (pack_I _ _ _ _ _ HINV) as (wf & wc & HR & HF & HK & H64 & H96).
    pose proof (H64 : id _) as H64i. pose proof (H96 : id _) as H96i. clear H64 H96.
    pose proof (memfix_tc _ HMF) as HTC.
    run_fp 100%nat [0x136d8%Z] noscr true; subst_triv.
    call_ec 0x15bcc%Z HTC.
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc1; [apply (tail_ok lp); prove_TINV H64i H96i|].
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc2; [apply (tail_ok lp); prove_TINV H64i H96i|].
    run_fp 100%nat (@nil Z) noscr true; subst_triv.
    branch_case as Hc3;
      (run_fp 100%nat [0x15c10%Z] noscr true; subst_triv; branch_case as Hc4;
       [ apply JOIN; prove_INV H64i H96i
       | run_fp 100%nat [0x15c10%Z] noscr true; subst_triv; apply JOIN; prove_INV H64i H96i ]).
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Theorem fitlin_runs : runs_to SEGS (mkst (FP:=FPI) regs (Z_to_bv 64 0x15b14) mem rom) Q.
  Proof.
    pose proof (u64_range sp) as Hspr. pose proof (u64_range C) as HCr. pose proof (u64_range data) as Hdr.
    pose proof Hwst as (W1 & W2 & W3 & W4). pose proof Hdok as (Hlen & _).
    pose proof (writable_rodata_apart_S1 mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) Hwst Hro) as Hsro.
    destruct Hcw as (wc0 & Hwc0).
    set (E := Env (vals_ev (junk_vals regs ++ fjunk_vals fp0 ++ [wc0])) (blobs_ev [bs])).
    assert (HR0 : regs_ok E (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp0) by exact (fregs_ok_vars (junk_vals regs) fp0 _ (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_upd (sr_upd (sr_upd (sr_vars 0) 12 (EAlu ALU_ADD (EVar 2) (ELit 12)))
                                   13 (EAlu ALU_ADD (EVar 2) (ELit 8))) 14 (EAlu ALU_ADD (EVar 2) (ELit 4))) regs).
    { apply (regs_ok_pin E _ regs 14); [apply (regs_ok_pin E _ regs 13); [apply (regs_ok_pin E _ regs 12); [exact HR0|]|]|];
        cbn [edenot]; ev_simpl E; rewrite alu_add_lit, Hsp; [exact H12 | exact H13 | exact H14]. }
    pose proof (HR0 : id _) as HRid. clear HR0. pose proof (HF : id _) as HFid.
    assert (HK : know_ok SEGS E mem [KAlign (EVar 2) 16; KRange (EVar 11) 2 16777216; KRange (EVar 2) 112 (2^64 - 16);
                                    KWord (SA (EVar 2) 12) 4 (EVar 64); KWr (SA (EVar 2) (-112)) 128]).
    { constructor; [apply kalign_intro; [lia | cbn [edenot]; ev_simpl E; rewrite Hsp; exact Hal16]|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite H11, u_small by lia; lia|].
      constructor; [apply krange_intro; cbn [edenot]; ev_simpl E; rewrite Hsp; lia|].
      constructor; [eapply (kword_intro SEGS E mem (EVar 2) sp 12 4 (EVar 64) wc0);
                    [cbn [edenot]; ev_simpl E; exact Hsp | cbn [edenot]; ev_simpl E; reflexivity | lia | lia | lia | lia | exact Hwc0]|].
      constructor; [apply (kwr_intro SEGS E mem (EVar 2) sp (-112) 128);
                    [cbn [edenot]; ev_simpl E; exact Hsp | lia | lia | lia |
                     replace (bv_unsigned sp + -112)%Z with (bv_unsigned sp - 112)%Z by lia; exact W4]|].
      constructor. }
    (* [comment removed for export] *)
    run_fp 100%nat [0x136d8%Z] noscr true.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      assert (HFRA1 : frame_mod mem M1 [(Z_to_bv 64 (bv_unsigned sp - 112), 128%Z)])
        by (lazymatch goal with EQM : M1 = _ |- _ => rewrite EQM end;
            frame_of_log [(SA (EVar 2) (-112), 128%Z)] ltac:(rewrite_getr));
      assert (HTC : table_curve SEGS M1 data len (bv_unsigned C) n t8 t16 /\ data_ok M1 data len bs /\ rodata_clear M1 0x103ec 0x1048c)
    end.
    { split; [|split; [eapply data_ok_frame; [exact HFRA1 | exact Hdok | solve_apart]
                      |eapply rodata_clear_frame; [exact HFRA1 | exact Hro | lia | lia | solve_apart]]].
      unfold table_curve. split; [split; [exact Hn32|]|split; [|split; [|split; [exact Hnr|split; [exact H8|split; [exact H16|exact Hsome]]]]]].
      - eapply cell_frame; [exact HFRA1 | exact Hn | lia | change (Z.of_nat 4) with 4%Z; lia | change (Z.of_nat 4) with 4%Z; solve_apart].
      - eapply cell64_frame; [exact HFRA1 | exact Ht8 | lia | lia | solve_apart].
      - eapply cell64_frame; [exact HFRA1 | exact Ht16 | lia | lia | solve_apart]. }
    call_ec 0x15b90%Z HTC.
    (* [comment removed for export] *)
    run_fp 100%nat [0x15bb8%Z] noscr true.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M2 _) _ =>
      lazymatch goal with EQM2 : M2 = mem_denot _ ?M1 _, HFRA1 : frame_mod mem ?M1 _ |- _ =>
      assert (HFRA : frame_mod mem M2 [(Z_to_bv 64 (bv_unsigned sp - 112), 128%Z)])
        by (eapply frame_mod_trans_same; [exact HFRA1|]; rewrite EQM2;
            frame_of_log [(SA (EVar 2) (-112), 128%Z)] ltac:(rewrite_getr))
    end end.
    eapply (loop_ok (Z.to_nat (n - 1)) 1 1); [| rewrite Z2Nat.id by lia; lia].
    unfold INV, TINV.
    split; [| split; [creg (22%bv:reg) | lia]].
    split; [prove_regfix HRid HFid|].
    split; [creg (21%bv:reg)|].
    split; [lia|].
    split.
    { kcell_auto HK (EVar 2) (-8)%Z 8%nat M1. kcell_auto HK (EVar 2) (-16)%Z 8%nat M2.
      kcell_auto HK (EVar 2) (-24)%Z 8%nat M3. kcell_auto HK (EVar 2) (-32)%Z 8%nat M4.
      kcell_auto HK (EVar 2) (-40)%Z 8%nat M5. kcell_auto HK (EVar 2) (-48)%Z 8%nat M6.
      kcell_auto HK (EVar 2) (-56)%Z 8%nat M7. kcell_auto HK (EVar 2) (-64)%Z 8%nat M8.
      kcell_auto HK (EVar 2) (-72)%Z 8%nat M9. kcell_auto HK (EVar 2) (-80)%Z 8%nat M10.
      kcell_auto HK (EVar 2) (-88)%Z 8%nat M11. kcell_auto HK (EVar 2) (-96)%Z 8%nat M12.
      kcell_auto HK (EVar 2) (-104)%Z 8%nat M13.
      unfold MEMFIX, cell64.
      repeat (split; [assumption|]).
      split; [eapply cell_frame; [exact HFRA | exact Hn | lia | change (Z.of_nat 4) with 4%Z; lia | change (Z.of_nat 4) with 4%Z; solve_apart]|].
      split; [eapply cell_frame; [exact HFRA | exact Ht8 | lia | change (Z.of_nat 8) with 8%Z; lia | change (Z.of_nat 8) with 8%Z; solve_apart]|].
      split; [eapply cell_frame; [exact HFRA | exact Ht16 | lia | change (Z.of_nat 8) with 8%Z; lia | change (Z.of_nat 8) with 8%Z; solve_apart]|].
      split; [eapply data_ok_frame; [exact HFRA | exact Hdok | solve_apart]|].
      split; [eapply rodata_clear_frame; [exact HFRA | exact Hro | lia | lia | solve_apart]|].
      split; [eapply writable_frame; [exact HFRA | exact Hwst]|].
      exact HFRA. }
    split; [prove_cell (EVar 2) 4%Z | prove_cell (EVar 2) 12%Z].
  Qed.

End Proof.

Theorem fit_linear_src1 :
  eval_curve_contract Plain.M.loaded_segments wp3_src1 -> fit_linear_contract Plain.M.loaded_segments wp3_src1.
Proof.
  intros Hev data len bs sp C n t8 t16 FPI regs mem rom ret Hra Hret PRE.
  unfold fitlin_pre in PRE. cbv zeta in PRE. cbn [w3_fitlin_fr w3_ro_lo w3_ro_hi wp3_src1] in PRE.
  destruct PRE as (Hsp & Hc & H11 & H12 & H13 & H14 & Hal16 & Hwst & Hcw & Hcal & Hc32 &
                   ([Hn32 Hn] & Ht8 & Ht16 & Hnr & H8 & H16 & Hsome) & Hdok & Hro & Hd1 & Hd2).
  change (112 + 16)%Z with 128%Z in Hwst.
  apply runs_to_contract.
  eapply runs_to_mono; [| exact (fitlin_runs Hev FPI regs mem rom ret sp C data t8 t16 n len bs Hra Hret Hsp Hc H11 H12 H13 H14
                                  Hal16 Hwst Hcw Hcal Hc32 Hn32 Hn Ht8 Ht16 Hnr H8 H16 Hsome Hdok Hro Hd1 Hd2)].
  intros st' (FPI' & regs' & mem' & -> & K1 & K2 & P). exists FPI', regs', mem'.
  split; [reflexivity|]. split; [exact K1|]. split; [exact K2|].
  unfold fitlin_post. cbv zeta. cbn [w3_fitlin_fr wp3_src1]. change (112 + 16)%Z with 128%Z. exact P.
Qed.
