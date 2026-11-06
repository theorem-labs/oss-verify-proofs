(* Copyright 2026 Anthropic PBC *)
(* SPDX-License-Identifier: Apache-2.0 OR MIT *)
(* Modified by Theorem Labs, 2026-10: ported to the binaries of release 2026.10.0 and LPS 2afba80c; the theorem statements are restated in the form this release states them. *)
(* [comment removed for export] *)
From Stdlib Require ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibTagsSpec LibWP1Spec LibWP2Spec LibTagsLib LibTagsCall LibFPLib LibParseLib.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf Require SymDriveLB.
From Stdlib Require Zify.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require SymDriveLZ.
Unset Nia Cache.  (* [comment removed for export] *)

Module LibParseDefsS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

(* [comment removed for export] *)
Lemma roseg_src1 : roseg_ok SEGS (Z_to_bv 64 0x103ec) (Z.to_nat (0x1048c - 0x103ec)) = true.
Proof. vm_compute. reflexivity. Qed.

(* [comment removed for export] *)
Ltac frk HF HFK :=
  intros r Hin; repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
  (etransitivity; [| apply HFK; cbn [In]; clear; repeat (first [left; reflexivity | right])]);
  first [ fregv HF (19%bv:reg); reflexivity | fregv HF (20%bv:reg); reflexivity
        | fregv HF (21%bv:reg); reflexivity | fregv HF (22%bv:reg); reflexivity
        | fregv HF (23%bv:reg); reflexivity | fregv HF (24%bv:reg); reflexivity
        | fregv HF (25%bv:reg); reflexivity | fregv HF (26%bv:reg); reflexivity
        | fregv HF (27%bv:reg); reflexivity ].

(* [comment removed for export] *)
Ltac common HR HF H2 H3 H4 H8 HFK :=
  split; [regv HR (2%bv:reg); rewrite ?H2; try reflexivity; try lia|];
  split; [regv HR (3%bv:reg); exact H3|];
  split; [regv HR (4%bv:reg); exact H4|];
  split; [regv HR (8%bv:reg); exact H8|];
  frk HF HFK.

Section Defs.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).

  (* [comment removed for export] *)
  Definition PENV : Prop :=
    let p := bv_unsigned P in let q := bv_unsigned prio in let s := bv_unsigned sp in
    let dd := bv_unsigned data in
    getr regs 1 = ret /\ ret_ok ret /\ getr regs 2 = sp /\
    data_ok mem data len bs /\
    cell32 SEGS mem q 0 /\ cell32 SEGS mem (q + 4) 1 /\ (q mod 4 = 0)%Z /\ (0 < q)%Z /\ (q + 8 <= 2 ^ 64)%Z /\
    writable SEGS mem p 976 /\ (p mod 8 = 0)%Z /\ (0 < p)%Z /\
    (s mod 16 = 0)%Z /\ writable SEGS mem (s - 656) 656 /\
    rodata_clear mem 0x103ec 0x1048c /\
    (dd + len <= s - 656 \/ s <= dd)%Z /\
    (dd + len <= p \/ p + 976 <= dd)%Z /\
    (dd + len <= q \/ q + 8 <= dd)%Z /\
    (s <= p \/ p + 976 <= s - 656)%Z /\
    (s <= q \/ q + 8 <= s - 656)%Z /\
    (p + 976 <= q \/ q + 8 <= p)%Z.

  Definition BIG : list (word * Z) := [(Z_to_bv 64 (bv_unsigned sp - 656), 656%Z); (P, 976%Z)].

  (* [comment removed for export] *)
  Definition Q (st' : machine_state) : Prop :=
    exists (FPI' : FPState) regs' mem',
      st' = mkst (FP:=FPI') regs' ret mem' rom /\
      regs_kept abi_kept regs regs' /\
      fregs_kept abi_fkept (fp_regs (FPState:=FP0)) (fp_regs (FPState:=FPI')) /\
      (frame_mod mem mem' BIG /\
       exists r, getr regs' 10 = Z_to_bv 64 r /\ (r = 0 \/ r = 1)%Z /\
         (r = 1%Z -> parsed_ok SEGS mem' data len bs (bv_unsigned P))).

  (* [comment removed for export] *)
  Definition SAVED (M : word -> option byte) : Prop :=
    let s := bv_unsigned sp in
    cell64 SEGS M (s - 8) (getr regs 1) /\ cell64 SEGS M (s - 16) (getr regs 8) /\
    cell64 SEGS M (s - 24) (getr regs 9) /\ cell64 SEGS M (s - 32) (getr regs 18) /\
    cell64 SEGS M (s - 40) (getr regs 19) /\ cell64 SEGS M (s - 48) (getr regs 20) /\
    cell64 SEGS M (s - 56) (getr regs 21) /\ cell64 SEGS M (s - 64) (getr regs 22) /\
    cell64 SEGS M (s - 72) (getr regs 23) /\ cell64 SEGS M (s - 80) (getr regs 24) /\
    cell64 SEGS M (s - 88) (getr regs 25) /\ cell64 SEGS M (s - 96) (getr regs 26) /\
    cell64 SEGS M (s - 104) (getr regs 27) /\
    cell64 SEGS M (s - 112) (reg_get (fp_regs (FPState:=FP0)) 8) /\
    cell64 SEGS M (s - 120) (reg_get (fp_regs (FPState:=FP0)) 9) /\
    cell64 SEGS M (s - 128) (reg_get (fp_regs (FPState:=FP0)) 18).

  (* [comment removed for export] *)
  Definition COMMON (FPI : FPState) (R : bvmap 5 word) : Prop :=
    (bv_unsigned (getr R 2) = bv_unsigned sp - 320)%Z /\
    getr R 3 = getr regs 3 /\ getr R 4 = getr regs 4 /\ getr R 8 = P /\
    (forall r, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
       reg_get (fp_regs (FPState:=FPI)) r = reg_get (fp_regs (FPState:=FP0)) r).

  Lemma SAVED_frame : forall M M' rs,
    SAVED M -> frame_mod M M' rs -> apart (bv_unsigned sp - 128) 128 rs -> (128 <= bv_unsigned sp)%Z -> SAVED M'.
  Proof using P mem rom.
    intros M M' rs HS Hf Hap Hsp. pose proof (u64_range sp).
    unfold SAVED in *. cbv zeta in *.
    repeat match goal with
    | |- _ /\ _ => split
    end;
    repeat match goal with
    | H : _ /\ _ |- _ => destruct H
    end;
    (eapply cell64_frame; [exact Hf | eassumption | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]]).
  Qed.

  Hypothesis HE : PENV.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma penv_rodata_apart : apart 0x103ec 0xa0 BIG.
  Proof using HE rom.
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WP & _ & _ & _ & WS & RO & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    pose proof (writable_rodata_apart SEGS mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) roseg_src1 WP RO) as A1.
    pose proof (writable_rodata_apart SEGS mem _ _ 0x103ec 0x1048c ltac:(lia) ltac:(lia) ltac:(lia) roseg_src1 WS RO) as A2.
    destruct WS as (S1 & _). unfold BIG. solve_apart.
  Qed.

  Lemma penv_data : forall M, frame_mod mem M BIG -> data_ok M data len bs.
  Proof using HE rom.
    intros M Hf. destruct HE as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & _ & _ & _ & WS & _ & A1 & A2 & _).
    pose proof (u64_range sp). pose proof (u64_range P). destruct WS as (S1 & _). pose proof D as (D1 & _).
    eapply data_ok_frame; [exact Hf | exact D | unfold BIG; solve_apart].
  Qed.

  Lemma penv_prio : forall M, frame_mod mem M BIG ->
    cell32 SEGS M (bv_unsigned prio) 0 /\ cell32 SEGS M (bv_unsigned prio + 4) 1.
  Proof using HE rom.
    intros M Hf. destruct HE as (_ & _ & _ & _ & C0 & C4 & _ & Q0 & Q8 & WP & _ & _ & _ & WS & _ & _ & _ & _ & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio). destruct WS as (S1 & _).
    split.
    - eapply cell32_frame; [exact Hf | exact C0 | lia | lia | unfold BIG; solve_apart].
    - eapply cell32_frame; [exact Hf | exact C4 | lia | lia | unfold BIG; solve_apart].
  Qed.

  Lemma penv_wP : forall M, frame_mod mem M BIG -> writable SEGS M (bv_unsigned P) 976.
  Proof using HE.
    intros M Hf. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & WP & _).
    eapply writable_frame; [exact Hf | exact WP].
  Qed.

  Lemma penv_wS : forall M, frame_mod mem M BIG -> writable SEGS M (bv_unsigned sp - 656) 656.
  Proof using HE.
    intros M Hf. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & WS & _).
    eapply writable_frame; [exact Hf | exact WS].
  Qed.

  Lemma penv_ro : forall M, frame_mod mem M BIG -> rodata_clear M 0x103ec 0x1048c.
  Proof using HE rom.
    intros M Hf. destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & RO & _).
    eapply rodata_clear_frame; [exact Hf | exact RO | lia | lia | ].
    replace (0x1048c - 0x103ec)%Z with 0xa0%Z by reflexivity. apply penv_rodata_apart.
  Qed.


  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma gettag_pre_at : forall Mx (FP : FPState) R (k sig psz tc : Z),
    frame_mod mem Mx BIG ->
    cell64 SEGS Mx (bv_unsigned P) data -> cell32 SEGS Mx (bv_unsigned P + 20) tc -> tags_ok len bs tc psz ->
    getr R 10 = P -> getr R 11 = Z_to_bv 64 sig -> getr R 12 = Z_to_bv 64 (bv_unsigned sp - 320 + k) ->
    (0 <= sig < 2 ^ 32)%Z -> (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    gettag_pre SEGS data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 320 + k)) FP R Mx.
  Proof using HE rom.
    intros Mx FP R k sig psz tc Hf C0 C20 Ht R10 R11 R12 Hsig Hk.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4). pose proof D as (D1 & _).
    unfold gettag_pre. cbv zeta. rewrite !u_small_frame by lia.
    split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact Hsig|].
    split; [apply penv_data; exact Hf|].
    split; [exact C0|]. split; [exact C20|]. split; [exact Ht|].
    split; [lia|]. split; [lia|]. split; [exact Pal|].
    split; [lia|]. split; [clear - Sal Hk; lia|].
    split; [eapply writable_sub; [apply penv_wS; exact Hf | lia | lia | lia]|].
    split; lia.
  Qed.

  Lemma gettag_big : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] -> frame_mod Mx My BIG.
  Proof using HE rom.
    intros Mx My k Hk Hfr. pose proof (u64_range sp).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
    eapply frame_mod_of_covered; [| exact Hfr]. unfold BIG. solve_covered.
  Qed.

  (* [comment removed for export] *)
  Lemma saved_tag : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    SAVED Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] -> SAVED My.
  Proof using HE rom.
    intros Mx My k Hk HS Hfr. pose proof (u64_range sp).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
    eapply SAVED_frame; [exact HS | exact Hfr | solve_apart | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma parsed_tag : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    parsed_ok SEGS Mx data len bs (bv_unsigned P) ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] ->
    parsed_ok SEGS My data len bs (bv_unsigned P).
  Proof using HE rom.
    intros Mx My k Hk Hpo Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    eapply parsed_ok_frame; [exact Hfr | exact Hpo | lia | lia | solve_apart | solve_apart | solve_apart].
  Qed.

  Lemma cell8_P_tag : forall Mx My (k o v : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z -> (0 <= o < 976)%Z ->
    cell8 SEGS Mx (bv_unsigned P + o) v ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] ->
    cell8 SEGS My (bv_unsigned P + o) v.
  Proof using HE rom.
    intros Mx My k o v Hk Ho Hc Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    eapply cell8_frame; [exact Hfr | exact Hc | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Exit.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (v : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis H15 : getr R 15 = Z_to_bv 64 v.
    Hypothesis Hv : (v = 0 \/ v = 1)%Z.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis Hok : v = 1%Z -> parsed_ok SEGS M data len bs (bv_unsigned P).

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
             ++ [getr regs 1; getr regs 8; getr regs 9; getr regs 18; getr regs 19; getr regs 20;
                 getr regs 21; getr regs 22; getr regs 23; getr regs 24; getr regs 25; getr regs 26;
                 getr regs 27; reg_get (fp_regs (FPState:=FP0)) 8; reg_get (fp_regs (FPState:=FP0)) 9;
                 reg_get (fp_regs (FPState:=FP0)) 18])) (blobs_ev [bs]).
    (* [comment removed for export] *)

    Definition kn_exit : list kentry :=
      [KRange (EVar 2) 0 (2^64 - 320);
       KWord (SA (EVar 2) 312) 8 (EVar 64); KWord (SA (EVar 2) 304) 8 (EVar 65);
       KWord (SA (EVar 2) 296) 8 (EVar 66); KWord (SA (EVar 2) 288) 8 (EVar 67);
       KWord (SA (EVar 2) 280) 8 (EVar 68); KWord (SA (EVar 2) 272) 8 (EVar 69);
       KWord (SA (EVar 2) 264) 8 (EVar 70); KWord (SA (EVar 2) 256) 8 (EVar 71);
       KWord (SA (EVar 2) 248) 8 (EVar 72); KWord (SA (EVar 2) 240) 8 (EVar 73);
       KWord (SA (EVar 2) 232) 8 (EVar 74); KWord (SA (EVar 2) 224) 8 (EVar 75);
       KWord (SA (EVar 2) 216) 8 (EVar 76);
       KWord (SA (EVar 2) 208) 8 (EVar 77); KWord (SA (EVar 2) 200) 8 (EVar 78);
       KWord (SA (EVar 2) 192) 8 (EVar 79)].

    Lemma kn_exit_ok : know_ok SEGS E M kn_exit.
    Proof using HC HE HS rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK). pose proof (u64_range sp).
      destruct HE as (Hra & Hret & Hsp & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & S2 & S3 & S4) & _).
      unfold SAVED in HS. cbv zeta in HS.
      destruct HS as (C1 & C8 & C9 & C18 & C19 & C20 & C21 & C22 & C23 & C24 & C25 & C26 & C27 & F8 & F9 & F18).
      unfold cell64, cell in *.
      unfold kn_exit, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil];
      [ apply krange_intro; cbn [edenot]; ev_simpl E; lia | ..];
      (eapply (kword_intro SEGS E M (EVar 2) (getr R 2));
       [ cbn [edenot]; ev_simpl E; reflexivity
       | cbn [edenot]; ev_simpl E; reflexivity
       | lia | lia | lia | cbn [Z.of_nat Pos.of_succ_nat Pos.succ]; lia
       | rewrite H2;
         lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => ring_simplify a end;
         first [eassumption
               | lazymatch goal with |- rdn _ _ (Z_to_bv 64 ?a) _ = _ => idtac "KWEXIT" a end ] ]).
    Qed.

    Lemma exit_ok : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13e20) M rom) Q.
    Proof using H15 HC HE HS Hf Hok Hv.
      destruct HC as (H2 & H3 & H4 & H8 & HFK). pose proof (u64_range sp) as Rsp.
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_exit_ok as HK.
      (* [comment removed for export] *)
      pin_reg HR (15%bv:reg) (ELit v) by (rewrite (HR (15%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H15).
      destruct Hv as [-> | ->];
        run_fp 40%nat (@nil Z) noscr false;
        fin_ret;
        lazymatch goal with
        | HR : regs_ok _ ?sr ?R2, HF : fregs_ok _ ?sfr (@fp_regs ?FP2), HK : know_ok _ _ ?M2 _ |- _ =>
          exists FP2, R2, M2;
          split; [regv HR (1%bv:reg); rewrite Hra; reflexivity|];
          split; [ unfold regs_kept, abi_kept; intros r Hin;
                   repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
                   [ regv_lin HR (2%bv:reg); rewrite H2, <- (Z_to_bv_bv_unsigned 64 (getr regs 2)), Hsp; f_equal; lia
                   | regv HR (3%bv:reg); exact H3
                   | regv HR (4%bv:reg); exact H4
                   | regv HR (8%bv:reg); reflexivity
                   | regv HR (9%bv:reg); reflexivity
                   | regv HR (18%bv:reg); reflexivity
                   | regv HR (19%bv:reg); reflexivity
                   | regv HR (20%bv:reg); reflexivity
                   | regv HR (21%bv:reg); reflexivity
                   | regv HR (22%bv:reg); reflexivity
                   | regv HR (23%bv:reg); reflexivity
                   | regv HR (24%bv:reg); reflexivity
                   | regv HR (25%bv:reg); reflexivity
                   | regv HR (26%bv:reg); reflexivity
                   | regv HR (27%bv:reg); reflexivity ] |];
          split; [ unfold fregs_kept, abi_fkept; intros r Hin;
                   repeat (destruct Hin as [<- | Hin]); try (solve [destruct Hin]);
                   [ fregv HF (8%bv:reg); reflexivity
                   | fregv HF (9%bv:reg); reflexivity
                   | fregv HF (18%bv:reg); reflexivity
                   | .. ];
                   (etransitivity; [| apply HFK; cbn [In]; clear; repeat (first [left; reflexivity | right])]);
                   first [ fregv HF (19%bv:reg); reflexivity | fregv HF (20%bv:reg); reflexivity
                         | fregv HF (21%bv:reg); reflexivity | fregv HF (22%bv:reg); reflexivity
                         | fregv HF (23%bv:reg); reflexivity | fregv HF (24%bv:reg); reflexivity
                         | fregv HF (25%bv:reg); reflexivity | fregv HF (26%bv:reg); reflexivity
                         | fregv HF (27%bv:reg); reflexivity ] |];
          split; [exact Hf|];
          eexists; split; [regv HR (10%bv:reg); reflexivity|]; split; [lia | exact Hok]
        end.
    Qed.
  End Exit.

  (* [comment removed for export] *)
  Lemma fail_ok : forall (FPI : FPState) R M,
    COMMON FPI R -> SAVED M -> frame_mod mem M BIG ->
    runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13e1c) M rom) Q.
  Proof using HE.
    intros FPI R M HC HS Hf.
    pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
    set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs])).
    assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
    assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
    assert (HK : know_ok SEGS E M []) by constructor.
    run_fp 1%nat [0x13e20%Z] noscr false.
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ _ _) _ => apply (exit_ok I R' M 0) end.
    - common HR HF H2 H3 H4 H8 HFK.
    - regv HR (15%bv:reg). reflexivity.
    - left; reflexivity.
    - exact HS.
    - exact Hf.
    - intros; exfalso; lia.
  Qed.
End Defs.
End LibParseDefsS1.

Module LibParseFS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
#[local] Abbreviation W := tags_src1.

Section F.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.


  Section Tail.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (h965 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis Hpo : parsed_ok SEGS M data len bs (bv_unsigned P).
    Hypothesis C965 : cell8 SEGS M (bv_unsigned P + 965) h965.
    Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_tail (a b c : Z) : list kentry :=
      [KRange (EVar 8) 1 (2^64 - 976);
       KWord (SA (EVar 8) 966) 1 (ELit a);
       KWord (SA (EVar 8) 964) 1 (ELit b);
       KWord (SA (EVar 8) 965) 1 (ELit c)].

    Lemma kn_tail_ok : forall a b,
      cell8 SEGS M (bv_unsigned P + 966) a -> cell8 SEGS M (bv_unsigned P + 964) b ->
      know_ok SEGS E M (kn_tail a b h965).
    Proof.
      intros a b [Ra Ca] [Rb Cb]. destruct C965 as [Rc Cc]. unfold cell in Ca, Cb, Cc.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & P0 & _).
      unfold kn_tail. pose proof (u64_range P).
      unfold know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H8. lia.
      - eapply (kword_intro SEGS E M (EVar 8) P 966 1 (ELit a) (Z_to_bv 64 a)); cbn; try lia; auto.
      - eapply (kword_intro SEGS E M (EVar 8) P 964 1 (ELit b) (Z_to_bv 64 b)); cbn; try lia; auto.
      - eapply (kword_intro SEGS E M (EVar 8) P 965 1 (ELit h965) (Z_to_bv 64 h965)); cbn; try lia; auto.
    Qed.

    Lemma tailF_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1422c) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof Hpo as Hpo'.
      destruct Hpo' as (psz & tc & htrc & hasA2B & _ & _ & _ & _ & _ & C964 & R964 & C966 & R966 & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof (kn_tail_ok hasA2B htrc C966 C964) as HK.
      destruct R966 as [-> | ->]; destruct R964 as [-> | ->]; destruct R965 as [-> | ->];
        run_fp 20%nat [0x13e1c%Z; 0x13e20%Z] noscr false;
        first
          [ (* [comment removed for export] *)
            lazymatch goal with |- runs_to _ (@mkst ?I ?R' (Z_to_bv 64 0x13e1c) ?M' _) _ =>
              apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
              [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ] end
          | (exit_with 0%Z HR HF H2 H3 H4 H8 HFK HS Hf; [intros; exfalso; lia])
          | (exit_with 1%Z HR HF H2 H3 H4 H8 HFK HS Hf; [intros _; exact Hpo]) ].
    Qed.
  End Tail.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (h965 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis Hpo : parsed_ok SEGS M data len bs (bv_unsigned P).
    Hypothesis C965 : cell8 SEGS M (bv_unsigned P + 965) h965.
    Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [data; Z_to_bv 64 len])) (blobs_ev [bs]).

    Definition kn_F : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KRange (EVar 64) 1 (2^47);
       KRange (EVar 65) 0 (2^26);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976].

    Lemma kn_F_ok : know_ok SEGS E M kn_F.
    Proof.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
      destruct D as (D1 & D2 & D3 & D4 & D5).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      unfold kn_F, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply krange_intro; cbn. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
    Qed.

    Lemma blockF_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x141cc) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      pose proof Hpo as Hpo'.
      destruct Hpo' as (psz & tc & htrc & hasA2B & C0 & C8 & C20 & Htags & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_F_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 20%nat [0x137b4%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz 0x63696370%Z (Z_to_bv 64 (bv_unsigned sp - 320 + 144)) I R1 Mx ro (Z_to_bv 64 0x141e4));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 144 _ psz tc Hf C0 C20 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS Hfr) as HS1.
      pose proof (parsed_tag regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hpo Hfr) as Hpo1.
      pose proof (cell8_P_tag regs mem rom ret sp data prio P len bs HE _ _ 144 965 h965 ltac:(lia) ltac:(lia) C965 Hfr) as C965a.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 76) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1422c%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (tailF_run I R2 mq1 h965) end;
          [ common HR HF H2 H3 H4 H8 HFK | exact HS1 | exact Hf1 | exact Hpo1 | exact C965a | exact R965 ]. }
      (* [comment removed for export] *)
      destruct (Htag eq_refl) as ((sz & buf & Csz & Cbuf & Hsz4 & Hin) & Csig & (ty & Cty)).
      rewrite !u_small_frame in Csz, Cbuf, Csig, Cty by lia.
      destruct Csz as [Rsz Csz]. destruct Cty as [Rty Cty]. unfold cell64, cell in Cbuf. unfold cell in Csz, Cty.
      destruct Hin as (In1 & In2 & In3). pose proof (u64_range buf) as Rbuf.
      add_krange (EVar 76) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      env_extend [Z_to_bv 64 ty; Z_to_bv 64 sz; buf].
      lazymatch type of HK with know_ok _ ?E2 _ ?kn =>
        assert (HK2 : know_ok SEGS E2 mq1
          ([KWord (SA (EVar 2) 148) 4 (EVar 130);
            KWord (SA (EVar 2) 152) 4 (EVar 131);
            KWord (SA (EVar 2) 160) 8 (EVar 132);
            KRange (EVar 130) 0 (2^32 - 1);
            KRange (EVar 132) 1 (2^47)] ++ kn ++
           [KBlobD (SA (EVar 64) 0) (EVar 65) 0]));
        [ apply know_ok_app; [| apply know_ok_app; [exact HK|]]; unfold know_ok;
          repeat (apply Forall_cons); try apply Forall_nil;
          [ eapply (kword_intro SEGS E2 mq1 (EVar 2) (getr R 2) 148 4 (EVar 130) (Z_to_bv 64 ty)); cbn; try lia; auto;
            replace (bv_unsigned (getr R 2) + 148)%Z with (bv_unsigned sp - 320 + 144 + 4)%Z by lia; exact Cty
          | eapply (kword_intro SEGS E2 mq1 (EVar 2) (getr R 2) 152 4 (EVar 131) (Z_to_bv 64 sz)); cbn; try lia; auto;
            replace (bv_unsigned (getr R 2) + 152)%Z with (bv_unsigned sp - 320 + 144 + 8)%Z by lia; exact Csz
          | eapply (kword_intro SEGS E2 mq1 (EVar 2) (getr R 2) 160 8 (EVar 132) buf); cbn; try lia; auto;
            replace (bv_unsigned (getr R 2) + 160)%Z with (bv_unsigned sp - 320 + 144 + 16)%Z by lia; exact Cbuf
          | apply krange_intro; cbn; rewrite u_small by lia; lia
          | apply krange_intro; cbn; lia
          | cbn [kentry_ok]; unfold flat, estart, elenZ; cbn [a_base a_off edenot]; ev_simpl E2;
            rewrite u_small by lia; split; [lia|]; split; [exact D2|]; intros i Hi; rewrite Z.add_0_r;
            eapply (proj2 (proj2 (proj2 (proj2 (penv_data regs mem rom ret sp data prio P len bs HE mq1 Hf1))))); exact Hi ]
        | clear HK; rename HK2 into HK; cbn [app] in HK ]
      end.
      run_fp 30%nat [0x13e20%Z; 0x1422c%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hty.
      { exit_with 0%Z HR HF H2 H3 H4 H8 HFK HS1 Hf1. intros; exfalso; lia. }
      destruct (Z_lt_le_dec sz 12) as [Hsz|Hsz].
      { (* [comment removed for export] *)
        add_krange (EVar 131) 4%Z 11%Z by (rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e20%Z] noscr false.
        exit_with 0%Z HR HF H2 H3 H4 H8 HFK HS1 Hf1. intros; exfalso; lia. }
      add_krange (EVar 131) 12%Z (2^26)%Z by (rewrite u_small by lia; lia).
      lazymatch type of HK with know_ok _ ?E2 _ ?kn =>
        assert (HK2 : know_ok SEGS E2 mq1 (KDisj (SA (EVar 8) 0) 976 (SA (EVar 132) 8) 4 :: kn));
        [ apply know_ok_cons; [| exact HK];
          cbn [kentry_ok]; unfold estart; cbn [a_base a_off edenot]; ev_simpl E2; rewrite H8; lia
        | clear HK; rename HK2 into HK ]
      end.
      run_fp 30%nat [0x1422c%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 960, 4%Z); (SA (EVar 8) 968, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (tailF_run I R2 M2 h965) end.
      - common HR HF H2 H3 H4 H8 HFK.
      - eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS1 | exact Hfr2 | solve_apart | lia].
      - eapply frame_mod_trans_same; [exact Hf1|]. eapply frame_mod_of_covered; [| exact Hfr2]. unfold LibParseDefsS1.BIG. solve_covered.
      - eapply parsed_ok_frame; [exact Hfr2 | exact Hpo1 | lia | lia | solve_apart | solve_apart | solve_apart].
      - eapply cell8_frame; [exact Hfr2 | exact C965a | lia | lia | solve_apart].
      - exact R965.
    Qed.
  End Run.
End F.
End LibParseFS1.

Module LibParseES1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac perf_el3_core := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs;
  first [ Zify.zify_post_hook; xlia zchecker | lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with true => idtac end; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ].
Local Ltac perf_el3_clear_all := clear.  (* [comment removed for export] *)
Local Ltac perf_el3_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif perf_el3_has_var then perf_el3_core
  else first [ solve [perf_el3_clear_all; perf_el3_core] | perf_el3_core ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W2 := wp2_src1.

Section E.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc h964 h965 h966 : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.
  Hypothesis R964 : (h964 = 0 \/ h964 = 1)%Z.
  Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.
  Hypothesis R966 : (h966 = 0 \/ h966 = 1)%Z.

  (* [comment removed for export] *)
  Definition EFACTS (Mx : word -> option byte) : Prop :=
    let p := bv_unsigned P in let s := bv_unsigned sp in
    cell64 SEGS Mx (s - 304) (Z_to_bv 64 2) /\ cell64 SEGS Mx (s - 312) raw /\
    cell64 SEGS Mx p data /\ cell32 SEGS Mx (p + 8) psz /\ cell32 SEGS Mx (p + 20) tc /\
    Forall (fun off => curve_ok SEGS Mx data len (p + off)) [24; 56; 88]%Z /\
    Forall (fun off => curve_ok SEGS Mx data len (p + 160 + off)) a2b_curve_offsets /\
    zero Mx (p + 560) 400 /\
    cell8 SEGS Mx (p + 964) h964 /\ cell8 SEGS Mx (p + 965) h965 /\ cell8 SEGS Mx (p + 966) h966 /\
    (h966 <> 0%Z -> grid_ok_A2B SEGS Mx data len p).

  Lemma EFACTS_frame : forall Mx My rs,
    EFACTS Mx -> frame_mod Mx My rs ->
    apart (bv_unsigned sp - 312) 16 rs -> apart (bv_unsigned P) 976 rs -> EFACTS My.
  Proof using HE.
    intros Mx My rs (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12) Hf As Ap.
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _).
    unfold EFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply a2b_curves_frame; [exact Hf | exact F7 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply zero_frame; [exact Hf | exact F8 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F10 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F11 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    intros Hnz. eapply grid_ok_A2B_frame; [exact Hf | exact (F12 Hnz) | lia | lia | exact Ap].
  Qed.

  Lemma EFACTS_tag : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    EFACTS Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] -> EFACTS My.
  Proof using HE.
    intros Mx My k Hk HF Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    eapply EFACTS_frame; [exact HF | exact Hfr | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma EFACTS_parsed : forall Mx, EFACTS Mx -> parsed_ok SEGS Mx data len bs (bv_unsigned P).
  Proof using HE Htags R964 R966.
    intros Mx (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _).
    exists psz, tc, h964, h966.
    split; [exact F3|]. split; [exact F4|]. split; [exact F5|]. split; [exact Htags|].
    split; [apply curves_ok_assemble; [exact F6 | exact F7 | apply zero_b2a_curves; [exact F8 | lia | lia]]|].
    split; [exact F9|]. split; [exact R964|]. split; [exact F11|]. split; [exact R966|]. exact F12.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma b2a_pre_at : forall Mx (FP : FPState) R sig,
    frame_mod mem Mx BIG -> EFACTS Mx ->
    tag_ok SEGS Mx data len (bv_unsigned sp - 320 + 144) ->
    cell32 SEGS Mx (bv_unsigned sp - 320 + 144) sig ->
    (exists ty, cell32 SEGS Mx (bv_unsigned sp - 320 + 144 + 4) ty) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 320) ->
    getr R 10 = Z_to_bv 64 (bv_unsigned sp - 320 + 144) ->
    getr R 11 = Z_to_bv 64 (bv_unsigned P + 560) ->
    getr R 12 = Z_to_bv 64 (pcs_of raw) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned data + len) ->
    b2a_pre SEGS W2 data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) (Z_to_bv 64 (bv_unsigned sp - 320 + 144))
            (Z_to_bv 64 (bv_unsigned P + 560)) (pcs_of raw) FP R Mx.
  Proof using HE rom.
    intros Mx FP R sig Hf HF Htag Hsig Hty R2 R10 R11 R12 R13.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4). pose proof D as (D1 & _).
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    unfold b2a_pre. cbv zeta. rewrite !u_small_frame by lia. cbn [w_ab_d w_ro_lo w_ro_hi wp2_src1].
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [apply pcs_of_01|].
    split; [apply (penv_data regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [exact Hty|]. split; [exact Htag|].
    split; [clear - Sal; lia|]. split; [lia|].
    split; [eapply writable_sub; [apply (penv_wP regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [clear - Pal; lia|]. split; [lia|]. split; [lia|].
    split; [apply zero_b2a_curves; [exact F8 | lia | lia]|].
    split; [clear - Sal; lia|].
    split; [eapply writable_sub; [apply (penv_wS regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [apply (penv_ro regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma after_b2a : forall Mx My,
    EFACTS Mx -> SAVED Mx -> frame_mod mem Mx BIG ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320)) - 336), 336%Z);
                     (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 560))), 400%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\ cell8 SEGS My (bv_unsigned P + 965) h965 /\
    (Forall (fun off => curve_ok SEGS My data len (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 560)) + off)) b2a_curve_offsets ->
     parsed_ok SEGS My data len bs (bv_unsigned P)).
  Proof using HE Htags R964 R966 rom.
    intros Mx My HF HS Hf Hfr.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4).
    rewrite !u_small_frame in Hfr by lia. rewrite !u_small_frame by lia.
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10 & F11 & F12).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    split; [eapply cell8_frame; [exact Hfr | exact F10 | lia | lia | solve_apart]|].
    intros Hc. exists psz, tc, h964, h966.
    split; [eapply cell64_frame; [exact Hfr | exact F3 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F4 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F5 | lia | lia | solve_apart]|].
    split; [exact Htags|].
    split.
    { apply curves_ok_assemble.
      - eapply trc_curves_frame; [exact Hfr | exact F6 | lia | lia | solve_apart].
      - eapply a2b_curves_frame; [exact Hfr | exact F7 | lia | lia | solve_apart].
      - exact Hc. }
    split; [eapply cell8_frame; [exact Hfr | exact F9 | lia | lia | solve_apart]|].
    split; [exact R964|].
    split; [eapply cell8_frame; [exact Hfr | exact F11 | lia | lia | solve_apart]|].
    split; [exact R966|].
    intros Hnz. eapply grid_ok_A2B_frame288; [exact Hfr | exact (F12 Hnz) | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Found.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (sig : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 (bv_unsigned data + len).
    Hypothesis HF : EFACTS M.
    Hypothesis Htag : tag_ok SEGS M data len (bv_unsigned sp - 320 + 144).
    Hypothesis Hsig : cell32 SEGS M (bv_unsigned sp - 320 + 144) sig.
    Hypothesis Hty : exists ty, cell32 SEGS M (bv_unsigned sp - 320 + 144 + 4) ty.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [raw])) (blobs_ev [bs]).

    Definition kn_found : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KWord (SA (EVar 2) 8) 8 (EVar 64)].

    Lemma kn_found_ok : know_ok SEGS E M kn_found.
    Proof using HC HE HF Hf.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      destruct HF as (F1 & F2 & _).
      unfold kn_found, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 8 8 (EVar 64) raw); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 8)%Z with (bv_unsigned sp - 312)%Z by lia. exact F2.
    Qed.

    Lemma foundE_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1419c) M rom) Q.
    Proof using E H19 HC HE HF HS Hb2a Hf Hgettag Hsig Htag Htags Hty R964 R965 R966.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF' : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_found_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 20%nat [0x151f8%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hb2a data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) (Z_to_bv 64 (bv_unsigned sp - 320 + 144))
                    (Z_to_bv 64 (bv_unsigned P + 560)) (pcs_of raw) I R1 Mx ro (Z_to_bv 64 0x141c0));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (b2a_pre_at Mx I R1 sig Hf HF Htag Hsig Hty);
            [ regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity
            | regv_lin HR (10%bv:reg); f_equal; lia
            | regv_lin HR (11%bv:reg); rewrite H8; f_equal; lia
            | regv HR (12%bv:reg); rewrite alu_sltu, alu_xor; apply sltiu_xor_pcs
            | regv HR (13%bv:reg); exact H19 ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Hcurves).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) (-336), 336%Z); (SA (EVar 8) 560, 400%Z)];
        [unfold v_addi; rewrite H2, H8, !u_small_frame by lia; repeat f_equal; lia|].
      destruct (after_b2a M mq1 HF HS Hf Hfr) as (HS1 & Hf1 & C965a & Hpo1).
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 75) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false.
        fail_with HR HF' H2 H3 H4 H8 HFK HS1 Hf1. }
      add_krange (EVar 75) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      run_fp 10%nat [0x141cc%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 967, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockF_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag I R2 M2 h965) end.
      - common HR HF' H2 H3 H4 H8 HFK.
      - eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS1 | exact Hfr2 | solve_apart | lia].
      - eapply frame_mod_trans_same; [exact Hf1|]. eapply frame_mod_of_covered; [| exact Hfr2]. unfold LibParseDefsS1.BIG. solve_covered.
      - eapply parsed_ok_frame; [exact Hfr2 | exact (Hpo1 (Hcurves eq_refl)) | lia | lia | solve_apart | solve_apart | solve_apart].
      - eapply cell8_frame; [exact Hfr2 | exact C965a | lia | lia | solve_apart].
      - exact R965.
    Qed.
  End Found.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 (bv_unsigned data + len).
    Hypothesis HF : EFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_E : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KRange (EVar 9) 1 (2^64 - 8);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 9) 0) 8;
       KWord (SA (EVar 2) 16) 8 (ELit 2);
       KWord (SA (EVar 9) 0) 4 (ELit 0);
       KWord (SA (EVar 9) 4) 4 (ELit 1)].

    Lemma kn_E_ok : know_ok SEGS E M kn_E.
    Proof using H9 HC HE HF Hf rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      pose proof (penv_prio regs mem rom ret sp data prio P len bs HE M Hf) as [[_ C0] [_ C4]].
      destruct HF as (F1 & F2 & _).
      unfold kn_E, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply krange_intro; cbn. rewrite H9. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H9. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 16)%Z with (bv_unsigned sp - 304)%Z by lia. exact F1.
      - eapply (kword_intro SEGS E M (EVar 9) prio 0 4 (ELit 0) (Z_to_bv 64 0)); cbn; try lia; auto.
        rewrite Z.add_0_r. exact C0.
      - eapply (kword_intro SEGS E M (EVar 9) prio 4 4 (ELit 1) (Z_to_bv 64 1)); cbn; try lia; auto.
    Qed.

    (* [comment removed for export] *)
    Ltac call_gettag sig retw Mx0 Hfx C0 C20 H8 H2 :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 320 + 144)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 144 _ psz tc Hfx C0 C20 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.

    Lemma blockE_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14158) M rom) Q.
    Proof using H19 H9 HC HE HF HS Hb2a Hf Hgettag Htags R964 R965 R966.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      pose proof HF as HF'. destruct HF' as (F1 & F2 & F3 & F4 & F5 & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_E_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 30%nat [0x137b4%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x42324130%Z (Z_to_bv 64 0x14188) M Hf F3 F5 H8 H2.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS Hfr) as HS1.
      pose proof (EFACTS_tag _ _ 144 ltac:(lia) HF Hfr) as HF1.
      clear Hfr.
      destruct Hr01 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1419c%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundE_run I R2 mq1 0x42324130%Z) end;
          [ common HR HFr H2 H3 H4 H8 HFK | exact HS1 | exact Hf1 | regv HR (19%bv:reg); exact H19
          | exact HF1 | exact Htg | exact Csig | exact Cty ]. }
      add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      pose proof HF1 as HF1'. destruct HF1' as (G1 & G2 & G3 & G4 & G5 & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x42324131%Z (Z_to_bv 64 0x14188) mq1 Hf1 G3 G5 H8 H2.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf1 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf2.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS1 Hfr) as HS2.
      pose proof (EFACTS_tag _ _ 144 ltac:(lia) HF1 Hfr) as HF2.
      clear Hfr.
      destruct Hr02 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag2 eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1419c%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundE_run I R2 mq2 0x42324131%Z) end;
          [ common HR HFr H2 H3 H4 H8 HFK | exact HS2 | exact Hf2 | regv HR (19%bv:reg); exact H19
          | exact HF2 | exact Htg | exact Csig | exact Cty ]. }
      (* [comment removed for export] *)
      add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      run_fp 10%nat [0x141cc%Z] noscr false.
      pose proof HF2 as HF2'. destruct HF2' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & K10 & _).
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
        apply (blockF_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag I R2 mq2 h965) end;
        [ common HR HFr H2 H3 H4 H8 HFK | exact HS2 | exact Hf2 | apply EFACTS_parsed; exact HF2 | exact K10 | exact R965 ].
    Qed.
  End Run.
End E.
End LibParseES1.

Module LibParseDS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac perf_el3_core := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs;
  first [ Zify.zify_post_hook; xlia zchecker | lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with true => idtac end; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ].
Local Ltac perf_el3_clear_all := clear.  (* [comment removed for export] *)
Local Ltac perf_el3_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif perf_el3_has_var then perf_el3_core
  else first [ solve [perf_el3_clear_all; perf_el3_core] | perf_el3_core ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W2 := wp2_src1.

Section D.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc h964 h965 : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.
  Hypothesis R964 : (h964 = 0 \/ h964 = 1)%Z.
  Hypothesis R965 : (h965 = 0 \/ h965 = 1)%Z.

  #[local] Notation EFACTS := (EFACTS sp data P len psz tc h964 h965).

  (* [comment removed for export] *)
  Definition DFACTS (Mx : word -> option byte) : Prop :=
    let p := bv_unsigned P in let s := bv_unsigned sp in
    cell64 SEGS Mx (s - 304) (Z_to_bv 64 2) /\ cell64 SEGS Mx (s - 312) raw /\
    cell64 SEGS Mx p data /\ cell32 SEGS Mx (p + 8) psz /\ cell32 SEGS Mx (p + 20) tc /\
    Forall (fun off => curve_ok SEGS Mx data len (p + off)) [24; 56; 88]%Z /\
    zero Mx (p + 160) 800 /\
    cell8 SEGS Mx (p + 964) h964 /\ cell8 SEGS Mx (p + 965) h965 /\ cell8 SEGS Mx (p + 966) 0.

  Lemma DFACTS_frame : forall Mx My rs,
    DFACTS Mx -> frame_mod Mx My rs ->
    apart (bv_unsigned sp - 312) 16 rs -> apart (bv_unsigned P) 120 rs ->
    apart (bv_unsigned P + 160) 800 rs -> apart (bv_unsigned P + 964) 3 rs -> DFACTS My.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My rs (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf As Ap Az Afl.
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _).
    unfold DFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | exact Az]|].
    split; [eapply cell8_frame; [exact Hf | exact F8 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]]|].
    split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]]|].
    eapply cell8_frame; [exact Hf | exact F10 | lia | lia | eapply apart_sub; [exact Afl | lia | lia | lia]].
  Qed.

  Lemma DFACTS_tag : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    DFACTS Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] -> DFACTS My.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My k Hk HF Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    eapply DFACTS_frame; [exact HF | exact Hfr | solve_apart | solve_apart | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma DFACTS_E : forall Mx, DFACTS Mx -> EFACTS 0 raw Mx.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _).
    unfold LibParseES1.EFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split; [exact F6|].
    split; [apply zero_a2b_curves; [eapply zero_sub; [exact F7 | lia | lia] | lia | lia]|].
    split; [eapply zero_sub; [exact F7 | lia | lia]|].
    split; [exact F8|]. split; [exact F9|]. split; [exact F10|]. intros Hc; exfalso; lia.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma a2b_pre_at : forall Mx (FP : FPState) R sig,
    frame_mod mem Mx BIG -> DFACTS Mx ->
    tag_ok SEGS Mx data len (bv_unsigned sp - 320 + 144) ->
    cell32 SEGS Mx (bv_unsigned sp - 320 + 144) sig ->
    (exists ty, cell32 SEGS Mx (bv_unsigned sp - 320 + 144 + 4) ty) ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 320) ->
    getr R 10 = Z_to_bv 64 (bv_unsigned sp - 320 + 144) ->
    getr R 11 = Z_to_bv 64 (bv_unsigned P + 160) ->
    getr R 12 = Z_to_bv 64 (pcs_of raw) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned data + len) ->
    a2b_pre SEGS W2 data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) (Z_to_bv 64 (bv_unsigned sp - 320 + 144))
            (Z_to_bv 64 (bv_unsigned P + 160)) (pcs_of raw) FP R Mx.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx FP R sig Hf HF Htag Hsig Hty R2 R10 R11 R12 R13.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4). pose proof D as (D1 & _).
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    unfold a2b_pre. cbv zeta. rewrite !u_small_frame by lia. cbn [w_ab_d w_ro_lo w_ro_hi wp2_src1].
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [apply pcs_of_01|].
    split; [apply (penv_data regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [exact Hty|]. split; [exact Htag|].
    split; [clear - Sal; lia|]. split; [lia|].
    split; [eapply writable_sub; [apply (penv_wP regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [clear - Pal; lia|]. split; [lia|]. split; [lia|].
    split; [apply zero_a2b_curves; [eapply zero_sub; [exact F7 | lia | lia] | lia | lia]|].
    split.
    { exists (Z_to_bv 64 0), (Z_to_bv 64 0). split.
      - replace (bv_unsigned P + 160 + 128)%Z with (bv_unsigned P + 160 + 128)%Z by lia.
        eapply (zero_cell64 SEGS Mx (bv_unsigned P + 160) 800 128); [exact F7 | lia | lia | lia | lia].
      - eapply (zero_cell64 SEGS Mx (bv_unsigned P + 160) 800 136); [exact F7 | lia | lia | lia | lia]. }
    split; [clear - Sal; lia|].
    split; [eapply writable_sub; [apply (penv_wS regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [apply (penv_ro regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [lia|]. split; [lia|]. split; [lia|]. split; [lia|]. split; lia.
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  (* [comment removed for export] *)
  Lemma after_a2b : forall Mx My,
    DFACTS Mx -> SAVED Mx -> frame_mod mem Mx BIG ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320)) - 336), 336%Z);
                     (Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160))), 400%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\
    (Forall (fun off => curve_ok SEGS My data len (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160)) + off)) a2b_curve_offsets ->
     a2b_grid_ok SEGS My data len (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 160))) ->
     forall Mz, frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell8 SEGS Mz (bv_unsigned P + 966) 1 ->
     EFACTS 1 raw Mz).
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My HF HS Hf Hfr.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4).
    rewrite !u_small_frame in Hfr by lia. rewrite !u_small_frame by lia.
    destruct HF as (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    intros Hc Hg Mz Hfz C966. unfold LibParseES1.EFACTS. cbv zeta.
    assert (T64 : forall a x, cell64 SEGS Mx a x -> (0 <= a)%Z -> (a + 8 <= 2 ^ 64)%Z ->
              apart a 8 [(Z_to_bv 64 (bv_unsigned sp - 320 - 336), 336%Z); (Z_to_bv 64 (bv_unsigned P + 160), 400%Z)] ->
              apart a 8 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell64 SEGS Mz a x).
    { intros a x C Ha Ha8 Ap1 Ap2. eapply cell64_frame; [exact Hfz | | lia | lia | exact Ap2].
      eapply cell64_frame; [exact Hfr | exact C | lia | lia | exact Ap1]. }
    assert (T32 : forall a x, cell32 SEGS Mx a x -> (0 <= a)%Z -> (a + 4 <= 2 ^ 64)%Z ->
              apart a 4 [(Z_to_bv 64 (bv_unsigned sp - 320 - 336), 336%Z); (Z_to_bv 64 (bv_unsigned P + 160), 400%Z)] ->
              apart a 4 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell32 SEGS Mz a x).
    { intros a x C Ha Ha4 Ap1 Ap2. eapply cell32_frame; [exact Hfz | | lia | lia | exact Ap2].
      eapply cell32_frame; [exact Hfr | exact C | lia | lia | exact Ap1]. }
    assert (T8 : forall a x, cell8 SEGS Mx a x -> (0 <= a)%Z -> (a + 1 <= 2 ^ 64)%Z ->
              apart a 1 [(Z_to_bv 64 (bv_unsigned sp - 320 - 336), 336%Z); (Z_to_bv 64 (bv_unsigned P + 160), 400%Z)] ->
              apart a 1 [(Z_to_bv 64 (bv_unsigned P + 966), 1%Z)] -> cell8 SEGS Mz a x).
    { intros a x C Ha Ha1 Ap1 Ap2. eapply cell8_frame; [exact Hfz | | lia | lia | exact Ap2].
      eapply cell8_frame; [exact Hfr | exact C | lia | lia | exact Ap1]. }
    split; [apply T64; [exact F1 | lia | lia | solve_apart | solve_apart]|].
    split; [apply T64; [exact F2 | lia | lia | solve_apart | solve_apart]|].
    split; [apply T64; [exact F3 | lia | lia | solve_apart | solve_apart]|].
    split; [apply T32; [exact F4 | lia | lia | solve_apart | solve_apart]|].
    split; [apply T32; [exact F5 | lia | lia | solve_apart | solve_apart]|].
    split.
    { eapply trc_curves_frame; [exact Hfz | | lia | lia | solve_apart].
      eapply trc_curves_frame; [exact Hfr | exact F6 | lia | lia | solve_apart]. }
    split; [eapply a2b_curves_frame; [exact Hfz | exact Hc | lia | lia | solve_apart]|].
    split.
    { eapply zero_frame; [exact Hfz | | lia | lia | solve_apart].
      eapply zero_frame; [exact Hfr | eapply zero_sub; [exact F7 | lia | lia] | lia | lia | solve_apart]. }
    split; [apply T8; [exact F8 | lia | lia | solve_apart | solve_apart]|].
    split; [apply T8; [exact F9 | lia | lia | solve_apart | solve_apart]|].
    split; [exact C966|].
    intros _. eapply grid_ok_A2B_frame288; [exact Hfz | exact Hg | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Found.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (sig : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 (bv_unsigned data + len).
    Hypothesis HF : DFACTS M.
    Hypothesis Htag : tag_ok SEGS M data len (bv_unsigned sp - 320 + 144).
    Hypothesis Hsig : cell32 SEGS M (bv_unsigned sp - 320 + 144) sig.
    Hypothesis Hty : exists ty, cell32 SEGS M (bv_unsigned sp - 320 + 144 + 4) ty.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [raw])) (blobs_ev [bs]).

    Definition kn_found : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KWord (SA (EVar 2) 8) 8 (EVar 64)].

    Lemma kn_found_ok : know_ok SEGS E M kn_found.
    Proof using HC HE HF Hf.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      destruct HF as (F1 & F2 & _).
      unfold kn_found, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 8 8 (EVar 64) raw); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 8)%Z with (bv_unsigned sp - 312)%Z by lia. exact F2.
    Qed.

    Lemma foundD_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x14128) M rom) Q.
    Proof using E H19 H9 HC HE HF HS Ha2b Hb2a Hf Hgettag Hsig Htag Htags Hty R964 R965.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HF' : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_found_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 20%nat [0x148ec%Z] noscr false.
      (* [comment removed for export] *)
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Ha2b data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) (Z_to_bv 64 (bv_unsigned sp - 320 + 144))
                    (Z_to_bv 64 (bv_unsigned P + 160)) (pcs_of raw) I R1 Mx ro (Z_to_bv 64 0x1414c));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (a2b_pre_at Mx I R1 sig Hf HF Htag Hsig Hty);
            [ regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity
            | regv_lin HR (10%bv:reg); f_equal; lia
            | regv_lin HR (11%bv:reg); rewrite H8; f_equal; lia
            | regv HR (12%bv:reg); rewrite alu_sltu, alu_xor; apply sltiu_xor_pcs
            | regv HR (13%bv:reg); exact H19 ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Hpost).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) (-336), 336%Z); (SA (EVar 8) 160, 400%Z)];
        [unfold v_addi; rewrite H2, H8, !u_small_frame by lia; repeat f_equal; lia|].
      destruct (after_a2b M mq1 HF HS Hf Hfr) as (HS1 & Hf1 & HE1).
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 75) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false.
        fail_with HR HF' H2 H3 H4 H8 HFK HS1 Hf1. }
      destruct (Hpost eq_refl) as [Hcurves Hgrid].
      add_krange (EVar 75) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      run_fp 10%nat [0x14158%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 966, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      kread_fact HK (EVar 8) 966%Z 1%nat C966.
      rewrite H8 in C966. unfold v_addi in C966.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockE_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hb2a psz tc h964 h965 1 raw
                 Htags R964 R965 ltac:(lia) I R2 M2) end.
      - common HR HF' H2 H3 H4 H8 HFK.
      - eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS1 | exact Hfr2 | solve_apart | lia].
      - eapply frame_mod_trans_same; [exact Hf1|]. eapply frame_mod_of_covered; [| exact Hfr2]. unfold LibParseDefsS1.BIG. solve_covered.
      - regv HR (9%bv:reg). exact H9.
      - regv HR (19%bv:reg). exact H19.
      - apply (HE1 Hcurves Hgrid _ Hfr2). split; [lia|]. exact C966.
    Qed.
  End Found.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H23 : getr R 23 = Z_to_bv 64 2.
    Hypothesis HF : DFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_D : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KRange (EVar 9) 1 (2^64 - 8);
       KRange (EVar 19) 0 (2^26);
       KRange (EVar 20) 1 (2^47);
       KRange (EVar 23) 2 2;
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 9) 0) 8;
       KWord (SA (EVar 9) 0) 4 (ELit 0);
       KWord (SA (EVar 9) 4) 4 (ELit 1)].

    Lemma kn_D_ok : know_ok SEGS E M kn_D.
    Proof using H19 H20 H23 H9 HC HE Hf rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range prio). pose proof (u64_range data).
      pose proof D as (D1 & D2 & D3 & D4 & _).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      pose proof (penv_prio regs mem rom ret sp data prio P len bs HE M Hf) as [[_ C0] [_ C4]].
      unfold kn_D, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply krange_intro; cbn. rewrite H9. lia.
      - apply krange_intro; cbn. rewrite H19, u_small by lia. lia.
      - apply krange_intro; cbn. rewrite H20. lia.
      - apply krange_intro; cbn. rewrite H23, u_small by lia. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H9. lia.
      - eapply (kword_intro SEGS E M (EVar 9) prio 0 4 (ELit 0) (Z_to_bv 64 0)); cbn; try lia; auto.
        rewrite Z.add_0_r. exact C0.
      - eapply (kword_intro SEGS E M (EVar 9) prio 4 4 (ELit 1) (Z_to_bv 64 1)); cbn; try lia; auto.
    Qed.

    Ltac call_gettag sig retw Mx0 Hfx C0 C20 H8 H2 :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 320 + 144)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 144 _ psz tc Hfx C0 C20 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.

    Lemma blockD_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x140e4) M rom) Q.
    Proof using H19 H20 H23 H9 HC HE HF HS Ha2b Hb2a Hf Hgettag Htags R964 R965.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      pose proof HF as HF'. destruct HF' as (F1 & F2 & F3 & F4 & F5 & _).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_D_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 30%nat [0x137b4%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x41324230%Z (Z_to_bv 64 0x14114) M Hf F3 F5 H8 H2.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS Hfr) as HS1.
      pose proof (DFACTS_tag _ _ 144 ltac:(lia) HF Hfr) as HF1.
      clear Hfr.
      destruct Hr01 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x14128%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundD_run I R2 mq1 0x41324230%Z) end;
          [ common HR HFr H2 H3 H4 H8 HFK | exact HS1 | exact Hf1
          | regv HR (9%bv:reg); exact H9
          | regv_lin HR (19%bv:reg); rewrite H19, H20, u_small by lia; f_equal; lia
          | exact HF1 | exact Htg | exact Csig | exact Cty ]. }
      add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      pose proof HF1 as HF1'. destruct HF1' as (G1 & G2 & G3 & G4 & G5 & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      (* [comment removed for export] *)
      call_gettag 0x41324231%Z (Z_to_bv 64 0x14114) mq1 Hf1 G3 G5 H8 H2.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf1 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf2.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS1 Hfr) as HS2.
      pose proof (DFACTS_tag _ _ 144 ltac:(lia) HF1 Hfr) as HF2.
      clear Hfr.
      destruct Hr02 as [-> | ->].
      2:{ (* [comment removed for export] *)
        destruct (Htag2 eq_refl) as (Htg & Csig & Cty). rewrite !u_small_frame in Htg, Csig, Cty by lia.
        add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x14128%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (foundD_run I R2 mq2 0x41324231%Z) end;
          [ common HR HFr H2 H3 H4 H8 HFK | exact HS2 | exact Hf2
          | regv HR (9%bv:reg); exact H9
          | regv_lin HR (19%bv:reg); rewrite H19, H20, u_small by lia; f_equal; lia
          | exact HF2 | exact Htg | exact Csig | exact Cty ]. }
      (* [comment removed for export] *)
      add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      run_fp 10%nat [0x14158%Z] noscr false.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
        apply (blockE_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hb2a psz tc h964 h965 0 raw
                 Htags R964 R965 ltac:(lia) I R2 mq2) end;
        [ common HR HFr H2 H3 H4 H8 HFK | exact HS2 | exact Hf2
        | regv HR (9%bv:reg); exact H9
        | regv_lin HR (19%bv:reg); rewrite H19, H20, u_small by lia; f_equal; lia
        | apply DFACTS_E; exact HF2 ].
    Qed.
  End Run.
End D.

(* [comment removed for export] *)
Lemma DFACTS_set965 : forall regs (mem rom : word -> option byte) ret sp data prio P len bs,
  PENV regs mem ret sp data prio P len bs ->
  forall psz tc h964 h965 raw v Mx My,
  DFACTS sp data P len psz tc h964 h965 raw Mx ->
  frame_mod Mx My [(Z_to_bv 64 (bv_unsigned P + 965), 1%Z)] ->
  cell8 Plain.M.loaded_segments My (bv_unsigned P + 965) v ->
  DFACTS sp data P len psz tc h964 v raw My.
Proof.
  intros regs mem rom ret sp data prio P len bs HE psz tc h964 h965 raw v Mx My
         (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf C.
  pose proof (u64_range sp). pose proof (u64_range P).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
  unfold DFACTS. cbv zeta.
  split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | solve_apart]|].
  split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | solve_apart]|].
  split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | solve_apart]|].
  split; [eapply cell8_frame; [exact Hf | exact F8 | lia | lia | solve_apart]|].
  split; [exact C|].
  eapply cell8_frame; [exact Hf | exact F10 | lia | lia | solve_apart].
Qed.

(* [comment removed for export] *)
Lemma DFACTS_set964 : forall regs (mem rom : word -> option byte) ret sp data prio P len bs,
  PENV regs mem ret sp data prio P len bs ->
  forall psz tc h964 h965 raw v Mx My,
  DFACTS sp data P len psz tc h964 h965 raw Mx ->
  frame_mod Mx My [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
  cell8 Plain.M.loaded_segments My (bv_unsigned P + 964) v ->
  DFACTS sp data P len psz tc v h965 raw My.
Proof.
  intros regs mem rom ret sp data prio P len bs HE psz tc h964 h965 raw v Mx My
         (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hf C.
  pose proof (u64_range sp). pose proof (u64_range P).
  destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
  unfold DFACTS. cbv zeta.
  split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | solve_apart]|].
  split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | solve_apart]|].
  split; [eapply cell32_frame; [exact Hf | exact F5 | lia | lia | solve_apart]|].
  split; [eapply trc_curves_frame; [exact Hf | exact F6 | lia | lia | solve_apart]|].
  split; [eapply zero_frame; [exact Hf | exact F7 | lia | lia | solve_apart]|].
  split; [exact C|].
  split; [eapply cell8_frame; [exact Hf | exact F9 | lia | lia | solve_apart]|].
  eapply cell8_frame; [exact Hf | exact F10 | lia | lia | solve_apart].
Qed.
End LibParseDS1.

Module LibParseC3S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W2 := wp2_src1.

Section C3.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc h964 : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.
  Hypothesis R964 : (h964 = 0 \/ h964 = 1)%Z.

  #[local] Notation DFACTS := (DFACTS sp data P len psz tc h964).

  (* [comment removed for export] *)
  Definition XT (Mx : word -> option byte) (k sig : Z) : Prop :=
    tag_ok SEGS Mx data len (bv_unsigned sp - 320 + k) /\
    cell32 SEGS Mx (bv_unsigned sp - 320 + k) sig /\
    (exists ty, cell32 SEGS Mx (bv_unsigned sp - 320 + k + 4) ty).

  Lemma XT_frame : forall Mx My rs k sig,
    XT Mx k sig -> frame_mod Mx My rs -> (0 <= k <= 168)%Z -> apart (bv_unsigned sp - 320 + k) 24 rs -> XT My k sig.
  Proof using HE raw rom.
    intros Mx My rs k sig (X1 & X2 & [ty X3]) Hf Hk Hap. pose proof (u64_range sp).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
    split; [eapply tag_ok_frame; [exact Hf | exact X1 | lia | lia | exact Hap]|].
    split; [eapply cell32_frame; [exact Hf | exact X2 | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]]|].
    exists ty. eapply cell32_frame; [exact Hf | exact X3 | lia | lia | eapply apart_sub; [exact Hap | lia | lia | lia]].
  Qed.

  Lemma XT_intro : forall Mx k sig,
    (0 <= k <= 168)%Z ->
    tag_ok SEGS Mx data len (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320 + k))) /\
    cell32 SEGS Mx (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320 + k))) sig /\
    (exists ty, cell32 SEGS Mx (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320 + k)) + 4) ty) -> XT Mx k sig.
  Proof using HE raw rom.
    intros Mx k sig Hk H. pose proof (u64_range sp).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
    rewrite !u_small_frame in H by lia. exact H.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Lemma xyz_pre_at : forall Mx (FP : FPState) R s1 s2 s3,
    frame_mod mem Mx BIG ->
    XT Mx 72 s1 -> XT Mx 48 s2 -> XT Mx 24 s3 ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 320) ->
    getr R 10 = Z_to_bv 64 (bv_unsigned sp - 320 + 72) ->
    getr R 11 = Z_to_bv 64 (bv_unsigned sp - 320 + 48) ->
    getr R 12 = Z_to_bv 64 (bv_unsigned sp - 320 + 24) ->
    getr R 13 = Z_to_bv 64 (bv_unsigned P + 120) ->
    xyzd50_pre SEGS W data len bs (Z_to_bv 64 (bv_unsigned sp - 320))
      (Z_to_bv 64 (bv_unsigned sp - 320 + 72)) (Z_to_bv 64 (bv_unsigned sp - 320 + 48))
      (Z_to_bv 64 (bv_unsigned sp - 320 + 24)) (Z_to_bv 64 (bv_unsigned P + 120)) FP R Mx.
  Proof using HE raw rom.
    intros Mx FP R s1 s2 s3 Hf X1 X2 X3 R2 R10 R11 R12 R13.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4). pose proof D as (D1 & _).
    assert (XK : forall k s, XT Mx k s -> (k = 72 \/ k = 48 \/ k = 24)%Z ->
              xtag_ok SEGS W Mx data len (Z_to_bv 64 (bv_unsigned sp - 320)) (bv_unsigned (Z_to_bv 64 (bv_unsigned P + 120)))
                      (Z_to_bv 64 (bv_unsigned sp - 320 + k))).
    { intros k s (T1 & T2 & T3) Hk. unfold xtag_ok. cbv zeta. cbn [t_xyzd50_d tags_src1].
      rewrite !u_small_frame by lia.
      split; [exact T3|]. split; [exact T1|]. split; [clear - Sal Hk; lia|]. split; [lia|]. split; lia. }
    unfold xyzd50_pre. cbv zeta. cbn [t_xyzd50_d tags_src1].
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [apply (penv_data regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [apply (XK 72%Z s1 X1); lia|]. split; [apply (XK 48%Z s2 X2); lia|]. split; [apply (XK 24%Z s3 X3); lia|].
    rewrite !u_small_frame by lia.
    split; [eapply writable_sub; [apply (penv_wP regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [clear - Pal; lia|]. split; [lia|]. split; [clear - Sal; lia|].
    split; [eapply writable_sub; [apply (penv_wS regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [lia|]. split; lia.
  Qed.

  Lemma after_xyz : forall Mx My,
    DFACTS 0 raw Mx -> SAVED Mx -> frame_mod mem Mx BIG ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320)) - 32), 32%Z);
                     (Z_to_bv 64 (bv_unsigned P + 120), 36%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\ DFACTS 0 raw My.
  Proof using HE rom.
    intros Mx My HF HS Hf Hfr.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4).
    rewrite !u_small_frame in Hfr by lia.
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    eapply (DFACTS_frame regs mem rom ret sp data prio P len bs HE); [exact HF | exact Hfr | solve_apart | solve_apart | solve_apart | solve_apart].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H23 : getr R 23 = Z_to_bv 64 2.
    Hypothesis HF : DFACTS 0 raw M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_C3 : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976].

    Lemma kn_C3_ok : know_ok SEGS E M kn_C3.
    Proof using HC HE Hf raw rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      unfold kn_C3, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
    Qed.

    Ltac call_gettag sig k retw Hfx C0 C20 H8 H2 :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 320 + k)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 k _ psz tc Hfx C0 C20 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.

    (* [comment removed for export] *)
    Ltac to_D HR HFr H2 H3 H4 H8 HFK HSx Hfx HFx :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Ha2b Hb2a psz tc h964 0 raw
                 Htags R964 ltac:(lia) I R2 M2);
        [ common HR HFr H2 H3 H4 H8 HFK | exact HSx | exact Hfx
        | regv HR (9%bv:reg); exact H9
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | regv HR (23%bv:reg); exact H23
        | exact HFx ]
      end.

    Lemma blockC3_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1407c) M rom) Q.
    Proof using H19 H20 H23 H9 HC HE HF HS Ha2b Hb2a Hf Hgettag Htags Hxyz R964.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_C3_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as (_ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x7258595a%Z 72%Z (Z_to_bv 64 0x14090) Hf F3 F5 H8 H2.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 72, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 72 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 72 ltac:(lia) HS Hfr) as HS1.
      pose proof (DFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ _ _ 72%Z ltac:(lia) HF Hfr) as HF1.
      clear Hfr F3 F5.
      destruct Hr01 as [-> | ->].
      { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x140e4%Z] noscr false. to_D HR HFr H2 H3 H4 H8 HFK HS1 Hf1 HF1. }
      pose proof (XT_intro mq1 72%Z _ ltac:(lia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as (_ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x6758595a%Z 48%Z (Z_to_bv 64 0x140a8) Hf1 F3 F5 H8 H2.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 48, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf1 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 48 ltac:(lia) Hfr)) as Hf2.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 48 ltac:(lia) HS1 Hfr) as HS2.
      pose proof (DFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ _ _ 48%Z ltac:(lia) HF1 Hfr) as HF2.
      pose proof (XT_frame _ _ _ _ _ X1 Hfr ltac:(lia) ltac:(solve_apart)) as X1b.
      clear Hfr F3 F5 X1 HF1 HS1 Hf1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x140e4%Z] noscr false. to_D HR HFr H2 H3 H4 H8 HFK HS2 Hf2 HF2. }
      pose proof (XT_intro mq2 48%Z _ ltac:(lia) (Htag2 eq_refl)) as X2. clear Htag2.
      add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF2 as HF'. destruct HF' as (_ & _ & F3 & _ & F5 & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x6258595a%Z 24%Z (Z_to_bv 64 0x140c0) Hf2 F3 F5 H8 H2.
      intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03 & Htag3).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 24, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf2 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 24 ltac:(lia) Hfr)) as Hf3.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 24 ltac:(lia) HS2 Hfr) as HS3.
      pose proof (DFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ _ _ 24%Z ltac:(lia) HF2 Hfr) as HF3.
      pose proof (XT_frame _ _ _ _ _ X1b Hfr ltac:(lia) ltac:(solve_apart)) as X1c.
      pose proof (XT_frame _ _ _ _ _ X2 Hfr ltac:(lia) ltac:(solve_apart)) as X2c.
      clear Hfr F3 F5 X1b X2 HF2 HS2 Hf2.
      destruct Hr03 as [-> | ->].
      { add_krange (EVar 202) 0%Z 0%Z by (rewrite Hr3; rewrite u_small by lia; lia).
        run_fp 10%nat [0x140e4%Z] noscr false. to_D HR HFr H2 H3 H4 H8 HFK HS3 Hf3 HF3. }
      pose proof (XT_intro mq3 24%Z _ ltac:(lia) (Htag3 eq_refl)) as X3. clear Htag3.
      add_krange (EVar 202) 1%Z 1%Z by (rewrite Hr3; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x1485c%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hxyz data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) (Z_to_bv 64 (bv_unsigned sp - 320 + 72))
                    (Z_to_bv 64 (bv_unsigned sp - 320 + 48)) (Z_to_bv 64 (bv_unsigned sp - 320 + 24))
                    (Z_to_bv 64 (bv_unsigned P + 120)) I R1 Mx ro (Z_to_bv 64 0x140d8));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (xyz_pre_at Mx I R1 _ _ _ Hf3 X1c X2c X3);
            [ regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 2)), H2; reflexivity
            | regv_lin HR (10%bv:reg); f_equal; lia
            | regv_lin HR (11%bv:reg); f_equal; lia
            | regv_lin HR (12%bv:reg); f_equal; lia
            | regv_lin HR (13%bv:reg); rewrite H8; f_equal; lia ] ]
        | cbv beta ]
      end.
      intros FQ4 rq4 mq4 (Hkeep & Hfkeep & Hfr & r4 & Hr4 & Hr04).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ4. clear Hkeep Hfkeep.
      cbn [t_xyzd50_d tags_src1] in Hfr.
      know_frame HK Hfr [(SA (EVar 2) (-32), 32%Z); (SA (EVar 8) 120, 36%Z)];
        [unfold v_addi; rewrite H2, H8, !u_small_frame by lia; repeat f_equal; lia|].
      destruct (after_xyz mq3 mq4 HF3 HS3 Hf3 Hfr) as (HS4 & Hf4 & HF4). clear Hfr.
      destruct Hr04 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 266) 0%Z 0%Z by (rewrite Hr4; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false.
        fail_with HR HFr H2 H3 H4 H8 HFK HS4 Hf4. }
      add_krange (EVar 266) 1%Z 1%Z by (rewrite Hr4; rewrite u_small by lia; lia).
      run_fp 10%nat [0x140e4%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 965, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      kread_fact HK (EVar 8) 965%Z 1%nat C965.
      rewrite H8 in C965. unfold v_addi in C965.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Ha2b Hb2a psz tc h964 1 raw
                 Htags R964 ltac:(lia) I R2 M2) end.
      - common HR HFr H2 H3 H4 H8 HFK.
      - eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS4 | exact Hfr2 | solve_apart | lia].
      - eapply frame_mod_trans_same; [exact Hf4|]. eapply frame_mod_of_covered; [| exact Hfr2]. unfold LibParseDefsS1.BIG. solve_covered.
      - regv HR (9%bv:reg). exact H9.
      - regv HR (19%bv:reg). exact H19.
      - regv HR (20%bv:reg). exact H20.
      - regv HR (23%bv:reg). exact H23.
      - eapply (DFACTS_set965 regs mem rom ret sp data prio P len bs HE); [exact HF4 | exact Hfr2 | split; [lia | exact C965]].
    Qed.
  End Run.
End C3.
End LibParseC3S1.

Module LibParseC2S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
(* [comment removed for export] *)
Local Ltac perf_el3_core := intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs;
  first [ Zify.zify_post_hook; xlia zchecker | lazymatch Zify.zify_convert_to_euclidean_division_equations_flag with true => idtac end; Zify.zify_to_euclidean_division_equations; Zify.zify_post_hook; xlia zchecker ].
Local Ltac perf_el3_clear_all := clear.  (* [comment removed for export] *)
Local Ltac perf_el3_has_var := match goal with |- ?G => match G with context [?x] => is_var x end end.
Local Ltac Lia.lia ::= tryif perf_el3_has_var then perf_el3_core
  else first [ solve [perf_el3_clear_all; perf_el3_core] | perf_el3_core ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section C2.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).

  Ltac call_rcurve Hrc pre_at c sz buf Hin Rsz retw Hfx H2 H8 :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
      eapply rt_call;
      [ eapply (Hrc data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) buf (Z_to_bv 64 c) (Z_to_bv 64 0) sz I R1 Mx ro retw);
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | apply (pre_at Mx I R1 c sz buf Hfx Hin Rsz ltac:(lia));
          [ regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr _ 2)), H2; reflexivity
          | regv HR (10%bv:reg); reflexivity
          | regv HR (11%bv:reg); reflexivity
          | regv_lin HR (12%bv:reg); rewrite H8; f_equal; lia
          | regv HR (13%bv:reg); reflexivity ] ]
      | cbv beta ]
    end.
  Hypothesis Htags : tags_ok len bs tc psz.

  #[local] Notation DFACTS := (DFACTS sp data P len psz tc).
  #[local] Notation XT := (XT sp data len).

  (* [comment removed for export] *)
  Definition ZH (Mx : word -> option byte) : Prop :=
    let p := bv_unsigned P in let s := bv_unsigned sp in
    cell64 SEGS Mx (s - 304) (Z_to_bv 64 2) /\ cell64 SEGS Mx (s - 312) raw /\
    cell64 SEGS Mx p data /\ cell32 SEGS Mx (p + 8) psz /\ cell32 SEGS Mx (p + 20) tc.

  (* [comment removed for export] *)
  Definition ZFACTS (Mx : word -> option byte) : Prop := ZH Mx /\ zero Mx (bv_unsigned P + 24) 952.

  Lemma ZH_frame : forall Mx My rs,
    ZH Mx -> frame_mod Mx My rs -> apart (bv_unsigned sp - 312) 16 rs -> apart (bv_unsigned P) 24 rs -> ZH My.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My rs (F1 & F2 & F3 & F4 & F5) Hf As Ap.
    pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _).
    unfold ZH. cbv zeta.
    split; [eapply cell64_frame; [exact Hf | exact F1 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F2 | lia | lia | eapply apart_sub; [exact As | lia | lia | lia]]|].
    split; [eapply cell64_frame; [exact Hf | exact F3 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    split; [eapply cell32_frame; [exact Hf | exact F4 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]]|].
    eapply cell32_frame; [exact Hf | exact F5 | lia | lia | eapply apart_sub; [exact Ap | lia | lia | lia]].
  Qed.

  Lemma ZFACTS_tag : forall Mx My (k : Z),
    (k = 168 \/ k = 144 \/ k = 120 \/ k = 96 \/ k = 72 \/ k = 48 \/ k = 24)%Z ->
    ZFACTS Mx -> frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 + k), 24%Z)] -> ZFACTS My.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My k Hk [HZ Hz] Hfr. pose proof (u64_range sp). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    split; [eapply ZH_frame; [exact HZ | exact Hfr | solve_apart | solve_apart]|].
    eapply zero_frame; [exact Hfr | exact Hz | lia | lia | solve_apart].
  Qed.

  Lemma ZFACTS_D : forall Mx, ZFACTS Mx -> DFACTS 0 0 raw Mx.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx ((F1 & F2 & F3 & F4 & F5) & Hz). pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _).
    unfold LibParseDS1.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split.
    { eapply (zero_curve_list SEGS Mx data len (bv_unsigned P + 24) 952); [exact Hz | lia | lia |].
      repeat constructor; cbn; lia. }
    split; [eapply zero_sub; [exact Hz | lia | lia]|].
    split; [replace (bv_unsigned P + 964)%Z with (bv_unsigned P + 24 + 940)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia]|].
    split; [replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 24 + 941)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia]|].
    replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 24 + 942)%Z by lia; eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma trc_D : forall My Mz,
    ZH My -> zero My (bv_unsigned P + 120) 856 ->
    curve_ok SEGS My data len (bv_unsigned P + 24) ->
    curve_ok SEGS My data len (bv_unsigned P + 56) ->
    curve_ok SEGS My data len (bv_unsigned P + 88) ->
    frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell8 SEGS Mz (bv_unsigned P + 964) 1 ->
    DFACTS 1 0 raw Mz.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros My Mz HZ Hz C1 C2 C3 Hf C964. pose proof (u64_range P). pose proof (u64_range sp).
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    pose proof (ZH_frame My Mz _ HZ Hf ltac:(solve_apart) ltac:(solve_apart)) as (F1 & F2 & F3 & F4 & F5).
    unfold LibParseDS1.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split.
    { repeat constructor.
      - eapply curve_ok_frame; [exact Hf | exact C1 | lia | lia | solve_apart].
      - eapply curve_ok_frame; [exact Hf | exact C2 | lia | lia | solve_apart].
      - eapply curve_ok_frame; [exact Hf | exact C3 | lia | lia | solve_apart]. }
    split; [eapply zero_frame; [exact Hf | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]|].
    split; [exact C964|].
    split.
    - eapply cell8_frame; [exact Hf | | lia | lia | solve_apart].
      replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 120 + 845)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
    - eapply cell8_frame; [exact Hf | | lia | lia | solve_apart].
      replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 120 + 846)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
  Lemma rcurve_pre_at : forall Mx (FP : FPState) R (c sz : Z) (buf : word),
    frame_mod mem Mx BIG -> inDATA data len (bv_unsigned buf) sz -> (0 <= sz < 2 ^ 32)%Z ->
    (c = bv_unsigned P + 24 \/ c = bv_unsigned P + 56 \/ c = bv_unsigned P + 88)%Z ->
    getr R 2 = Z_to_bv 64 (bv_unsigned sp - 320) ->
    getr R 10 = buf -> getr R 11 = Z_to_bv 64 sz -> getr R 12 = Z_to_bv 64 c -> getr R 13 = Z_to_bv 64 0 ->
    rcurve_pre SEGS W1 data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) buf (Z_to_bv 64 c) (Z_to_bv 64 0) sz FP R Mx.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx FP R c sz buf Hf Hin Hsz Hc R2 R10 R11 R12 R13.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    destruct WS as (S1 & S2 & S3 & S4). destruct WP as (WP1 & WP2 & WP3 & WP4). pose proof D as (D1 & _).
    unfold rcurve_pre. cbv zeta. cbn [w1_rcurve_d w1_ro_lo w1_ro_hi wp1_src1]. rewrite !u_small_frame by lia.
    split; [exact R2|]. split; [exact R10|]. split; [exact R11|]. split; [exact R12|]. split; [exact R13|].
    split; [apply (penv_data regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [exact Hsz|]. split; [exact Hin|].
    split; [eapply writable_sub; [apply (penv_wP regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [clear - Pal Hc; lia|].
    split; [clear - Sal; lia|].
    split; [eapply writable_sub; [apply (penv_wS regs mem ret sp data prio P len bs HE); exact Hf | lia | lia | lia]|].
    split; [apply (penv_ro regs mem rom ret sp data prio P len bs HE); exact Hf|].
    split; [lia|]. split; [lia|]. split; [lia|]. left. first [reflexivity | apply u_small; lia].
  Qed.
  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(false).

  Lemma rcurve_frame_norm : forall Mx My (C : word),
    frame_mod Mx My ((Z_to_bv 64 (bv_unsigned (Z_to_bv 64 (bv_unsigned sp - 320)) - 64), 64%Z) :: (C, 32%Z)
                      :: (if Z.eq_dec (bv_unsigned (Z_to_bv 64 0)) 0 then [] else [(Z_to_bv 64 0 : word, 4%Z)])) ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 - 64), 64%Z); (C, 32%Z)].
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My C Hf. pose proof (u64_range sp).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
    rewrite (u_small 0) in Hf by lia. rewrite u_small_frame in Hf by lia. cbn [Z.eq_dec] in Hf. exact Hf.
  Qed.

  (* [comment removed for export] *)
  Lemma after_rcurve : forall Mx My (c : Z),
    (c = bv_unsigned P + 24 \/ c = bv_unsigned P + 56 \/ c = bv_unsigned P + 88)%Z ->
    SAVED Mx -> frame_mod mem Mx BIG -> ZH Mx -> forall n, zero Mx c n -> (c + n = bv_unsigned P + 976)%Z ->
    frame_mod Mx My [(Z_to_bv 64 (bv_unsigned sp - 320 - 64), 64%Z); (Z_to_bv 64 c, 32%Z)] ->
    SAVED My /\ frame_mod mem My BIG /\ ZH My /\
    (forall c2 n2, (c + 32 <= c2)%Z -> (0 <= n2)%Z -> (c2 + n2 <= bv_unsigned P + 976)%Z -> zero My c2 n2) /\
    (forall c', curve_ok SEGS Mx data len c' -> (bv_unsigned P <= c')%Z -> (c' + 32 <= c)%Z -> curve_ok SEGS My data len c').
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros Mx My c Hc HS Hf HZ n Hz Hn Hfr.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    split; [eapply ZH_frame; [exact HZ | exact Hfr | solve_apart | solve_apart]|].
    split.
    { intros c2 n2 H1 H2 H3. eapply zero_frame; [exact Hfr | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]. }
    intros c' Hc' H1 H2. eapply curve_ok_frame; [exact Hfr | exact Hc' | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma after_trc : forall My Mz,
    SAVED My -> frame_mod mem My BIG -> ZH My -> zero My (bv_unsigned P + 120) 856 ->
    curve_ok SEGS My data len (bv_unsigned P + 24) ->
    curve_ok SEGS My data len (bv_unsigned P + 56) ->
    curve_ok SEGS My data len (bv_unsigned P + 88) ->
    frame_mod My Mz [(Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell8 SEGS Mz (bv_unsigned P + 964) 1 ->
    SAVED Mz /\ frame_mod mem Mz BIG /\ DFACTS 1 0 raw Mz.
  Proof using HE rom.
    pose proof rom as HUSEr; clear HUSEr.
    intros My Mz HS Hf HZ Hz C1 C2 C3 Hfr C964.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    eapply trc_D; eassumption.
  Qed.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section RunB.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte) (s1 s2 s3 : Z).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H23 : getr R 23 = Z_to_bv 64 2.
    Hypothesis HF : ZFACTS M.
    Hypothesis X1 : XT M 144 s1.
    Hypothesis X2 : XT M 120 s2.
    Hypothesis X3 : XT M 96 s3.

    Lemma blockC2b_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x1402c) M rom) Q.
    Proof using H19 H20 H23 H9 HC HE HF HS Ha2b Hb2a Hf Hgettag Hrc Htags Hxyz X1 X2 X3.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (_ & _ & _ & S4M).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (_ & _ & _ & W4M).
      (* [comment removed for export] *)
      destruct X1 as ((sz1 & buf1 & [Rs1 Cs1] & Cb1 & Hs1 & In1) & _ & _).
      destruct X2 as ((sz2 & buf2 & [Rs2 Cs2] & Cb2 & Hs2 & In2) & _ & _).
      destruct X3 as ((sz3 & buf3 & [Rs3 Cs3] & Cb3 & Hs3 & In3) & _ & _).
      unfold cell64, cell in Cb1, Cb2, Cb3. unfold cell in Cs1, Cs2, Cs3.
      pose proof In1 as (In1a & In1b & In1c). pose proof In2 as (In2a & In2b & In2c). pose proof In3 as (In3a & In3b & In3c).
      pose proof (u64_range buf1). pose proof (u64_range buf2). pose proof (u64_range buf3).
      set (E := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
                               ++ [Z_to_bv 64 sz1; buf1; Z_to_bv 64 sz2; buf2; Z_to_bv 64 sz3; buf3])) (blobs_ev [bs])).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS E M
        [KRange (EVar 2) 336 (2^64 - 321);
         KRange (EVar 8) 1 (2^64 - 976);
         KWr (SA (EVar 2) (-336)) 656;
         KWr (SA (EVar 8) 0) 976;
         KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
         KWord (SA (EVar 2) 152) 4 (EVar 64); KWord (SA (EVar 2) 160) 8 (EVar 65);
         KWord (SA (EVar 2) 128) 4 (EVar 66); KWord (SA (EVar 2) 136) 8 (EVar 67);
         KWord (SA (EVar 2) 104) 4 (EVar 68); KWord (SA (EVar 2) 112) 8 (EVar 69);
         KRange (EVar 64) 4 (2^26); KRange (EVar 66) 4 (2^26); KRange (EVar 68) 4 (2^26)]).
      { unfold know_ok.
        repeat (apply Forall_cons); [..|apply Forall_nil].
        - apply krange_intro; cbn. rewrite H2. lia.
        - apply krange_intro; cbn. rewrite H8. lia.
        - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
          replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4M.
        - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
          rewrite Z.add_0_r. exact W4M.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 152 4 (EVar 64) (Z_to_bv 64 sz1)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 152)%Z with (bv_unsigned sp - 320 + 144 + 8)%Z by lia. exact Cs1.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 160 8 (EVar 65) buf1); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 160)%Z with (bv_unsigned sp - 320 + 144 + 16)%Z by lia. exact Cb1.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 128 4 (EVar 66) (Z_to_bv 64 sz2)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 128)%Z with (bv_unsigned sp - 320 + 120 + 8)%Z by lia. exact Cs2.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 136 8 (EVar 67) buf2); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 136)%Z with (bv_unsigned sp - 320 + 120 + 16)%Z by lia. exact Cb2.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 104 4 (EVar 68) (Z_to_bv 64 sz3)); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 104)%Z with (bv_unsigned sp - 320 + 96 + 8)%Z by lia. exact Cs3.
        - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 112 8 (EVar 69) buf3); cbn [edenot]; ev_simpl E; try lia; auto.
          replace (bv_unsigned (getr R 2) + 112)%Z with (bv_unsigned sp - 320 + 96 + 16)%Z by lia. exact Cb3.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia.
        - apply krange_intro; cbn [edenot]; ev_simpl E. rewrite u_small by lia. lia. }
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as (HZ3 & Hz3).
      run_fp 30%nat [0x1424c%Z] noscr false.
      call_rcurve Hrc rcurve_pre_at (bv_unsigned P + 24)%Z sz1 buf1 In1 Rs1 (Z_to_bv 64 0x14040) Hf H2 H8.
      intros FQ4 rq4 mq4 (Hkeep & Hfkeep & Hfr & r4 & Hr4 & Hr04 & Hc4 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ4. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      know_frame HK Hfr [(SA (EVar 2) (-64), 64%Z); (SA (EVar 8) 24, 32%Z)];
        [unfold v_addi; rewrite H2, H8; repeat f_equal; lia|].
      rewrite !u_small_frame in Hc4 by lia.
      destruct (after_rcurve M mq4 (bv_unsigned P + 24) ltac:(lia) HS Hf HZ3 _ Hz3 ltac:(lia) Hfr) as (HS4 & Hf4 & HZ4 & Hz4 & _).
      specialize (Hz4 (bv_unsigned P + 56)%Z 920%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      clear Hfr HZ3 Hz3.
      destruct Hr04 as [-> | ->].
      { add_krange (EVar 80) 0%Z 0%Z by (rewrite Hr4; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false. fail_with HR HFr H2 H3 H4 H8 HFK HS4 Hf4. }
      specialize (Hc4 eq_refl).
      add_krange (EVar 80) 1%Z 1%Z by (rewrite Hr4; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x1424c%Z] noscr false.
      call_rcurve Hrc rcurve_pre_at (bv_unsigned P + 56)%Z sz2 buf2 In2 Rs2 (Z_to_bv 64 0x14058) Hf4 H2 H8.
      intros FQ5 rq5 mq5 (Hkeep & Hfkeep & Hfr & r5 & Hr5 & Hr05 & Hc5 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ5. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      know_frame HK Hfr [(SA (EVar 2) (-64), 64%Z); (SA (EVar 8) 56, 32%Z)];
        [unfold v_addi; rewrite H2, H8; repeat f_equal; lia|].
      rewrite !u_small_frame in Hc5 by lia.
      destruct (after_rcurve mq4 mq5 (bv_unsigned P + 56) ltac:(lia) HS4 Hf4 HZ4 _ Hz4 ltac:(lia) Hfr) as (HS5 & Hf5 & HZ5 & Hz5 & HK5).
      specialize (Hz5 (bv_unsigned P + 88)%Z 888%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      pose proof (HK5 _ Hc4 ltac:(lia) ltac:(lia)) as C1_5.
      clear Hfr HZ4 Hz4 HS4 Hf4 Hc4 HK5.
      destruct Hr05 as [-> | ->].
      { add_krange (EVar 144) 0%Z 0%Z by (rewrite Hr5; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false. fail_with HR HFr H2 H3 H4 H8 HFK HS5 Hf5. }
      specialize (Hc5 eq_refl).
      add_krange (EVar 144) 1%Z 1%Z by (rewrite Hr5; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 30%nat [0x1424c%Z] noscr false.
      call_rcurve Hrc rcurve_pre_at (bv_unsigned P + 88)%Z sz3 buf3 In3 Rs3 (Z_to_bv 64 0x14070) Hf5 H2 H8.
      intros FQ6 rq6 mq6 (Hkeep & Hfkeep & Hfr & r6 & Hr6 & Hr06 & Hc6 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ6. clear Hkeep Hfkeep.
      apply rcurve_frame_norm in Hfr.
      know_frame HK Hfr [(SA (EVar 2) (-64), 64%Z); (SA (EVar 8) 88, 32%Z)];
        [unfold v_addi; rewrite H2, H8; repeat f_equal; lia|].
      rewrite !u_small_frame in Hc6 by lia.
      destruct (after_rcurve mq5 mq6 (bv_unsigned P + 88) ltac:(lia) HS5 Hf5 HZ5 _ Hz5 ltac:(lia) Hfr) as (HS6 & Hf6 & HZ6 & Hz6 & HK6).
      specialize (Hz6 (bv_unsigned P + 120)%Z 856%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      pose proof (HK6 _ C1_5 ltac:(lia) ltac:(lia)) as C1_6.
      pose proof (HK6 _ Hc5 ltac:(lia) ltac:(lia)) as C2_6.
      clear Hfr HZ5 Hz5 HS5 Hf5 Hc5 C1_5 HK6.
      destruct Hr06 as [-> | ->].
      { add_krange (EVar 208) 0%Z 0%Z by (rewrite Hr6; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false. fail_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6. }
      specialize (Hc6 eq_refl).
      add_krange (EVar 208) 1%Z 1%Z by (rewrite Hr6; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      run_fp 10%nat [0x1407c%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 964, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      kread_fact HK (EVar 8) 964%Z 1%nat C964.
      rewrite H8 in C964. unfold v_addi in C964.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        destruct (after_trc mq6 M2 HS6 Hf6 HZ6 Hz6 C1_6 C2_6 Hc6 Hfr2 ltac:(split; [lia | exact C964])) as (HS7 & Hf7 & HF7);
        apply (blockC3_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hxyz Ha2b Hb2a psz tc 1 raw
                 Htags ltac:(lia) I R2 M2) end.
      - common HR HFr H2 H3 H4 H8 HFK.
      - exact HS7.
      - exact Hf7.
      - regv HR (9%bv:reg). exact H9.
      - regv HR (19%bv:reg). exact H19.
      - regv HR (20%bv:reg). exact H20.
      - regv HR (23%bv:reg). exact H23.
      - exact HF7.
    Qed.
  End RunB.
End C2.
End LibParseC2S1.

Module LibParseC2aS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section C2a.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.

  #[local] Notation ZFACTS := (ZFACTS sp data P psz tc raw).
  #[local] Notation XT := (XT sp data len).

  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H23 : getr R 23 = Z_to_bv 64 2.
    Hypothesis HF : ZFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [])) (blobs_ev [bs]).

    Definition kn_C2 : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976].

    Lemma kn_C2_ok : know_ok SEGS E M kn_C2.
    Proof using HC HE Hf raw rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      unfold kn_C2, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
    Qed.

    Ltac call_gettag sig k retw Hfx C0 C20 H8 H2 :=
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz sig (Z_to_bv 64 (bv_unsigned sp - 320 + k)) I R1 Mx ro retw);
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 k _ psz tc Hfx C0 C20 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.

    (* [comment removed for export] *)
    Ltac to_C3 HR HFr H2 H3 H4 H8 HFK HSx Hfx HFx :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockC3_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hxyz Ha2b Hb2a psz tc 0 raw
                 Htags ltac:(lia) I R2 M2);
        [ common HR HFr H2 H3 H4 H8 HFK | exact HSx | exact Hfx
        | regv HR (9%bv:reg); exact H9
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | regv HR (23%bv:reg); exact H23
        | apply (ZFACTS_D regs mem rom ret sp data prio P len bs HE); exact HFx ]
      end.

    Lemma blockC2_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13fe4) M rom) Q.
    Proof using H19 H20 H23 H9 HC HE HF HS Ha2b Hb2a Hf Hgettag Hrc Htags Hxyz.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_C2_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as ((_ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x72545243%Z 144%Z (Z_to_bv 64 0x13ff8) Hf F3 F5 H8 H2.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 144, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 144 ltac:(lia) HS Hfr) as HS1.
      pose proof (ZFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ 144%Z ltac:(lia) HF Hfr) as HF1.
      clear Hfr F3 F5.
      destruct Hr01 as [-> | ->].
      { add_krange (EVar 74) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1407c%Z] noscr false. to_C3 HR HFr H2 H3 H4 H8 HFK HS1 Hf1 HF1. }
      pose proof (XT_intro regs mem rom ret sp data prio P len bs HE raw mq1 144%Z _ ltac:(lia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 74) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as ((_ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x67545243%Z 120%Z (Z_to_bv 64 0x14010) Hf1 F3 F5 H8 H2.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Htag2).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 120, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf1 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 120 ltac:(lia) Hfr)) as Hf2.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 120 ltac:(lia) HS1 Hfr) as HS2.
      pose proof (ZFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ 120%Z ltac:(lia) HF1 Hfr) as HF2.
      pose proof (XT_frame regs mem rom ret sp data prio P len bs HE raw _ _ _ _ _ X1 Hfr ltac:(lia) ltac:(solve_apart)) as X1b.
      clear Hfr F3 F5 X1 HF1 HS1 Hf1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 138) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1407c%Z] noscr false. to_C3 HR HFr H2 H3 H4 H8 HFK HS2 Hf2 HF2. }
      pose proof (XT_intro regs mem rom ret sp data prio P len bs HE raw mq2 120%Z _ ltac:(lia) (Htag2 eq_refl)) as X2. clear Htag2.
      add_krange (EVar 138) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      pose proof HF2 as HF'. destruct HF' as ((_ & _ & F3 & _ & F5) & _).
      run_fp 30%nat [0x137b4%Z] noscr false.
      call_gettag 0x62545243%Z 96%Z (Z_to_bv 64 0x14028) Hf2 F3 F5 H8 H2.
      intros FQ3 rq3 mq3 (Hkeep & Hfkeep & Hfr & r3 & Hr3 & Hr03 & Htag3).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ3. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 96, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf2 (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 96 ltac:(lia) Hfr)) as Hf3.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 96 ltac:(lia) HS2 Hfr) as HS3.
      pose proof (ZFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ 96%Z ltac:(lia) HF2 Hfr) as HF3.
      pose proof (XT_frame regs mem rom ret sp data prio P len bs HE raw _ _ _ _ _ X1b Hfr ltac:(lia) ltac:(solve_apart)) as X1c.
      pose proof (XT_frame regs mem rom ret sp data prio P len bs HE raw _ _ _ _ _ X2 Hfr ltac:(lia) ltac:(solve_apart)) as X2c.
      clear Hfr F3 F5 X1b X2 HF2 HS2 Hf2.
      destruct Hr03 as [-> | ->].
      { add_krange (EVar 202) 0%Z 0%Z by (rewrite Hr3; rewrite u_small by lia; lia).
        run_fp 10%nat [0x1407c%Z] noscr false. to_C3 HR HFr H2 H3 H4 H8 HFK HS3 Hf3 HF3. }
      pose proof (XT_intro regs mem rom ret sp data prio P len bs HE raw mq3 96%Z _ ltac:(lia) (Htag3 eq_refl)) as X3. clear Htag3.
      add_krange (EVar 202) 1%Z 1%Z by (rewrite Hr3; rewrite u_small by lia; lia).
      run_fp 2%nat [0x1402c%Z] noscr false.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        eapply (blockC2b_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw Htags
                 I R2 M2);
        [ common HR HFr H2 H3 H4 H8 HFK | exact HS3 | exact Hf3
        | regv HR (9%bv:reg); exact H9
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | regv HR (23%bv:reg); exact H23
        | exact HF3 | exact X1c | exact X2c | exact X3 ]
      end.
    Qed.
  End Run.
End C2a.
End LibParseC2aS1.

Module LibParseC1S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section C1.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).
  Hypothesis Htags : tags_ok len bs tc psz.

  #[local] Notation ZFACTS := (ZFACTS sp data P psz tc raw).
  #[local] Notation ZH := (ZH sp data P psz tc raw).
  #[local] Notation DFACTS := (DFACTS sp data P len psz tc).
  #[local] Notation XT := (XT sp data len).

  (* [comment removed for export] *)
  Lemma after_copy : forall Mq M2 (w0 w1 w2 : word),
    SAVED Mq -> frame_mod mem Mq BIG -> ZH Mq -> zero Mq (bv_unsigned P + 56) 920 ->
    curve_ok SEGS Mq data len (bv_unsigned P + 24) ->
    cell64 SEGS Mq (bv_unsigned P + 24) w0 -> cell64 SEGS Mq (bv_unsigned P + 32) w1 -> cell64 SEGS Mq (bv_unsigned P + 40) w2 ->
    frame_mod Mq M2 [(Z_to_bv 64 (bv_unsigned P + 56), 32%Z); (Z_to_bv 64 (bv_unsigned P + 88), 32%Z);
                     (Z_to_bv 64 (bv_unsigned P + 964), 1%Z)] ->
    cell64 SEGS M2 (bv_unsigned P + 56) w0 -> cell64 SEGS M2 (bv_unsigned P + 64) w1 -> cell64 SEGS M2 (bv_unsigned P + 72) w2 ->
    cell64 SEGS M2 (bv_unsigned P + 88) w0 -> cell64 SEGS M2 (bv_unsigned P + 96) w1 -> cell64 SEGS M2 (bv_unsigned P + 104) w2 ->
    cell8 SEGS M2 (bv_unsigned P + 964) 1 ->
    SAVED M2 /\ frame_mod mem M2 BIG /\ DFACTS 1 0 raw M2.
  Proof.
    intros Mq M2 w0 w1 w2 HS Hf HZ Hz Hc C0 C1 C2 Hfr D0 D1 D2 D3 D4 D5 C964.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    pose proof (ZH_frame regs mem rom ret sp data prio P len bs HE psz tc raw Mq M2 _ HZ Hfr ltac:(solve_apart) ltac:(solve_apart)) as (F1 & F2 & F3 & F4 & F5).
    unfold LibParseDS1.DFACTS. cbv zeta.
    split; [exact F1|]. split; [exact F2|]. split; [exact F3|]. split; [exact F4|]. split; [exact F5|].
    split.
    { repeat constructor.
      - eapply curve_ok_frame; [exact Hfr | exact Hc | lia | lia | solve_apart].
      - eapply (curve_ok_copy SEGS Mq data len (bv_unsigned P + 24) w0 w1 w2 Hc C0);
          [replace (bv_unsigned P + 24 + 8)%Z with (bv_unsigned P + 32)%Z by lia; exact C1
          |replace (bv_unsigned P + 24 + 16)%Z with (bv_unsigned P + 40)%Z by lia; exact C2
          |exact D0
          |replace (bv_unsigned P + 56 + 8)%Z with (bv_unsigned P + 64)%Z by lia; exact D1
          |replace (bv_unsigned P + 56 + 16)%Z with (bv_unsigned P + 72)%Z by lia; exact D2].
      - eapply (curve_ok_copy SEGS Mq data len (bv_unsigned P + 24) w0 w1 w2 Hc C0);
          [replace (bv_unsigned P + 24 + 8)%Z with (bv_unsigned P + 32)%Z by lia; exact C1
          |replace (bv_unsigned P + 24 + 16)%Z with (bv_unsigned P + 40)%Z by lia; exact C2
          |exact D3
          |replace (bv_unsigned P + 88 + 8)%Z with (bv_unsigned P + 96)%Z by lia; exact D4
          |replace (bv_unsigned P + 88 + 16)%Z with (bv_unsigned P + 104)%Z by lia; exact D5]. }
    split; [eapply zero_frame; [exact Hfr | eapply zero_sub; [exact Hz | lia | lia] | lia | lia | solve_apart]|].
    split; [exact C964|].
    split.
    - eapply cell8_frame; [exact Hfr | | lia | lia | solve_apart].
      replace (bv_unsigned P + 965)%Z with (bv_unsigned P + 56 + 909)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
    - eapply cell8_frame; [exact Hfr | | lia | lia | solve_apart].
      replace (bv_unsigned P + 966)%Z with (bv_unsigned P + 56 + 910)%Z by lia. eapply zero_cell8; [exact Hz | lia | lia | lia | lia].
  Qed.

  (* [comment removed for export] *)
  Lemma after_fsw : forall M2 M3,
    SAVED M2 -> frame_mod mem M2 BIG -> DFACTS 1 0 raw M2 ->
    frame_mod M2 M3 [(Z_to_bv 64 (bv_unsigned P + 120), 4%Z); (Z_to_bv 64 (bv_unsigned P + 136), 4%Z);
                     (Z_to_bv 64 (bv_unsigned P + 152), 4%Z); (Z_to_bv 64 (bv_unsigned P + 965), 1%Z)] ->
    cell8 SEGS M3 (bv_unsigned P + 965) 1 ->
    SAVED M3 /\ frame_mod mem M3 BIG /\ DFACTS 1 1 raw M3.
  Proof.
    intros M2 M3 HS Hf (F1 & F2 & F3 & F4 & F5 & F6 & F7 & F8 & F9 & F10) Hfr C965.
    pose proof HE as HE'.
    destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _ & _ & _ & (S1 & _) & _ & _ & _ & _ & A4 & _).
    pose proof (u64_range sp). pose proof (u64_range P).
    split; [eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS | exact Hfr | solve_apart | lia]|].
    split; [eapply frame_mod_trans_same; [exact Hf|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered|].
    unfold LibParseDS1.DFACTS. cbv zeta.
    split; [eapply cell64_frame; [exact Hfr | exact F1 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact F2 | lia | lia | solve_apart]|].
    split; [eapply cell64_frame; [exact Hfr | exact F3 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F4 | lia | lia | solve_apart]|].
    split; [eapply cell32_frame; [exact Hfr | exact F5 | lia | lia | solve_apart]|].
    split; [eapply trc_curves_frame; [exact Hfr | exact F6 | lia | lia | solve_apart]|].
    split; [eapply zero_frame; [exact Hfr | exact F7 | lia | lia | solve_apart]|].
    split; [eapply cell8_frame; [exact Hfr | exact F8 | lia | lia | solve_apart]|].
    split; [exact C965|].
    eapply cell8_frame; [exact Hfr | exact F10 | lia | lia | solve_apart].
  Qed.

  (* [comment removed for export] *)
  Lemma trc0_words : forall Mq,
    present Mq (bv_unsigned P + 24) 32 ->
    exists w0 w1 w2 w3,
      cell64 SEGS Mq (bv_unsigned P + 24) w0 /\ cell64 SEGS Mq (bv_unsigned P + 32) w1 /\
      cell64 SEGS Mq (bv_unsigned P + 40) w2 /\ cell64 SEGS Mq (bv_unsigned P + 48) w3.
  Proof.
    intros Mq Hp. pose proof (u64_range P).
    destruct HE as (_ & _ & _ & _ & _ & _ & _ & _ & _ & (WP1 & WP2 & WP3 & WP4) & _).
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 24) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w0 C0].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 32) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w1 C1].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 40) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w2 C2].
    destruct (present_cell64 SEGS Mq (bv_unsigned P + 48) ltac:(eapply present_sub; [exact Hp | lia | lia]) ltac:(lia) ltac:(lia)) as [w3 C3].
    exists w0, w1, w2, w3. auto.
  Qed.

  Ltac call_rcurve Hrc pre_at c sz buf Hin Rsz retw Hfx H2 H8 :=
    lazymatch goal with
    | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
      eapply rt_call;
      [ eapply (Hrc data len bs (Z_to_bv 64 (bv_unsigned sp - 320)) buf (Z_to_bv 64 c) (Z_to_bv 64 0) sz I R1 Mx ro retw);
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | apply (pre_at Mx I R1 c sz buf Hfx Hin Rsz ltac:(lia));
          [ regv HR (2%bv:reg); rewrite <- (Z_to_bv_bv_unsigned 64 (getr _ 2)), H2; reflexivity
          | regv HR (10%bv:reg); reflexivity
          | regv HR (11%bv:reg); reflexivity
          | regv_lin HR (12%bv:reg); rewrite H8; f_equal; lia
          | regv HR (13%bv:reg); reflexivity ] ]
      | cbv beta ]
    end.

  Section Run.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H23 : getr R 23 = Z_to_bv 64 2.
    Hypothesis HF : ZFACTS M.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI)) ++ [raw])) (blobs_ev [bs]).

    Definition kn_C1 : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KWord (SA (EVar 2) 8) 8 (EVar 64)].

    Lemma kn_C1_ok : know_ok SEGS E M kn_C1.
    Proof.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      destruct HF as ((F1 & F2 & _) & _).
      unfold kn_C1, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 8 8 (EVar 64) raw); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 8)%Z with (bv_unsigned sp - 312)%Z by lia. exact F2.
    Qed.

    Ltac to_C2 HR HFr H2 H3 H4 H8 HFK HSx Hfx HFx :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockC2_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw
                 Htags I R2 M2);
        [ common HR HFr H2 H3 H4 H8 HFK | exact HSx | exact Hfx
        | regv HR (9%bv:reg); exact H9
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | regv HR (23%bv:reg); exact H23
        | exact HFx ]
      end.

    Ltac to_D HR HFr H2 H3 H4 H8 HFK HSx Hfx HFx v :=
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (blockD_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Ha2b Hb2a psz tc 1 v raw
                 Htags ltac:(lia) ltac:(lia) I R2 M2);
        [ common HR HFr H2 H3 H4 H8 HFK | exact HSx | exact Hfx
        | regv HR (9%bv:reg); exact H9
        | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20
        | regv HR (23%bv:reg); exact H23
        | exact HFx ]
      end.

    (* [comment removed for export] *)
    Lemma ktrc_run : forall (FPc : FPState) Rc,
      COMMON FPc Rc -> getr Rc 9 = prio -> getr Rc 19 = Z_to_bv 64 len -> getr Rc 20 = data -> getr Rc 23 = Z_to_bv 64 2 ->
      runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13f4c) M rom) Q.
    Proof.
      clear HC H9 H19 H20 H23.
      intros FPc Rc HC H9 H19 H20 H23.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      set (Ec := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [raw])) (blobs_ev [bs])).
      assert (HR : regs_ok Ec (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok Ec (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS Ec M kn_C1).
      { (* [comment removed for export] *)
        pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (_ & _ & _ & S4M).
        pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (_ & _ & _ & W4M).
        destruct HF as ((F1 & F2 & _) & _).
        unfold kn_C1, know_ok.
        repeat (apply Forall_cons); [..|apply Forall_nil].
        - apply krange_intro; cbn. rewrite H2. lia.
        - apply krange_intro; cbn. rewrite H8. lia.
        - apply (kwr_intro SEGS Ec M (EVar 2) (getr Rc 2) (-336) 656); cbn; try lia; try reflexivity.
          replace (bv_unsigned (getr Rc 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4M.
        - apply (kwr_intro SEGS Ec M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
          rewrite Z.add_0_r. exact W4M.
        - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl Ec. rewrite H2, H8. lia.
        - eapply (kword_intro SEGS Ec M (EVar 2) (getr Rc 2) 8 8 (EVar 64) raw); cbn; try lia; auto.
          replace (bv_unsigned (getr Rc 2) + 8)%Z with (bv_unsigned sp - 312)%Z by lia. exact F2. }
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 30%nat [0x137b4%Z; 0x13fe4%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hgray.
      { (* [comment removed for export] *) to_C2 HR HFr H2 H3 H4 H8 HFK HS Hf HF. }
      (* [comment removed for export] *)
      pose proof HF as HF'. destruct HF' as ((_ & _ & F3 & _ & F5) & Hz).
      run_fp 30%nat [0x137b4%Z] noscr false.
      lazymatch goal with
      | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
        eapply rt_call;
        [ eapply (Hgettag data len bs P tc psz 0x6b545243%Z (Z_to_bv 64 (bv_unsigned sp - 320 + 168)) I R1 Mx ro (Z_to_bv 64 0x13f6c));
          [ regv HR (1%bv:reg); reflexivity
          | apply ret_ok_even; rewrite u_small by lia; reflexivity
          | apply (gettag_pre_at regs mem rom ret sp data prio P len bs HE Mx I R1 168 _ psz tc Hf F3 F5 Htags);
            [ regv HR (10%bv:reg); exact H8
            | regv HR (11%bv:reg); reflexivity
            | regv_lin HR (12%bv:reg); f_equal; lia
            | lia | lia ] ]
        | cbv beta ]
      end.
      intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfr & r1 & Hr1 & Hr01 & Htag1).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
      know_frame HK Hfr [(SA (EVar 2) 168, 24%Z)]; [unfold v_addi; rewrite H2; repeat f_equal; lia|].
      pose proof (frame_mod_trans_same _ _ _ _ Hf (gettag_big regs mem rom ret sp data prio P len bs HE _ _ 168 ltac:(lia) Hfr)) as Hf1.
      pose proof (saved_tag FP0 regs mem rom ret sp data prio P len bs HE _ _ 168 ltac:(lia) HS Hfr) as HS1.
      pose proof (ZFACTS_tag regs mem rom ret sp data prio P len bs HE _ _ _ _ _ 168%Z ltac:(lia) HF Hfr) as HF1.
      assert (Hp1 : present mq1 (bv_unsigned P + 24) 32)
        by (eapply present_frame; [exact Hfr|]; apply zero_present; eapply zero_sub; [exact Hz | lia | lia]).
      clear Hfr F3 F5 Hz.
      destruct Hr01 as [-> | ->].
      { (* [comment removed for export] *)
        add_krange (EVar 75) 0%Z 0%Z by (rewrite Hr1; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13fe4%Z] noscr false. to_C2 HR HFr H2 H3 H4 H8 HFK HS1 Hf1 HF1. }
      pose proof (XT_intro regs mem rom ret sp data prio P len bs HE raw mq1 168%Z _ ltac:(lia) (Htag1 eq_refl)) as X1. clear Htag1.
      add_krange (EVar 75) 1%Z 1%Z by (rewrite Hr1; rewrite u_small by lia; lia).
      destruct X1 as ((sz1 & buf1 & [Rs1 Cs1] & Cb1 & Hs1 & In1) & _ & _).
      unfold cell64, cell in Cb1. unfold cell in Cs1.
      pose proof In1 as (In1a & In1b & In1c). pose proof (u64_range buf1).
      env_extend [Z_to_bv 64 sz1; buf1].
      lazymatch type of HK with know_ok _ ?E2 _ ?kn =>
        assert (HK2 : know_ok SEGS E2 mq1
          ([KWord (SA (EVar 2) 176) 4 (EVar 129); KWord (SA (EVar 2) 184) 8 (EVar 130); KRange (EVar 129) 4 (2^26)] ++ kn));
        [ apply know_ok_app; [| exact HK]; unfold know_ok;
          repeat (apply Forall_cons); try apply Forall_nil;
          [ eapply (kword_intro SEGS E2 mq1 (EVar 2) (getr Rc 2) 176 4 (EVar 129) (Z_to_bv 64 sz1)); cbn [edenot]; ev_simpl E2; try lia; auto;
            replace (bv_unsigned (getr Rc 2) + 176)%Z with (bv_unsigned sp - 320 + 168 + 8)%Z by lia; exact Cs1
          | eapply (kword_intro SEGS E2 mq1 (EVar 2) (getr Rc 2) 184 8 (EVar 130) buf1); cbn [edenot]; ev_simpl E2; try lia; auto;
            replace (bv_unsigned (getr Rc 2) + 184)%Z with (bv_unsigned sp - 320 + 168 + 16)%Z by lia; exact Cb1
          | apply krange_intro; cbn [edenot]; ev_simpl E2; rewrite u_small by lia; lia ]
        | clear HK; rename HK2 into HK; cbn [app] in HK ]
      end.
      (* [comment removed for export] *)
      pose proof HF1 as HF'. destruct HF' as (HZ1 & Hz1).
      run_fp 30%nat [0x1424c%Z] noscr false.
      call_rcurve Hrc (rcurve_pre_at regs mem rom ret sp data prio P len bs HE) (bv_unsigned P + 24)%Z sz1 buf1 In1 Rs1 (Z_to_bv 64 0x13f88) Hf1 H2 H8.
      intros FQ2 rq2 mq2 (Hkeep & Hfkeep & Hfr & r2 & Hr2 & Hr02 & Hc2 & _ & _).
      unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
      after_call Hkeep Hfkeep FQ2. clear Hkeep Hfkeep.
      apply (rcurve_frame_norm regs mem rom ret sp data prio P len bs HE) in Hfr.
      know_frame HK Hfr [(SA (EVar 2) (-64), 64%Z); (SA (EVar 8) 24, 32%Z)];
        [unfold v_addi; rewrite H2, H8; repeat f_equal; lia|].
      rewrite !u_small_frame in Hc2 by lia.
      destruct (after_rcurve FP0 regs mem rom ret sp data prio P len bs HE psz tc raw mq1 mq2 (bv_unsigned P + 24) ltac:(lia) HS1 Hf1 HZ1 _ Hz1 ltac:(lia) Hfr)
        as (HS2 & Hf2 & HZ2 & Hz2 & _).
      specialize (Hz2 (bv_unsigned P + 56)%Z 920%Z ltac:(lia) ltac:(lia) ltac:(lia)).
      assert (Hp2 : present mq2 (bv_unsigned P + 24) 32) by (eapply present_frame; [exact Hfr | exact Hp1]).
      clear Hfr HZ1 Hz1 HS1 Hf1 Hp1 HF1.
      destruct Hr02 as [-> | ->].
      { add_krange (EVar 141) 0%Z 0%Z by (rewrite Hr2; rewrite u_small by lia; lia).
        run_fp 10%nat [0x13e1c%Z] noscr false. fail_with HR HFr H2 H3 H4 H8 HFK HS2 Hf2. }
      specialize (Hc2 eq_refl).
      add_krange (EVar 141) 1%Z 1%Z by (rewrite Hr2; rewrite u_small by lia; lia).
      (* [comment removed for export] *)
      destruct (trc0_words mq2 Hp2) as (w0 & w1 & w2 & w3 & C0 & C1 & C2 & C3).
      pose proof C0 as C0'. pose proof C1 as C1'. pose proof C2 as C2'.
      unfold cell64, cell in C0', C1', C2', C3.
      env_extend [w0; w1; w2; w3].
      lazymatch type of HK with know_ok _ ?E2 _ ?kn =>
        assert (HK2 : know_ok SEGS E2 mq2
          ([KWord (SA (EVar 8) 24) 8 (EVar 195); KWord (SA (EVar 8) 32) 8 (EVar 196);
            KWord (SA (EVar 8) 40) 8 (EVar 197); KWord (SA (EVar 8) 48) 8 (EVar 198)] ++ kn));
        [ apply know_ok_app; [| exact HK]; unfold know_ok;
          repeat (apply Forall_cons); try apply Forall_nil;
          [ eapply (kword_intro SEGS E2 mq2 (EVar 8) P 24 8 (EVar 195) w0); cbn [edenot]; ev_simpl E2; try lia; auto
          | eapply (kword_intro SEGS E2 mq2 (EVar 8) P 32 8 (EVar 196) w1); cbn [edenot]; ev_simpl E2; try lia; auto
          | eapply (kword_intro SEGS E2 mq2 (EVar 8) P 40 8 (EVar 197) w2); cbn [edenot]; ev_simpl E2; try lia; auto
          | eapply (kword_intro SEGS E2 mq2 (EVar 8) P 48 8 (EVar 198) w3); cbn [edenot]; ev_simpl E2; try lia; auto ]
        | clear HK; rename HK2 into HK; cbn [app] in HK ]
      end.
      run_fp 40%nat [0x140e4%Z] noscr true.
      lazymatch goal with
      | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr2 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 8) 56, 32%Z); (SA (EVar 8) 88, 32%Z); (SA (EVar 8) 964, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr2; cbn [map fst snd] in Hfr2; unfold adenot in Hfr2; cbn [a_base a_off edenot] in Hfr2;
        ev_simpl_in E2 Hfr2; rewrite H8 in Hfr2; unfold v_addi in Hfr2;
        clear EQM HLF
      end.
      kread_fact HK (EVar 8) 56%Z 8%nat G0. kread_fact HK (EVar 8) 64%Z 8%nat G1. kread_fact HK (EVar 8) 72%Z 8%nat G2.
      kread_fact HK (EVar 8) 88%Z 8%nat G3. kread_fact HK (EVar 8) 96%Z 8%nat G4. kread_fact HK (EVar 8) 104%Z 8%nat G5.
      kread_fact HK (EVar 8) 964%Z 1%nat C964.
      rewrite H8 in G0, G1, G2, G3, G4, G5, C964. unfold v_addi in G0, G1, G2, G3, G4, G5, C964.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M2 _) _ =>
        destruct (after_copy mq2 M2 w0 w1 w2 HS2 Hf2 HZ2 Hz2 Hc2 C0 C1 C2 Hfr2 G0 G1 G2 G3 G4 G5 ltac:(split; [lia | exact C964]))
          as (HS3 & Hf3 & HF3)
      end.
      clear G0 G1 G2 G3 G4 G5 C964 Hfr2.
      (* [comment removed for export] *)
      branch_case as Hx.
      { (* [comment removed for export] *) to_D HR HFr H2 H3 H4 H8 HFK HS3 Hf3 HF3 0%Z. }
      run_fp 10%nat [0x140e4%Z] noscr true.
      lazymatch goal with
      | EQM : ?M3 = mem_denot ?E2 ?M2 ?log, HLF : log_flat _ _ |- _ =>
        assert (Hfr3 : frame_mod M2 M3 (regions_denot E2 [(SA (EVar 8) 120, 4%Z); (SA (EVar 8) 136, 4%Z); (SA (EVar 8) 152, 4%Z); (SA (EVar 8) 965, 1%Z)]))
          by (rewrite EQM; apply (frame_mod_mem_denot E2 M2 log _ HLF); [flats_auto | vm_compute; reflexivity]);
        unfold regions_denot in Hfr3; cbn [map fst snd] in Hfr3; unfold adenot in Hfr3; cbn [a_base a_off edenot] in Hfr3;
        ev_simpl_in E2 Hfr3; rewrite H8 in Hfr3; unfold v_addi in Hfr3;
        clear EQM HLF
      end.
      kread_fact HK (EVar 8) 965%Z 1%nat C965.
      rewrite H8 in C965. unfold v_addi in C965.
      lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M3 _) _ =>
        destruct (after_fsw _ M3 HS3 Hf3 HF3 Hfr3 ltac:(split; [lia | exact C965])) as (HS4 & Hf4 & HF4)
      end.
      to_D HR HFr H2 H3 H4 H8 HFK HS4 Hf4 HF4 1%Z.
    Qed.

    Lemma blockC1_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13f34) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP.
      pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_C1_ok as HK.
      try clear Hra Hret Hsp; try clear RO; try clear A1; try clear A3 A5 A6; try clear Qal Q0 Q8; try clear D5; try clear Pal; try clear Sal; try clear S2 S3; try clear W1 W2; try clear D WS WP.
      run_fp 10%nat [0x13f4c%Z] noscr false.
      branch_case as Hpx.
      { (* [comment removed for export] *)
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (ktrc_run I R2) end;
          [ common HR HFr H2 H3 H4 H8 HFK
          | regv HR (9%bv:reg); exact H9 | regv HR (19%bv:reg); exact H19
          | regv HR (20%bv:reg); exact H20 | regv HR (23%bv:reg); exact H23 ]. }
      run_fp 10%nat [0x13f4c%Z; 0x13e1c%Z] noscr false.
      branch_case as Hlab.
      { (* [comment removed for export] *) fail_with HR HFr H2 H3 H4 H8 HFK HS Hf. }
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (ktrc_run I R2) end;
        [ common HR HFr H2 H3 H4 H8 HFK
        | regv HR (9%bv:reg); exact H9 | regv HR (19%bv:reg); exact H19
        | regv HR (20%bv:reg); exact H20 | regv HR (23%bv:reg); exact H23 ].
    Qed.
  End Run.
End C1.
End LibParseC1S1.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require LibBswap LibBswapSx.

Module LibParseBS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1 LibParseC1S1 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswapSx.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section B.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).
  Hypothesis Htc : (0 <= tc)%Z.
  Hypothesis Hpsz : (132 + 12 * tc <= psz <= len)%Z.

  #[local] Notation ZFACTS := (ZFACTS sp data P psz tc raw).

  Variable M : word -> option byte.
  Hypothesis HS : SAVED M.
  Hypothesis Hf : frame_mod mem M BIG.
  Hypothesis HF : ZFACTS M.

  (* [comment removed for export] *)
  Definition INV (i : Z) (FPc : FPState) (Rc : bvmap 5 word) : Prop :=
    (0 <= i < tc)%Z /\
    (bv_unsigned (getr Rc 14) = bv_unsigned data + 140 + 12 * i)%Z /\
    (bv_unsigned (getr Rc 13) = tc - i)%Z /\
    (bv_unsigned (getr Rc 12) = psz)%Z /\
    getr Rc 15 = Z_to_bv 64 4 /\ getr Rc 16 = Z_to_bv 64 65280 /\ getr Rc 20 = data /\
    getr Rc 9 = prio /\ getr Rc 19 = Z_to_bv 64 len /\ getr Rc 23 = Z_to_bv 64 2 /\
    COMMON FPc Rc /\
    (forall j, (0 <= j < i)%Z -> (4 <= be32 bs (132 + 12 * j + 8))%Z /\
                                (be32 bs (132 + 12 * j + 4) + be32 bs (132 + 12 * j + 8) <= psz)%Z).

  Section Body.
    Variables (i : Z) (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HI : INV i FPc Rc.
    Hypothesis IH : forall (FPc' : FPState) (R' : bvmap 5 word),
        INV (i + 1) FPc' R' -> runs_to SEGS (mkst (FP:=FPc') R' (Z_to_bv 64 0x13e98) M rom) Q.

    #[local] Abbreviation off_i := (be32 bs (132 + 12 * i + 4)).
    #[local] Abbreviation s_i := (be32 bs (132 + 12 * i + 8)).
    #[local] Abbreviation b0 := (bs_byte bs (132 + 12 * i + 8)).

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc))
                                  ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i; Z_to_bv 64 psz])) (blobs_ev [bs]).

    (* [comment removed for export] *)
    Definition kn_b (slo shi : Z) : list kentry :=
      [KRange (EVar 20) 1 (2^47);
       KRange (EVar 14) 141 (2^47 + 2^26);
       KRange (EVar 13) 1 (2^32);
       KRange (EVar 65) 0 (2^32 - 1);
       KRange (EVar 66) slo shi;
       KRange (EVar 67) 0 (2^26);
       KBlobD (SA (EVar 20) 0) (EVar 64) 0].

    Lemma kn_b_ok : forall slo shi, (slo <= s_i <= shi)%Z -> know_ok SEGS E M (kn_b slo shi).
    Proof.
      intros slo shi Hs.
      destruct HI as (Hi & H14 & H13 & H12 & H15 & H16 & H20 & _).
      pose proof (u64_range data).
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      unfold kn_b, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H20. lia.
      - apply krange_intro; cbn. rewrite H14. lia.
      - apply krange_intro; cbn. rewrite H13. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn. rewrite H20, u_small by lia.
        split; [lia|]. split; [exact D2|]. intros k Hk. rewrite Z.add_0_r. apply D5. exact Hk.
    Qed.

    (* [comment removed for export] *)
    Definition nu (j : nat) : Z :=
      nth j [bs_byte bs (132 + 12 * i); bs_byte bs (132 + 12 * i + 1); bs_byte bs (132 + 12 * i + 2); bs_byte bs (132 + 12 * i + 3);
             bs_byte bs (132 + 12 * i + 4); bs_byte bs (132 + 12 * i + 4 + 1); bs_byte bs (132 + 12 * i + 4 + 2); bs_byte bs (132 + 12 * i + 4 + 3);
             bs_byte bs (132 + 12 * i + 8); bs_byte bs (132 + 12 * i + 8 + 1); bs_byte bs (132 + 12 * i + 8 + 2); bs_byte bs (132 + 12 * i + 8 + 3)]%Z 0%Z.
    Definition atom (sx : bool) (d : Z) : expr * (bool * nat) :=
      (EBlobX sx 0 (EVar 14) d (EVar 20) 1, (sx, Z.to_nat (d + 8))).
    Definition atoms : list (expr * (bool * nat)) :=
      [atom true 3; atom false 0; atom false 1; atom false 2;
       atom false (-3); atom false (-2); atom false (-4); atom true (-1)].

    Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
    Proof. intros k. unfold nu. do 12 (destruct k as [|k]; [cbn [nth]; apply bs_byte_range|]). destruct k; cbn; lia. Qed.

    Lemma atoms_ok_i : atoms_ok E nu atoms.
    Proof.
      destruct HI as (Hi & H14 & H13 & H12 & H15 & H16 & H20 & _).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      unfold atoms, atoms_ok. pose proof (u64_range data).
      repeat (apply Forall_cons); [..|apply Forall_nil];
        unfold atom, atom_ok; cbn [edenot eb ev E blobs_ev nth]; ev_simpl E; rewrite H14, H20;
        first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu; cbn [nth Z.to_nat Z.add Pos.to_nat Pos.iter_op Nat.add]; unfold bs_byte;
        (repeat f_equal); lia.
    Qed.

    Ltac fail_here HR HFr HC :=
      let HC' := fresh "HCx" in
      pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H8 & ?HFK);
      fail_with HR HFr H2 H3 H4 H8 HFK HS Hf.

    (* [comment removed for export] *)
    Lemma tail_ok : forall (FPt : FPState) (Rt : bvmap 5 word),
      (4 <= s_i)%Z ->
      getr Rt 5 = Z_to_bv 64 off_i -> getr Rt 17 = Z_to_bv 64 s_i ->
      (bv_unsigned (getr Rt 14) = bv_unsigned data + 140 + 12 * i)%Z ->
      (bv_unsigned (getr Rt 13) = tc - i)%Z ->
      (bv_unsigned (getr Rt 12) = psz)%Z ->
      getr Rt 15 = Z_to_bv 64 4 -> getr Rt 16 = Z_to_bv 64 65280 -> getr Rt 20 = data ->
      getr Rt 9 = prio -> getr Rt 19 = Z_to_bv 64 len -> getr Rt 23 = Z_to_bv 64 2 ->
      COMMON FPt Rt ->
      runs_to SEGS (mkst (FP:=FPt) Rt (Z_to_bv 64 0x13f20) M rom) Q.
    Proof.
      intros FPt Rt Hs4 T5 T17 T14 T13 T12 T15 T16 T20 T9 T19 T23 HCt.
      pose proof HI as HI'. destruct HI' as (Hi & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & Hsofar).
      pose proof HCt as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      pose proof (u64_range data) as Rd.
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      set (Et := Env (vals_ev (junk_vals Rt ++ fjunk_vals (fp_regs (FPState:=FPt))
                               ++ [Z_to_bv 64 len; Z_to_bv 64 off_i; Z_to_bv 64 s_i; Z_to_bv 64 psz])) (blobs_ev [bs])).
      assert (HR : regs_ok Et (sr_vars 0) Rt) by exact (regs_ok_vars [] Rt _ (blobs_ev [bs])).
      assert (HFr : fregs_ok Et (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rt) fp_regs _ (blobs_ev [bs])).
      assert (HK : know_ok SEGS Et M
        [KRange (EVar 14) 141 (2^47 + 2^26); KRange (EVar 13) 1 (2^32);
         KRange (EVar 65) 0 (2^32 - 1); KRange (EVar 66) 4 (2^32 - 1); KRange (EVar 67) 0 (2^26)]).
      { unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
          apply krange_intro; cbn; rewrite ?T14, ?T13, ?u_small by lia; lia. }
      pin_reg HR (5%bv:reg) (EVar 65) by (rewrite (HR (5%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et; exact T5).
      pin_reg HR (17%bv:reg) (EVar 66) by (rewrite (HR (17%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et; exact T17).
      pin_reg HR (12%bv:reg) (EVar 67) by (rewrite (HR (12%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl Et;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rt 12)), T12; reflexivity).
      run_fp 10%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hend.
      { fail_here HR HFr HCt. }
      br_simpl_in Et Hend.
      rewrite ?alu_add in Hend. unfold v_add in Hend. rewrite ?Z_to_bv_unsigned, ?bv_wrap64_mod in Hend.
      apply Z.ltb_ge in Hend. rewrite !Z.mod_small in Hend by lia.
      run_fp 10%nat [0x13e98%Z; 0x13f34%Z] noscr false.
      (* [comment removed for export] *)
      branch_case as Hmore.
      - (* [comment removed for export] *)
        br_simpl_in Et Hmore.
        apply IH. unfold INV.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]].
        + rewrite alu_add in Hmore. unfold v_add in Hmore. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hmore.
          apply Z.eqb_neq in Hmore. rewrite T13 in Hmore. lia.
        + regv_lin HR (14%bv:reg). rewrite u_small by lia. lia.
        + regv_lin HR (13%bv:reg). rewrite u_small by lia. lia.
        + regv HR (12%bv:reg). rewrite u_small by lia. lia.
        + regv HR (15%bv:reg). exact T15.
        + regv HR (16%bv:reg). exact T16.
        + regv HR (20%bv:reg). exact T20.
        + regv HR (9%bv:reg). exact T9.
        + regv HR (19%bv:reg). exact T19.
        + regv HR (23%bv:reg). exact T23.
        + common HR HFr H2 H3 H4 H8 HFK.
        + intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [| apply Hsofar; lia].
          split; [exact Hs4 | lia].
      - (* [comment removed for export] *)
        br_simpl_in Et Hmore.
        assert (Hlast : (i = tc - 1)%Z).
        { rewrite alu_add in Hmore. unfold v_add in Hmore. rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Hmore.
          apply Z.eqb_eq in Hmore. rewrite T13 in Hmore. lia. }
        assert (Htags : tags_ok len bs tc psz).
        { apply tags_ok_intro; [lia | lia | lia |].
          intros j Hj. destruct (Z.eq_dec j i) as [->|Hne]; [| apply Hsofar; lia]. split; [exact Hs4 | lia]. }
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockC1_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw Htags I R2 M)
        end;
        [ common HR HFr H2 H3 H4 H8 HFK | exact HS | exact Hf
        | regv HR (9%bv:reg); exact T9
        | regv HR (19%bv:reg); exact T19
        | regv HR (20%bv:reg); exact T20
        | regv HR (23%bv:reg); exact T23
        | exact HF ].
    Qed.

    Ltac pin_bytes HR r v ids :=
      pin_reg HR r v by
        (rewrite (HR r);
         lazymatch goal with |- edenot ?E0 ?e = _ =>
           apply bv_eq; rewrite (beval_bytes E0 nu nu_range atoms e ids atoms_ok_i ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
           cbn [edenot ev vals_ev]; ev_simpl E0; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia
         end).

    Ltac to_tail HR HFr HC :=
      let HC' := fresh "HCx" in
      pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H8 & ?HFK);
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ => apply (tail_ok I R2) end;
      [ lia
      | regv HR (5%bv:reg); reflexivity
      | regv HR (17%bv:reg); reflexivity
      | regv HR (14%bv:reg); assumption
      | regv HR (13%bv:reg); assumption
      | regv HR (12%bv:reg); rewrite u_small by lia; reflexivity
      | regv HR (15%bv:reg); reflexivity
      | regv HR (16%bv:reg); reflexivity
      | regv HR (20%bv:reg); assumption
      | regv HR (9%bv:reg); assumption
      | regv HR (19%bv:reg); assumption
      | regv HR (23%bv:reg); assumption
      | common HR HFr H2 H3 H4 H8 HFK ].

    Lemma body_ok : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13e98) M rom) Q.
    Proof.
      pose proof HI as HI'. destruct HI' as (Hi & H14 & H13 & H12 & H15 & H16 & H20 & H9 & H19 & H23 & HC & Hsofar).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      pose proof (u64_range data) as Rd.
      pose proof (be32_range bs (132 + 12 * i + 4)) as Ro. pose proof (be32_range bs (132 + 12 * i + 8)) as Rs.
      pose proof (bs_byte_range bs (132 + 12 * i + 8)) as Rb0.
      pose proof (bs_byte_range bs (132 + 12 * i + 8 + 1)) as Rb1. pose proof (bs_byte_range bs (132 + 12 * i + 8 + 2)) as Rb2.
      pose proof (bs_byte_range bs (132 + 12 * i + 8 + 3)) as Rb3.
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pin_reg HR (15%bv:reg) (ELit 4) by (rewrite (HR (15%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H15).
      pin_reg HR (16%bv:reg) (ELit 65280) by (rewrite (HR (16%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H16).
      pin_reg HR (12%bv:reg) (EVar 67) by (rewrite (HR (12%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr Rc 12)), H12; reflexivity).
      destruct (Z_lt_le_dec b0 128) as [Hb0|Hb0].
      - (* [comment removed for export] *)
        assert (Hb7 : Z.testbit (nu 8%nat) 7 = false).
        { unfold nu. cbn [nth]. apply tb_small_high. cbn [Z.pow Z.pow_pos Pos.iter Z.mul]. lia. }
        assert (Hs31 : (s_i < 2 ^ 31)%Z) by (unfold be32 in *; lia).
        destruct (Z_lt_le_dec s_i 4) as [Hs4|Hs4].
        + (* [comment removed for export] *)
          pose proof (kn_b_ok 0 3 ltac:(lia)) as HK.
          run_fp 40%nat [0x13ec4%Z] noscr false.
          pin_reg HR (17%bv:reg) (EVar 66) by
            (rewrite (HR (17%bv:reg));
             lazymatch goal with |- edenot _ ?e = _ =>
               apply bv_eq; rewrite (beval_bytes_sx E nu nu_range atoms e [11;10;9;8]%nat 8%nat atoms_ok_i ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity))
             end;
             cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).
          run_fp 10%nat [0x13e1c%Z] noscr false.
          fail_here HR HFr HC.
        + (* [comment removed for export] *)
          pose proof (kn_b_ok 4 (2^31 - 1) ltac:(lia)) as HK.
          run_fp 40%nat [0x13ec4%Z] noscr false.
          pin_reg HR (17%bv:reg) (EVar 66) by
            (rewrite (HR (17%bv:reg));
             lazymatch goal with |- edenot _ ?e = _ =>
               apply bv_eq; rewrite (beval_bytes_sx E nu nu_range atoms e [11;10;9;8]%nat 8%nat atoms_ok_i ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity))
             end;
             cbn [edenot ev E vals_ev]; ev_simpl E; rewrite u_small by lia; unfold nu, be32; cbn [bytes_val nth]; lia).
          run_fp 40%nat [0x13f20%Z] noscr false.
          pin_bytes HR (5%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
          to_tail HR HFr HC.
      - (* [comment removed for export] *)
        assert (Hs31 : (2 ^ 31 <= s_i)%Z) by (unfold be32 in *; lia).
        pose proof (kn_b_ok (2^31) (2^32 - 1) ltac:(lia)) as HK.
        run_fp 40%nat [0x13ec4%Z] noscr false.
        branch_case as Hsz.
        { (* [comment removed for export] *) fail_here HR HFr HC. }
        run_fp 40%nat [0x13f20%Z] noscr false.
        pin_bytes HR (17%bv:reg) (EVar 66) [11; 10; 9; 8]%nat.
        pin_bytes HR (5%bv:reg) (EVar 65) [7; 6; 5; 4]%nat.
        to_tail HR HFr HC.
    Qed.
  End Body.

  (* [comment removed for export] *)
  Lemma loopB_run : forall (n : nat) (i : Z) (FPc : FPState) (Rc : bvmap 5 word),
      (tc - i <= Z.of_nat n)%Z -> INV i FPc Rc ->
      runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13e98) M rom) Q.
  Proof.
    induction n as [|n IHn]; intros i FPc Rc Hn HI.
    - destruct HI as (Hi & _). exfalso. lia.
    - apply (body_ok i FPc Rc HI). intros FPc' R' HI'. apply (IHn (i + 1)%Z FPc' R'); [| exact HI'].
      lia.
  Qed.

  Lemma blockB_run : forall (FPc : FPState) (Rc : bvmap 5 word),
      INV 0 FPc Rc -> runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13e98) M rom) Q.
  Proof. intros FPc Rc HI. apply (loopB_run (Z.to_nat tc) 0 FPc Rc); [lia | exact HI]. Qed.
End B.
End LibParseBS1.

Module LibParseA2S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1 LibParseC1S1 LibParseBS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section A2.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  (* [comment removed for export] *)
  Variables (psz tc : Z) (raw : word).
  Hypothesis Htc : (0 <= tc)%Z.
  Hypothesis Hpsz : (132 + 12 * tc <= psz <= len)%Z.

  #[local] Notation ZFACTS := (ZFACTS sp data P psz tc raw).

  Variable M : word -> option byte.
  Hypothesis HS : SAVED M.
  Hypothesis Hf : frame_mod mem M BIG.
  Hypothesis HF : ZFACTS M.

  (* [comment removed for export] *)
  Definition AREGS (Rc : bvmap 5 word) : Prop :=
    (bv_unsigned (getr Rc 12) = psz)%Z /\ (bv_unsigned (getr Rc 13) = tc)%Z /\
    ((bv_unsigned (getr Rc 14) = 0)%Z <-> tc = 0%Z) /\
    getr Rc 9 = prio /\ getr Rc 19 = Z_to_bv 64 len /\ getr Rc 20 = data.

  Ltac fail_here HR HFr HC :=
    let HC' := fresh "HCx" in
    pose proof HC as HC'; destruct HC' as (?H2 & ?H3 & ?H4 & ?H8 & ?HFK);
    fail_with HR HFr H2 H3 H4 H8 HFK HS Hf.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section Setup.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.
    Hypothesis H23 : getr Rc 23 = Z_to_bv 64 2.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev [bs]).

    Definition kn_s (lo14 hi14 : Z) : list kentry :=
      [KRange (EVar 14) lo14 hi14; KRange (EVar 13) 0 (2^23); KRange (EVar 20) 1 (2^47)].

    Lemma kn_s_ok : forall lo14 hi14, (lo14 <= bv_unsigned (getr Rc 14) <= hi14)%Z -> know_ok SEGS E M (kn_s lo14 hi14).
    Proof.
      intros lo14 hi14 H14. destruct HA as (A12 & A13 & A14 & A9 & A19 & A20).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      unfold kn_s, know_ok. repeat (apply Forall_cons); [..|apply Forall_nil];
        apply krange_intro; cbn; rewrite ?A13, ?A20; lia.
    Qed.

    Lemma setup_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13e74) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HA as HA'. destruct HA' as (A12 & A13 & A14 & A9 & A19 & A20).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (D1 & D2 & D3 & D4 & D5).
      pose proof (u64_range data) as Rd. pose proof (u64_range (getr Rc 14)) as R14.
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      destruct (Z.eq_dec tc 0) as [Htc0 | Htc0].
      - (* [comment removed for export] *)
        pose proof (kn_s_ok 0 0 ltac:(lia)) as HK.
        run_fp 10%nat [0x13f34%Z] noscr false.
        assert (Htags : tags_ok len bs tc psz) by (apply tags_ok_intro; [lia | lia | lia | intros j Hj; exfalso; lia]).
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockC1_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw Htags I R2 M)
        end;
        [ common HR HFr H2 H3 H4 H8 HFK | exact HS | exact Hf
        | regv HR (9%bv:reg); exact A9
        | regv HR (19%bv:reg); exact A19
        | regv HR (20%bv:reg); exact A20
        | regv HR (23%bv:reg); exact H23
        | exact HF ].
      - (* [comment removed for export] *)
        pose proof (kn_s_ok 1 (2^64 - 1) ltac:(lia)) as HK.
        run_fp 20%nat [0x13e98%Z] noscr false.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ _ _) _ =>
          apply (blockB_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc raw Htc Hpsz M HS Hf HF I R2)
        end.
        unfold INV.
        split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split; [| split]]]]]]]]]].
        + lia.
        + regv_lin HR (14%bv:reg). rewrite A20, u_small by lia. lia.
        + regv HR (13%bv:reg). rewrite alu_sltu. unfold v_sltu, c_ltu, bv_ltu. rewrite (u_small 1), A13 by lia.
          destruct (Z.ltb_spec tc 1); [exfalso; lia|].
          rewrite alu_add. unfold v_add. rewrite A13, (u_small 0), u_small by lia. lia.
        + regv HR (12%bv:reg). exact A12.
        + regv HR (15%bv:reg). reflexivity.
        + regv HR (16%bv:reg). reflexivity.
        + regv HR (20%bv:reg). exact A20.
        + regv HR (9%bv:reg). exact A9.
        + regv HR (19%bv:reg). exact A19.
        + regv HR (23%bv:reg). exact H23.
        + common HR HFr H2 H3 H4 H8 HFK.
        + intros j Hj. exfalso. lia.
    Qed.
  End Setup.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageZ.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.
    Hypothesis H23 : getr Rc 23 = Z_to_bv 64 2.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev [bs]).

    Lemma kn_z_ok : know_ok SEGS E M [KImg 0x103ec 0x1048c].
    Proof.
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      apply kimg_intro; [lia | lia | exact (penv_ro regs mem rom ret sp data prio P len bs HE M Hf)].
    Qed.

    Lemma stageZ_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13dd8) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HA as HA'. destruct HA' as (A12 & A13 & A14 & A9 & A19 & A20).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_z_ok as HK.
      run_fp 30%nat [0x13e74%Z; 0x13e1c%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x13e74%Z; 0x13e1c%Z] noscr false;
        branch_case as Hok;
        first
          [ (* [comment removed for export] *)
            lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x13e74) _ _) _ => apply (setup_run I R2) end;
            [ common HR HFr H2 H3 H4 H8 HFK
            | unfold AREGS;
              split; [regv HR (12%bv:reg); exact A12|];
              split; [regv HR (13%bv:reg); exact A13|];
              split; [regv HR (14%bv:reg); exact A14|];
              split; [regv HR (9%bv:reg); exact A9|];
              split; [regv HR (19%bv:reg); exact A19|];
              regv HR (20%bv:reg); exact A20
            | regv HR (23%bv:reg); exact H23 ]
          | fail_here HR HFr HC ].
    Qed.
  End StageZ.
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageY.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev [bs]).

    Lemma kn_y_ok : know_ok SEGS E M [KImg 0x103ec 0x1048c; KRange (EVar 2) 336 (2^64 - 321); KWord (SA (EVar 2) 16) 8 (ELit 2)].
    Proof.
      destruct HC as (H2 & H3 & H4 & H8 & HFK). pose proof (u64_range sp).
      pose proof HE as HE'. destruct HE' as (_ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & _ & (S1 & _) & _).
      destruct HF as ((F1 & _) & _).
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply kimg_intro; [lia | lia | exact (penv_ro regs mem rom ret sp data prio P len bs HE M Hf)].
      - apply krange_intro; cbn. rewrite H2. lia.
      - eapply (kword_intro SEGS E M (EVar 2) (getr Rc 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
        replace (bv_unsigned (getr Rc 2) + 16)%Z with (bv_unsigned sp - 304)%Z by lia. exact F1.
    Qed.

    Lemma stageY_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13d90) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HA as HA'. destruct HA' as (A12 & A13 & A14 & A9 & A19 & A20).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_y_ok as HK.
      run_fp 30%nat [0x13dd8%Z; 0x13e1c%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x13dd8%Z; 0x13e1c%Z] noscr false;
        branch_case as Hok;
        first
          [ lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x13dd8) _ _) _ => apply (stageZ_run I R2) end;
            [ common HR HFr H2 H3 H4 H8 HFK
            | unfold AREGS;
              split; [regv HR (12%bv:reg); exact A12|];
              split; [regv HR (13%bv:reg); exact A13|];
              split; [regv HR (14%bv:reg); exact A14|];
              split; [regv HR (9%bv:reg); exact A9|];
              split; [regv HR (19%bv:reg); exact A19|];
              regv HR (20%bv:reg); exact A20
            | regv HR (23%bv:reg); reflexivity ]
          | fail_here HR HFr HC ].
    Qed.
  End StageY.

  (* [comment removed for export] *)
  (* [comment removed for export] *)
  (* [comment removed for export] *)
  Section StageX.
    Variables (FPc : FPState) (Rc : bvmap 5 word).
    Hypothesis HC : COMMON FPc Rc.
    Hypothesis HA : AREGS Rc.

    Let E : env := Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ [])) (blobs_ev [bs]).

    Lemma kn_x_ok : know_ok SEGS E M [KImg 0x103ec 0x1048c].
    Proof.
      unfold know_ok. repeat (apply Forall_cons); [..|apply Forall_nil].
      apply kimg_intro; [lia | lia | exact (penv_ro regs mem rom ret sp data prio P len bs HE M Hf)].
    Qed.

    Lemma stageX_run : runs_to SEGS (mkst (FP:=FPc) Rc (Z_to_bv 64 0x13d38) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HA as HA'. destruct HA' as (A12 & A13 & A14 & A9 & A19 & A20).
      assert (HR : regs_ok E (sr_vars 0) Rc) by exact (regs_ok_vars [] Rc _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals Rc) fp_regs _ (blobs_ev [bs])).
      pose proof kn_x_ok as HK.
      run_fp 30%nat [0x13d90%Z; 0x13e1c%Z] noscr false.
      branch_case as Habs;
        run_fp 10%nat [0x13d90%Z; 0x13e1c%Z] noscr false;
        branch_case as Hok;
        first
          [ lazymatch goal with |- runs_to _ (@mkst ?I ?R2 (Z_to_bv 64 0x13d90) _ _) _ => apply (stageY_run I R2) end;
            [ common HR HFr H2 H3 H4 H8 HFK
            | unfold AREGS;
              split; [regv HR (12%bv:reg); exact A12|];
              split; [regv HR (13%bv:reg); exact A13|];
              split; [regv HR (14%bv:reg); exact A14|];
              split; [regv HR (9%bv:reg); exact A9|];
              split; [regv HR (19%bv:reg); exact A19|];
              regv HR (20%bv:reg); exact A20 ]
          | fail_here HR HFr HC ].
    Qed.
  End StageX.
End A2.
End LibParseA2S1.

Module LibParseA1S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1 LibParseBS1 LibParseA2S1 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswapSx.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section A1.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  #[local] Abbreviation psz := (be32 bs 0).
  #[local] Abbreviation tc := (be32 bs 128).
  (* [comment removed for export] *)
  #[local] Abbreviation lepcs := (bs_byte bs 20 + bs_byte bs 21 * 256 + bs_byte bs 22 * 65536 + bs_byte bs 23 * 16777216)%Z.
  #[local] Abbreviation letc := (bs_byte bs 128 + bs_byte bs 129 * 256 + bs_byte bs 130 * 65536 + bs_byte bs 131 * 16777216)%Z.

  (* [comment removed for export] *)
  Definition nu (k : nat) : Z := bs_byte bs (Z.of_nat k).
  Definition atomu (d : nat) : expr * (bool * nat) := (EBlob false 0 (Z.of_nat d) 1, (false, d)).
  Definition atoms_s (d : nat) : expr * (bool * nat) := (EBlob true 0 (Z.of_nat d) 1, (true, d)).
  Definition atoms : list (expr * (bool * nat)) :=
    map atomu [0; 1; 2; 8; 9; 10; 11; 16; 17; 18; 19; 20; 21; 22; 23; 36; 37; 38; 68; 69; 70; 72; 73; 74; 76; 77; 78; 128; 129; 130; 131]%nat
    ++ map atoms_s [3; 39; 71; 75; 79]%nat.

  Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
  Proof. intros k. unfold nu. apply bs_byte_range. Qed.

  Lemma atoms_ok_at : forall (FPc : FPState) (Rc : bvmap 5 word) (ws : list word),
    (132 <= len)%Z ->
    atoms_ok (Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ ws)) (blobs_ev [bs])) nu atoms.
  Proof.
    intros FPc Rc ws Hlen.
    destruct HE as (_ & _ & _ & (D1 & D2 & _) & _).
    unfold atoms, atoms_ok. cbn [map app].
    repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atomu, atoms_s, atom_ok; cbn [edenot eb blobs_ev nth Z.of_nat Pos.of_succ_nat Pos.succ];
      first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu, bs_byte; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac log_frame RS Hfr H2 H8 :=
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr : frame_mod M1 M2 (regions_denot E2 RS))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
      unfold regions_denot in Hfr; cbn [map fst snd] in Hfr; unfold adenot in Hfr; cbn [a_base a_off edenot] in Hfr;
      ev_simpl_in E2 Hfr; rewrite ?H2, ?H8 in Hfr; unfold v_addi in Hfr; clear EQM HLF
    end.

  (* [comment removed for export] *)
  Ltac advance RS HSo Hfo HSn Hfn H2 H8 :=
    let Hfr := fresh "Hfr" in
    log_frame RS Hfr H2 H8;
    assert (HSn : SAVED _) by (eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HSo | exact Hfr | solve_apart | lia]);
    assert (Hfn : frame_mod mem _ BIG)
      by (eapply frame_mod_trans_same; [exact Hfo|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered);
    clear Hfr HSo Hfo.

  (* [comment removed for export] *)
  Ltac pin_bytes HR r v ids Hat Epsz Etc :=
    pin_reg HR r v by
      (rewrite (HR r);
       lazymatch goal with |- edenot ?E1 ?e = _ =>
         apply bv_eq; rewrite (beval_bytes E1 nu nu_range atoms e ids Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
         cbn [edenot ev vals_ev]; ev_simpl E1; rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ];
         rewrite ?Epsz, ?Etc; lia
       end).

  Ltac exit0_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' 0);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | intros; exfalso; lia ]
    end.

  Section Hdr2.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis H12 : (bv_unsigned (getr R 12) = psz)%Z.
    Hypothesis H6 : (bv_unsigned (getr R 6) = lepcs)%Z.
    Hypothesis H13 : getr R 13 = Z_to_bv 64 65280.
    Hypothesis Hlen : (132 <= len)%Z.
    (* [comment removed for export] *)
    Hypothesis M16 : cell64 SEGS M (bv_unsigned sp - 304) (Z_to_bv 64 2).
    Hypothesis M0 : cell64 SEGS M (bv_unsigned P) data.
    Hypothesis M8 : cell32 SEGS M (bv_unsigned P + 8) psz.
    Hypothesis Mz : zero M (bv_unsigned P + 16) 960.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
                        ++ [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len])) (blobs_ev [bs]).

    Definition kn_h2 : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KRange (EVar 20) 1 (2^47);
       KRange (EVar 64) 0 (2^32 - 1);
       KRange (EVar 65) 0 (2^32 - 1);
       KRange (EVar 66) 0 (2^32 - 1);
       KRange (EVar 67) 0 (2^32 - 1);
       KRange (EVar 68) 132 (2^26);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 20) 0) 132;
       KDisj (SA (EVar 8) 0) 976 (SA (EVar 20) 0) 132;
       KZero (SA (EVar 8) 16) (ELit 960);
       KWord (SA (EVar 2) 16) 8 (ELit 2);
       KWord (SA (EVar 8) 0) 8 (EVar 20);
       KWord (SA (EVar 8) 8) 4 (EVar 64);
       KBlobD (SA (EVar 20) 0) (EVar 68) 0].

    Lemma kn_h2_ok : know_ok SEGS E M kn_h2.
    Proof.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
      pose proof D as (D1 & D2 & D3 & D4 & D5).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (_ & _ & _ & _ & D5').
      pose proof (be32_range bs 0). pose proof (be32_range bs 128).
      pose proof (bs_byte_range bs 20). pose proof (bs_byte_range bs 21). pose proof (bs_byte_range bs 22).
      pose proof (bs_byte_range bs 23). pose proof (bs_byte_range bs 128). pose proof (bs_byte_range bs 129). pose proof (bs_byte_range bs 130).
      pose proof (bs_byte_range bs 131).
      unfold kn_h2, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply krange_intro; cbn. rewrite H20. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H20. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H8, H20. lia.
      - apply (kzero_intro SEGS E M (EVar 8) P 16 (ELit 960) 960);
          [ cbn [edenot]; ev_simpl E; exact H8 | reflexivity | lia | lia | lia
          | intros i Hi; apply Mz; exact Hi ].
      - eapply (kword_intro SEGS E M (EVar 2) (getr R 2) 16 8 (ELit 2) (Z_to_bv 64 2)); cbn; try lia; auto.
        replace (bv_unsigned (getr R 2) + 16)%Z with (bv_unsigned sp - 304)%Z by lia. exact M16.
      - eapply (kword_intro SEGS E M (EVar 8) P 0 8 (EVar 20) data); cbn; try lia; auto.
        rewrite Z.add_0_r. exact M0.
      - destruct M8 as [_ M8']. eapply (kword_intro SEGS E M (EVar 8) P 8 4 (EVar 64) (Z_to_bv 64 psz)); cbn; try lia; auto.
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. ev_simpl E.
        rewrite H20, u_small by lia. split; [lia|]. split; [exact D2|]. intros i Hi. rewrite Z.add_0_r. apply D5'. exact Hi.
    Qed.

    Lemma hdr2_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13c2c) M rom) Q.
    Proof.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
      pose proof (be32_range bs 0) as Rpsz. pose proof (be32_range bs 128) as Rtc.
      assert (Epsz : be32 bs 0 = (bs_byte bs 0 * 16777216 + bs_byte bs 1 * 65536 + bs_byte bs 2 * 256 + bs_byte bs 3)%Z) by reflexivity.
      assert (Etc : be32 bs 128 = (bs_byte bs 128 * 16777216 + bs_byte bs 129 * 65536 + bs_byte bs 130 * 256 + bs_byte bs 131)%Z) by reflexivity.
      pose proof (bs_byte_range bs 20) as B20. pose proof (bs_byte_range bs 21) as B21. pose proof (bs_byte_range bs 22) as B22. pose proof (bs_byte_range bs 23) as B23.
      pose proof (bs_byte_range bs 128) as B128. pose proof (bs_byte_range bs 129) as B129. pose proof (bs_byte_range bs 130) as B130. pose proof (bs_byte_range bs 131) as B131.
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_h2_ok as HK.
      pose proof (atoms_ok_at FPI R [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len] Hlen) as Hat.
      change (atoms_ok E nu atoms) in Hat.
      (* [comment removed for export] *)
      clear A3 A5 A6 Qal Q0 Q8 Pal Sal RO D5 Hra Hret S2 S3 S4 W1 W2 W4 M16 M0 M8 Mz.
      pin_reg HR (12%bv:reg) (EVar 64) by (rewrite (HR (12%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 12)), H12; reflexivity).
      pin_reg HR (6%bv:reg) (EVar 66) by (rewrite (HR (6%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E;
         rewrite <- (Z_to_bv_bv_unsigned 64 (getr R 6)), H6; reflexivity).
      pin_reg HR (13%bv:reg) (ELit 65280) by (rewrite (HR (13%bv:reg)); cbn [edenot sr_get sr_vars nth map seq Nat.add]; ev_simpl E; exact H13).
      (* [comment removed for export] *)
      run_fp 10%nat [0x13c40%Z] noscr true hints keep_all.
      advance [(SA (EVar 2) 8, 8%Z); (SA (EVar 8) 16, 4%Z)] HS Hf HS5 Hf5 H2 H8.
      (* [comment removed for export] *)
      clear A1 A2.
      run_fp 60%nat [0x13cdc%Z] noscr false.
      pin_bytes HR (14%bv:reg) (EVar 67) [128; 129; 130; 131]%nat Hat Epsz Etc.
      run_fp 10%nat (@nil Z) noscr true.
      advance [(SA (EVar 8) 20, 4%Z)] HS5 Hf5 HS6 Hf6 H2 H8.
      (* [comment removed for export] *)
      branch_case as Hsig.
      { fail_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6. }
      run_fp 20%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hver.
      { exit0_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6. }
      run_fp 10%nat (@nil Z) noscr false.
      (* [comment removed for export] *)
      branch_case as Hlp.
      { exit0_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6. }
      br_simpl_in E Hlp. rewrite H19, !u_small in Hlp by lia. rewrite ?Z.mod_small in Hlp by lia. apply Z.ltb_ge in Hlp.
      run_fp 1%nat [0x13d24%Z] noscr false.
      destruct (Z_lt_le_dec (bs_byte bs 128) 128) as [Hb|Hb].
      - (* [comment removed for export] *)
        assert (Hb7 : Z.testbit (nu 128%nat) 7 = false).
        { cbv [nu Z.of_nat Pos.of_succ_nat Pos.succ]. apply tb_small_high. cbn [Z.pow Z.pow_pos Pos.iter Z.mul]. lia. }
        lazymatch type of HR with regs_ok ?E1 ?sr _ =>
          let e13 := eval vm_compute in (sr_get sr (13%bv:reg)) in
          assert (E13 : edenot E1 e13 = Z_to_bv 64 tc)
            by (apply bv_eq; rewrite (beval_bytes_sx E1 nu nu_range atoms e13 [131; 130; 129; 128]%nat 128%nat Hat ltac:(cbn; lia) Hb7 ltac:(vm_compute; reflexivity));
                rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Etc; lia)
        end.
        pin_reg HR (13%bv:reg) (EVar 65) by
          (rewrite (HR (13%bv:reg));
           lazymatch goal with |- edenot ?E1 ?x = _ => let x' := eval vm_compute in x in change (edenot E1 x) with (edenot E1 x') end;
           rewrite E13; cbn [edenot]; ev_simpl E; reflexivity).
        pin_reg HR (16%bv:reg) (EMd M_MUL (ELit 4294967296) (EVar 65)) by
          (rewrite (HR (16%bv:reg));
           lazymatch goal with |- edenot ?E1 ?x = _ => let x' := eval vm_compute in x in change (edenot E1 x) with (edenot E1 x') end;
           lazymatch goal with |- edenot ?E1 (EMd M_MUL ?c ?a) = _ =>
             change (edenot E1 (EMd M_MUL c a)) with (mul_div M_MUL (edenot E1 c) (edenot E1 a)); rewrite E13;
             cbn [edenot]; ev_simpl E1; reflexivity
           end).
        run_fp 10%nat [0x13d38%Z] noscr false.
        (* [comment removed for export] *)
        branch_case as Htab.
        { exit0_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6. }
        br_simpl_in E Htab.
        rewrite alu_add, m_mul in Htab. unfold v_add, v_mul in Htab.
        rewrite !Z_to_bv_unsigned, !bv_wrap64_mod in Htab.
        rewrite (Z.mod_small psz), (Z.mod_small 12), (Z.mod_small tc), (Z.mod_small 132) in Htab by lia.
        rewrite (Z.mod_small (12 * tc)) in Htab by lia. rewrite Z.mod_small in Htab by lia. apply Z.ltb_ge in Htab.
        (* [comment removed for export] *)
        kread_fact HK (EVar 2) 16%Z 8%nat K1. kread_fact HK (EVar 2) 8%Z 8%nat K2.
        kread_fact HK (EVar 8) 0%Z 8%nat K3. kread_fact HK (EVar 8) 8%Z 4%nat K4. kread_fact HK (EVar 8) 20%Z 4%nat K5.
        rewrite H8 in K3, K4, K5. unfold v_addi in K1, K2, K3, K4, K5.
        rewrite H20 in K3.
        pose proof E13 as E13'. cbn [edenot] in E13'. ev_simpl_in E E13'. rewrite E13' in K5. clear E13'.
        lazymatch type of HK with know_ok _ ?E1 ?Mx ?kn =>
          pose proof (kzero_lookup_sound SEGS E1 Mx kn (EVar 8) 24 952 HK ltac:(vm_compute; reflexivity) ltac:(lia)) as Kz;
          cbn [edenot] in Kz; ev_simpl_in E1 Kz; rewrite H8 in Kz
        end.
        rewrite H2 in K1, K2. rewrite Z.add_0_r in K3. rewrite ext_val_4_small in K4 by lia. rewrite ext_val_4_small in K5 by lia.
        lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
          assert (HF3 : ZFACTS sp data P psz tc (Z_to_bv 64 lepcs) M2);
          [ split; [| exact Kz]; unfold ZH; cbv zeta;
            split; [replace (bv_unsigned sp - 304)%Z with (bv_unsigned sp - 320 + 16)%Z by lia; exact K1|];
            split; [replace (bv_unsigned sp - 312)%Z with (bv_unsigned sp - 320 + 8)%Z by lia; exact K2|];
            split; [exact K3|];
            split; [split; [lia | exact K4]|];
            split; [lia | exact K5]
          | apply (stageX_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a psz tc (Z_to_bv 64 lepcs)
                     ltac:(lia) ltac:(lia) M2 HS6 Hf6 HF3 I R2);
            [ common HR HFr H2 H3 H4 H8 HFK
            | unfold AREGS;
              split; [regv HR (12%bv:reg); apply u_small; lia|];
              split; [regv HR (13%bv:reg); apply u_small; lia|];
              split; [regv HR (14%bv:reg); rewrite u_small by lia; rewrite Etc; lia|];
              split; [regv HR (9%bv:reg); exact H9|];
              split; [regv HR (19%bv:reg); exact H19|];
              regv HR (20%bv:reg); exact H20 ] ]
        end.
      - (* [comment removed for export] *)
        assert (Htc31 : (2 ^ 31 <= tc)%Z) by (rewrite Etc; lia).
        lazymatch type of HR with regs_ok ?E1 ?sr _ =>
          let e13 := eval vm_compute in (sr_get sr (13%bv:reg)) in
          let etc := constr:(EAlu ALU_SRL (EMd M_MUL (ELit 4294967296) e13) (ELit 32)) in
          assert (Etcv : edenot E1 etc = Z_to_bv 64 tc)
            by (apply bv_eq; rewrite (beval_bytes E1 nu nu_range atoms etc [131; 130; 129; 128]%nat Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
                rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ]; rewrite Etc; lia);
          pin_reg HR (16%bv:reg) (EMd M_MUL (ELit 4294967296) (EVar 65)) by
            (rewrite (HR (16%bv:reg));
             lazymatch goal with |- edenot _ ?x = _ => let x' := eval vm_compute in x in change (edenot E1 x) with (edenot E1 x') end;
             rewrite (beval_same E1 nu nu_range atoms (EMd M_MUL (ELit 4294967296) e13) (EMd M_MUL (ELit 4294967296) etc) Hat
                        ltac:(vm_compute; reflexivity));
             change (edenot E1 (EMd M_MUL (ELit 4294967296) etc)) with (mul_div M_MUL (edenot E1 (ELit 4294967296)) (edenot E1 etc));
             rewrite Etcv; cbn [edenot]; ev_simpl E1; reflexivity)
        end.
        add_krange (EVar 65) (2^31)%Z (2^32 - 1)%Z by (rewrite u_small by lia; lia).
        run_fp 10%nat [0x13d38%Z; 0x13e20%Z] noscr false.
        exit0_with HR HFr H2 H3 H4 H8 HFK HS6 Hf6.
    Qed.
  End Hdr2.
End A1.
End LibParseA1S1.

Module LibParseA1aS1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1 LibParseA2S1 LibParseA1S1 OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswap OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibBswapSx.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).
(* [comment removed for export] *)
Local Ltac Lia.lia ::= first [ (intros; Zify.zify_pre_hook; zify_elim_let; zify_op; zify_iter_specs; Zify.zify_post_hook); xlia zchecker
                             | Zify.zify; xlia zchecker ].

#[local] Abbreviation SEGS := Plain.M.loaded_segments.
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section A1a.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  #[local] Abbreviation psz := (be32 bs 0).
  #[local] Abbreviation tc := (be32 bs 128).
  (* [comment removed for export] *)
  #[local] Abbreviation lepcs := (bs_byte bs 20 + bs_byte bs 21 * 256 + bs_byte bs 22 * 65536 + bs_byte bs 23 * 16777216)%Z.
  #[local] Abbreviation letc := (bs_byte bs 128 + bs_byte bs 129 * 256 + bs_byte bs 130 * 65536 + bs_byte bs 131 * 16777216)%Z.

  (* [comment removed for export] *)
  Definition nu (k : nat) : Z := bs_byte bs (Z.of_nat k).
  Definition atomu (d : nat) : expr * (bool * nat) := (EBlob false 0 (Z.of_nat d) 1, (false, d)).
  Definition atoms_s (d : nat) : expr * (bool * nat) := (EBlob true 0 (Z.of_nat d) 1, (true, d)).
  Definition atoms : list (expr * (bool * nat)) :=
    map atomu [0; 1; 2; 8; 9; 10; 11; 16; 17; 18; 19; 20; 21; 22; 23; 36; 37; 38; 68; 69; 70; 72; 73; 74; 76; 77; 78; 128; 129; 130; 131]%nat
    ++ map atoms_s [3; 39; 71; 75; 79]%nat.

  Lemma nu_range : forall k, (0 <= nu k < 256)%Z.
  Proof using . intros k. unfold nu. apply bs_byte_range. Qed.

  Lemma atoms_ok_at : forall (FPc : FPState) (Rc : bvmap 5 word) (ws : list word),
    (132 <= len)%Z ->
    atoms_ok (Env (vals_ev (junk_vals Rc ++ fjunk_vals (fp_regs (FPState:=FPc)) ++ ws)) (blobs_ev [bs])) nu atoms.
  Proof using HE rom.
    intros FPc Rc ws Hlen.
    destruct HE as (_ & _ & _ & (D1 & D2 & _) & _).
    unfold atoms, atoms_ok. cbn [map app].
    repeat (apply Forall_cons); [..|apply Forall_nil];
      unfold atomu, atoms_s, atom_ok; cbn [edenot eb blobs_ev nth Z.of_nat Pos.of_succ_nat Pos.succ];
      first [rewrite blob_val_u8 by lia | rewrite blob_val_s8 by lia]; unfold nu, bs_byte; cbn [Z.of_nat Pos.of_succ_nat Pos.succ Z.to_nat Pos.to_nat Pos.iter_op Nat.add]; reflexivity.
  Qed.

  (* [comment removed for export] *)
  Ltac log_frame RS Hfr H2 H8 :=
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr : frame_mod M1 M2 (regions_denot E2 RS))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
      unfold regions_denot in Hfr; cbn [map fst snd] in Hfr; unfold adenot in Hfr; cbn [a_base a_off edenot] in Hfr;
      ev_simpl_in E2 Hfr; rewrite ?H2, ?H8 in Hfr; unfold v_addi in Hfr; clear EQM HLF
    end.

  (* [comment removed for export] *)
  Ltac advance RS HSo Hfo HSn Hfn H2 H8 :=
    let Hfr := fresh "Hfr" in
    log_frame RS Hfr H2 H8;
    assert (HSn : SAVED _) by (eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HSo | exact Hfr | solve_apart | lia]);
    assert (Hfn : frame_mod mem _ BIG)
      by (eapply frame_mod_trans_same; [exact Hfo|]; eapply frame_mod_of_covered; [| exact Hfr]; unfold LibParseDefsS1.BIG; solve_covered);
    clear Hfr HSo Hfo.

  (* [comment removed for export] *)
  Ltac pin_bytes HR r v ids Hat Epsz Etc :=
    pin_reg HR r v by
      (rewrite (HR r);
       lazymatch goal with |- edenot ?E1 ?e = _ =>
         apply bv_eq; rewrite (beval_bytes E1 nu nu_range atoms e ids Hat ltac:(cbn; lia) ltac:(vm_compute; reflexivity));
         cbn [edenot ev vals_ev]; ev_simpl E1; rewrite u_small by lia; cbv [bytes_val nu Z.of_nat Pos.of_succ_nat Pos.succ];
         rewrite ?Epsz, ?Etc; lia
       end).

  Ltac exit0_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' 0);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | intros; exfalso; lia ]
    end.

  Section Hdr.
    Variables (FPI : FPState) (R : bvmap 5 word) (M : word -> option byte).
    Hypothesis HC : COMMON FPI R.
    Hypothesis HS : SAVED M.
    Hypothesis Hf : frame_mod mem M BIG.
    Hypothesis Hz : zero M (bv_unsigned P) 976.
    Hypothesis H9 : getr R 9 = prio.
    Hypothesis H18 : getr R 18 = Z_to_bv 64 2.
    Hypothesis H19 : getr R 19 = Z_to_bv 64 len.
    Hypothesis H20 : getr R 20 = data.
    Hypothesis Hlen : (132 <= len)%Z.

    Let E : env := Env (vals_ev (junk_vals R ++ fjunk_vals (fp_regs (FPState:=FPI))
                        ++ [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len])) (blobs_ev [bs]).

    Definition kn_h : list kentry :=
      [KRange (EVar 2) 336 (2^64 - 321);
       KRange (EVar 8) 1 (2^64 - 976);
       KRange (EVar 20) 1 (2^47);
       KRange (EVar 64) 0 (2^32 - 1);
       KRange (EVar 68) 132 (2^26);
       KWr (SA (EVar 2) (-336)) 656;
       KWr (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 8) 0) 976;
       KDisj (SA (EVar 2) (-336)) 656 (SA (EVar 20) 0) 132;
       KDisj (SA (EVar 8) 0) 976 (SA (EVar 20) 0) 132;
       KZero (SA (EVar 8) 0) (ELit 976);
       KBlobD (SA (EVar 20) 0) (EVar 68) 0].

    Lemma kn_h_ok : know_ok SEGS E M kn_h.
    Proof using H20 HC HE Hf Hlen Hz rom.
      destruct HC as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
      pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
      pose proof D as (D1 & D2 & D3 & D4 & D5).
      pose proof (penv_wS _ _ _ _ _ _ _ _ _ HE M Hf) as (S1 & S2 & S3 & S4).
      pose proof (penv_wP _ _ _ _ _ _ _ _ _ HE M Hf) as (W1 & W2 & W3 & W4).
      pose proof (penv_data regs mem rom ret sp data prio P len bs HE M Hf) as (_ & _ & _ & _ & D5').
      pose proof (be32_range bs 0).
      unfold kn_h, know_ok.
      repeat (apply Forall_cons); [..|apply Forall_nil].
      - apply krange_intro; cbn. rewrite H2. lia.
      - apply krange_intro; cbn. rewrite H8. lia.
      - apply krange_intro; cbn. rewrite H20. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply krange_intro; cbn. rewrite u_small by lia. lia.
      - apply (kwr_intro SEGS E M (EVar 2) (getr R 2) (-336) 656); cbn; try lia; try reflexivity.
        replace (bv_unsigned (getr R 2) + -336)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
      - apply (kwr_intro SEGS E M (EVar 8) P 0 976); cbn; try lia; [exact H8|].
        rewrite Z.add_0_r. exact W4.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H8. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H2, H20. lia.
      - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E. rewrite H8, H20. lia.
      - apply (kzero_intro SEGS E M (EVar 8) P 0 (ELit 976) 976);
          [ cbn [edenot]; ev_simpl E; exact H8 | reflexivity | lia | lia | lia
          | intros i Hi; rewrite Z.add_0_r; apply Hz; exact Hi ].
      - cbn [kentry_ok]. unfold flat, estart, elenZ. cbn [a_base a_off edenot]. ev_simpl E.
        rewrite H20, u_small by lia. split; [lia|]. split; [exact D2|]. intros i Hi. rewrite Z.add_0_r. apply D5'. exact Hi.
    Qed.

    Lemma hdr_run : runs_to SEGS (mkst (FP:=FPI) R (Z_to_bv 64 0x13b5c) M rom) Q.
    Proof using H18 H19 H20 H9 HC HE HS Ha2b Hb2a Hf Hgettag Hlen Hrc Hxyz Hz.
      pose proof HC as HC'. destruct HC' as (H2 & H3 & H4 & H8 & HFK).
      pose proof HE as HE'.
      destruct HE' as (_ & _ & _ & D & _ & _ & _ & _ & _ & WP & _ & P0 & _ & WS & _ & A1 & A2 & _ & A4 & _ & _).
      pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
      pose proof D as (D1 & D2 & D3 & D4 & _). pose proof WS as (S1 & _ & _ & _). pose proof WP as (_ & _ & W3 & _).
      clear D WS WP.
      pose proof (be32_range bs 0) as Rpsz. pose proof (be32_range bs 128) as Rtc.
      assert (Epsz : be32 bs 0 = (bs_byte bs 0 * 16777216 + bs_byte bs 1 * 65536 + bs_byte bs 2 * 256 + bs_byte bs 3)%Z) by reflexivity.
      assert (Etc : be32 bs 128 = (bs_byte bs 128 * 16777216 + bs_byte bs 129 * 65536 + bs_byte bs 130 * 256 + bs_byte bs 131)%Z) by reflexivity.
      pose proof (bs_byte_range bs 0) as B0. pose proof (bs_byte_range bs 1) as B1. pose proof (bs_byte_range bs 2) as B2. pose proof (bs_byte_range bs 3) as B3.
      pose proof (bs_byte_range bs 20) as B20. pose proof (bs_byte_range bs 21) as B21. pose proof (bs_byte_range bs 22) as B22. pose proof (bs_byte_range bs 23) as B23.
      assert (HR : regs_ok E (sr_vars 0) R) by exact (regs_ok_vars [] R _ (blobs_ev [bs])).
      assert (HFr : fregs_ok E (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals R) fp_regs _ (blobs_ev [bs])).
      pose proof kn_h_ok as HK.
      pose proof (atoms_ok_at FPI R [Z_to_bv 64 psz; Z_to_bv 64 tc; Z_to_bv 64 lepcs; Z_to_bv 64 letc; Z_to_bv 64 len] Hlen) as Hat.
      change (atoms_ok E nu atoms) in Hat.
      clear Hz.
      (* [comment removed for export] *)
      run_fp 40%nat [0x13b98%Z] noscr true hints keep_all.
      advance [(SA (EVar 2) 16, 8%Z); (SA (EVar 8) 0, 8%Z)] HS Hf HS3 Hf3 H2 H8.
      pin_bytes HR (12%bv:reg) (EVar 64) [3; 2; 1; 0]%nat Hat Epsz Etc.
      (* [comment removed for export] *)
      run_fp 60%nat [0x13c2c%Z] noscr true hints keep_all.
      advance [(SA (EVar 8) 8, 8%Z)] HS3 Hf3 HS4 Hf4 H2 H8.
      pin_bytes HR (6%bv:reg) (EVar 66) [20; 21; 22; 23]%nat Hat Epsz Etc.
      (* [comment removed for export] *)
      kread_fact HK (EVar 2) 16%Z 8%nat K1. kread_fact HK (EVar 8) 0%Z 8%nat K3. kread_fact HK (EVar 8) 8%Z 4%nat K4.
      rewrite H8 in K3, K4. unfold v_addi in K1, K3, K4. rewrite H2, H18 in K1. rewrite Z.add_0_r, H20 in K3.
      rewrite ext_val_4_small in K4 by lia.
      lazymatch type of HK with know_ok _ ?E1 ?Mx ?kn =>
        pose proof (kzero_lookup_sound SEGS E1 Mx kn (EVar 8) 16 960 HK ltac:(vm_compute; reflexivity) ltac:(lia)) as Kz;
        cbn [edenot] in Kz; ev_simpl_in E1 Kz; rewrite H8 in Kz
      end.
      lazymatch goal with |- runs_to _ (@mkst ?I ?R2 _ ?M2 _) _ =>
        apply (hdr2_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a I R2 M2)
      end.
      - common HR HFr H2 H3 H4 H8 HFK.
      - exact HS4.
      - exact Hf4.
      - regv HR (9%bv:reg). exact H9.
      - regv HR (19%bv:reg). exact H19.
      - regv HR (20%bv:reg). exact H20.
      - regv HR (12%bv:reg). apply u_small. lia.
      - regv HR (6%bv:reg). apply u_small. lia.
      - regv HR (13%bv:reg). reflexivity.
      - exact Hlen.
      - replace (bv_unsigned sp - 304)%Z with (bv_unsigned sp - 320 + 16)%Z by lia. exact K1.
      - exact K3.
      - split; [lia | exact K4].
      - exact Kz.
    Qed.
  End Hdr.
End A1a.
End LibParseA1aS1.

Module LibParseA0S1.
(* [comment removed for export] *)
(* [comment removed for export] *)
Import Stdlib.ZArith.ZArith Stdlib.NArith.NArith Stdlib.Lists.List Stdlib.micromega.Lia Stdlib.Bool.Bool.
Import LinuxProcessSemantics.LinuxProcessSem.BvBase LinuxProcessSemantics.LinuxProcessSem.RiscvSemantics LinuxProcessSemantics.LinuxProcessSem.MemImageType LinuxProcessSemantics.LinuxProcessSem.StackLayout LinuxProcessSemantics.LinuxProcessSem.State LinuxProcessSemantics.LinuxProcessSem.Run.
Import LinuxProcessSemantics.Riscv.Prelude LinuxProcessSemantics.Riscv.Instr LinuxProcessSemantics.Riscv.Decode LinuxProcessSemantics.Riscv.DecodeC LinuxProcessSemantics.Riscv.Sem LinuxProcessSemantics.Riscv.Fpu.
Import OSSVerify.skcms.iccprofile_info.images.Plain.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.CatSim OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SeqExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.StoreOk OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Hoare OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.Frame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.PropExecFP.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymExecFPSound OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymRunFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymCallFP OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibDefs OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFrame OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsSpec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP1Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibWP2Spec OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibTagsCall OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibFPLib OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.LibParseLib LibParseDefsS1 LibParseFS1 LibParseES1 LibParseDS1 LibParseC3S1 LibParseC2S1 LibParseC2aS1 LibParseA2S1 LibParseA1S1 LibParseA1aS1.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Atf.SymDriveLB.
Import Stdlib.micromega.Zify.
Import OSSVerify.Proofs.skcms.iccprofile_info.lib.Info.SymDriveLZ.
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
#[local] Abbreviation W := tags_src1.
#[local] Abbreviation W1 := wp1_src1.
#[local] Abbreviation W2 := wp2_src1.

Section A0.
  Variables (FP0 : FPState) (regs : bvmap 5 word) (mem rom : word -> option byte).
  Variables (ret sp data prio P : word) (len : Z) (bs : list byte).
  Hypothesis HE : PENV regs mem ret sp data prio P len bs.
  Hypothesis Hmemset : memset976_contract SEGS W1.
  Hypothesis Hgettag : gettag_contract SEGS W.
  Hypothesis Hrc : read_curve_contract SEGS W1.
  Hypothesis Hxyz : xyzd50_contract SEGS W.
  Hypothesis Ha2b : read_a2b_contract SEGS W2.
  Hypothesis Hb2a : read_b2a_contract SEGS W2.

  #[local] Notation Q := (Q FP0 regs mem rom ret sp data P len bs).
  #[local] Notation BIG := (BIG sp P).
  #[local] Notation COMMON := (COMMON FP0 regs sp P).
  #[local] Notation SAVED := (SAVED FP0 regs sp).

  Ltac exit_with v HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (exit_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M' v);
      [ common HR HF H2 H3 H4 H8 HFK
      | regv HR (15%bv:reg); reflexivity
      | lia | exact HS | exact Hf | ]
    end.
  Ltac fail_with HR HF H2 H3 H4 H8 HFK HS Hf :=
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
      [ common HR HF H2 H3 H4 H8 HFK | exact HS | exact Hf ]
    end.

  Hypotheses (R10 : getr regs 10 = data) (R11 : getr regs 11 = Z_to_bv 64 len) (R12 : getr regs 12 = prio)
             (R13 : getr regs 13 = Z_to_bv 64 2) (R14 : getr regs 14 = P).

  Let E0 : env := Env (vals_ev (junk_vals regs ++ fjunk_vals (fp_regs (FPState:=FP0)) ++ [Z_to_bv 64 len])) (blobs_ev [bs]).

  Definition kn_A : list kentry :=
    [KRange (EVar 2) 656 (2^64 - 1);
     KRange (EVar 14) 1 (2^64 - 976);
     KRange (EVar 10) 1 (2^47);
     KRange (EVar 11) 0 (2^26);
     KAlign (EVar 2) 16;
     KAlign (EVar 14) 8;
     KWr (SA (EVar 2) (-656)) 656;
     KWr (SA (EVar 14) 0) 976;
     KDisj (SA (EVar 2) (-656)) 656 (SA (EVar 14) 0) 976].

  Lemma kn_A_ok : know_ok SEGS E0 mem kn_A.
  Proof.
    pose proof HE as HE'.
    destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp). pose proof (u64_range P). pose proof (u64_range data).
    pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
    unfold kn_A, know_ok.
    repeat (apply Forall_cons); [..|apply Forall_nil].
    - apply krange_intro; cbn. rewrite Hsp. lia.
    - apply krange_intro; cbn. rewrite R14. lia.
    - apply krange_intro; cbn. rewrite R10. lia.
    - apply krange_intro; cbn. rewrite R11, u_small by lia. lia.
    - apply kalign_intro; [lia|]. cbn. rewrite Hsp. exact Sal.
    - apply kalign_intro; [lia|]. cbn. rewrite R14. exact Pal.
    - apply (kwr_intro SEGS E0 mem (EVar 2) sp (-656) 656); cbn; try lia; [exact Hsp|].
      replace (bv_unsigned sp + -656)%Z with (bv_unsigned sp - 656)%Z by lia. exact S4.
    - apply (kwr_intro SEGS E0 mem (EVar 14) P 0 976); cbn; try lia; [exact R14|].
      rewrite Z.add_0_r. exact W4.
    - cbn [kentry_ok]. unfold estart. cbn [a_base a_off edenot]. ev_simpl E0. rewrite Hsp, R14. lia.
  Qed.

  (* [comment removed for export] *)
  Ltac commonA HR HF Hsp R14 HFK0 :=
    split; [regv_lin HR (2%bv:reg); rewrite Hsp, u_small by lia; lia|];
    split; [regv HR (3%bv:reg); reflexivity|];
    split; [regv HR (4%bv:reg); reflexivity|];
    split; [regv HR (8%bv:reg); exact R14|];
    frk HF HFK0.

  Lemma blockA_run : runs_to SEGS (mkst (FP:=FP0) regs (Z_to_bv 64 0x13ae8) mem rom) Q.
  Proof.
    pose proof HE as HE'.
    destruct HE' as (Hra & Hret & Hsp & D & _ & _ & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO & A1 & A2 & A3 & A4 & A5 & A6).
    pose proof (u64_range sp) as Rsp. pose proof (u64_range P) as RP. pose proof (u64_range data) as Rd.
    pose proof D as (D1 & D2 & D3 & D4 & D5). pose proof WS as (S1 & S2 & S3 & S4). pose proof WP as (W1 & W2 & W3 & W4).
    assert (HR : regs_ok E0 (sr_vars 0) regs) by exact (regs_ok_vars [] regs _ (blobs_ev [bs])).
    assert (HFr : fregs_ok E0 (sfr_vars 32) fp_regs) by exact (fregs_ok_vars (junk_vals regs) fp_regs _ (blobs_ev [bs])).
    assert (HFK0 : forall r : reg, In r [19; 20; 21; 22; 23; 24; 25; 26; 27]%bv ->
              reg_get (fp_regs (FPState:=FP0)) r = reg_get (fp_regs (FPState:=FP0)) r) by (intros; reflexivity).
    pose proof kn_A_ok as HK.
    (* [comment removed for export] *)
    run_fp 40%nat [0x1dfe4%Z] noscr true.
    (* [comment removed for export] *)
    kread_fact HK (EVar 2) (-8)%Z 8%nat K1. kread_fact HK (EVar 2) (-16)%Z 8%nat K2.
    kread_fact HK (EVar 2) (-24)%Z 8%nat K3. kread_fact HK (EVar 2) (-32)%Z 8%nat K4.
    kread_fact HK (EVar 2) (-40)%Z 8%nat K5. kread_fact HK (EVar 2) (-48)%Z 8%nat K6.
    kread_fact HK (EVar 2) (-56)%Z 8%nat K7. kread_fact HK (EVar 2) (-64)%Z 8%nat K8.
    kread_fact HK (EVar 2) (-72)%Z 8%nat K9. kread_fact HK (EVar 2) (-80)%Z 8%nat K10.
    kread_fact HK (EVar 2) (-88)%Z 8%nat K11. kread_fact HK (EVar 2) (-96)%Z 8%nat K12.
    kread_fact HK (EVar 2) (-104)%Z 8%nat K13. kread_fact HK (EVar 2) (-112)%Z 8%nat K14.
    kread_fact HK (EVar 2) (-120)%Z 8%nat K15. kread_fact HK (EVar 2) (-128)%Z 8%nat K16.
    rewrite Hsp in K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16.
    unfold v_addi in K1, K2, K3, K4, K5, K6, K7, K8, K9, K10, K11, K12, K13, K14, K15, K16.
    lazymatch goal with |- runs_to _ (@mkst _ _ _ ?M1 _) _ =>
      assert (HS1 : SAVED M1) by
        (unfold LibParseDefsS1.SAVED; cbv zeta;
         repeat match goal with |- _ /\ _ => split end;
         (lazymatch goal with |- cell64 _ _ (?a - ?k)%Z _ => replace (a - k)%Z with (a + - k)%Z by lia end; cbn [Z.opp]; assumption))
    end.
    clear K1 K2 K3 K4 K5 K6 K7 K8 K9 K10 K11 K12 K13 K14 K15 K16.
    lazymatch goal with
    | EQM : ?M2 = mem_denot ?E2 ?M1 ?log, HLF : log_flat _ _ |- _ =>
      assert (Hfr1 : frame_mod M1 M2 (regions_denot E2 [(SA (EVar 2) (-128), 128%Z)]))
        by (rewrite EQM; apply (frame_mod_mem_denot E2 M1 log _ HLF); [flats_auto | vm_compute; reflexivity]);
      unfold regions_denot in Hfr1; cbn [map fst snd] in Hfr1; unfold adenot in Hfr1; cbn [a_base a_off edenot] in Hfr1;
      ev_simpl_in E2 Hfr1; rewrite Hsp in Hfr1; unfold v_addi in Hfr1; clear EQM HLF
    end.
    assert (Hf1 : frame_mod mem M BIG)
      by (eapply frame_mod_of_covered; [| exact Hfr1]; unfold LibParseDefsS1.BIG; solve_covered).
    clear Hfr1.
    (* [comment removed for export] *)
    lazymatch goal with
    | HR : regs_ok _ _ ?R1 |- runs_to _ (@mkst ?I ?R1 _ ?Mx ?ro) _ =>
      eapply rt_call;
      [ eapply (Hmemset P I R1 Mx ro (Z_to_bv 64 0x13b54));
        [ regv HR (1%bv:reg); reflexivity
        | apply ret_ok_even; rewrite u_small by lia; reflexivity
        | unfold memset_pre;
          split; [regv HR (10%bv:reg); exact R14|];
          split; [regv HR (11%bv:reg); reflexivity|];
          split; [regv HR (12%bv:reg); reflexivity|];
          split; [exact Pal|];
          split; [apply (penv_wP regs mem ret sp data prio P len bs HE); exact Hf1|];
          lia ]
      | cbv beta ]
    end.
    intros FQ1 rq1 mq1 (Hkeep & Hfkeep & Hfrm & Hzero & Ha0).
    unfold regs_kept in Hkeep. unfold fregs_kept in Hfkeep.
    after_call Hkeep Hfkeep FQ1. clear Hkeep Hfkeep.
    know_frame HK Hfrm [(SA (EVar 14) 0, 976%Z)]; [unfold v_addi; rewrite R14, Z.add_0_r, Z_to_bv_bv_unsigned; reflexivity|].
    assert (HS2 : SAVED mq1) by (eapply (SAVED_frame FP0 regs mem rom sp sp); [exact HS1 | exact Hfrm | solve_apart | lia]).
    assert (Hf2 : frame_mod mem mq1 BIG)
      by (eapply frame_mod_trans_same; [exact Hf1|]; eapply frame_mod_of_covered; [| exact Hfrm]; unfold LibParseDefsS1.BIG; solve_covered).
    assert (Hz : zero mq1 (bv_unsigned P) 976) by (intros i Hi; apply Hzero; exact Hi).
    clear HS1 Hf1 Hfrm Hzero.
    run_fp 10%nat (@nil Z) noscr false.
    (* [comment removed for export] *)
    branch_case as Hl132.
    { lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
        apply (fail_ok FP0 regs mem rom ret sp data prio P len bs HE I R' M');
        [ commonA HR HFr Hsp R14 HFK0 | exact HS2 | exact Hf2 ]
      end. }
    br_simpl_in E0 Hl132. rewrite R11, (u_small len) in Hl132 by lia. apply Z.ltb_ge in Hl132.
    lazymatch goal with |- runs_to _ (@mkst ?I ?R' _ ?M' _) _ =>
      apply (hdr_run FP0 regs mem rom ret sp data prio P len bs HE Hgettag Hrc Hxyz Ha2b Hb2a I R' M');
      [ commonA HR HFr Hsp R14 HFK0 | exact HS2 | exact Hf2 | exact Hz
      | regv HR (9%bv:reg); exact R12
      | regv HR (18%bv:reg); exact R13
      | regv HR (19%bv:reg); exact R11
      | regv HR (20%bv:reg); exact R10
      | exact Hl132 ]
    end.
  Qed.
End A0.
End LibParseA0S1.

(* [comment removed for export] *)
(* [comment removed for export] *)
From Stdlib Require Import ZArith NArith List Lia Bool.
From LinuxProcessSemantics.LinuxProcessSem Require Import
  BvBase RiscvSemantics MemImageType StackLayout State Run.
From LinuxProcessSemantics.Riscv Require Import Prelude Instr Decode DecodeC Sem Fpu.
From OSSVerify.skcms.iccprofile_info.images Require Import Plain.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import PropExec CatExec CatSim SeqExec StoreOk SymExec Hoare Frame PropExecFP.
From OSSVerify.Proofs.skcms.iccprofile_info.lib.Info Require Import SymExecFP SymExecFPSound SymRunFP SymDriveFP SymCallFP LibDefs LibFrame LibTagsSpec LibWP1Spec LibWP2Spec LibTagsLib LibTagsCall LibFPLib LibParseLib. Import LibParseDefsS1. Import LibParseA0S1.
Unset Lia Cache.
Import ListNotations.
Open Scope bv_scope.

#[local] Abbreviation SEGS := Plain.M.loaded_segments.

Theorem parse_S1_ok :
  memset976_contract SEGS wp1_src1 -> gettag_contract SEGS tags_src1 -> read_curve_contract SEGS wp1_src1 ->
  xyzd50_contract SEGS tags_src1 -> read_a2b_contract SEGS wp2_src1 -> read_b2a_contract SEGS wp2_src1 ->
  parse_contract SEGS tags_src1.
Proof.
  intros Hmemset Hgettag Hrc Hxyz Ha2b Hb2a data len bs sp prio P FPI regs mem rom ret Hra Hret PRE.
  destruct PRE as (Hsp & R10 & R11 & R12 & R13 & R14 & D & C0 & C4 & Qal & Q0 & Q8 & WP & Pal & P0 & Sal & WS & RO &
                   A1 & A2 & A3 & A4 & A5 & A6).
  cbn [t_parse_d t_ro_lo t_ro_hi tags_src1] in WS, RO, A1, A4, A5.
  assert (HE : PENV regs mem ret sp data prio P len bs).
  { unfold PENV. cbv zeta. repeat (split; [assumption|]). assumption. }
  destruct (blockA_run FPI regs mem rom ret sp data prio P len bs HE Hmemset Hgettag Hrc Hxyz Ha2b Hb2a R10 R11 R12 R13 R14)
    as (st' & Hms & (FPI' & regs' & mem' & -> & Hk1 & Hk2 & Hpost)).
  exists FPI', regs', mem'. split; [exact Hms|]. split; [exact Hk1|]. split; [exact Hk2|].
  unfold parse_post. cbn [t_parse_d tags_src1]. exact Hpost.
Qed.
